import { roundRatio } from './binary64.js'
import type { CircuitInput, ThieleSmallDriver } from './circuit.js'
import { distributedPort } from './ductBounds.js'
import { dyadicIntervals as math, outwardBinary64, type DyadicInterval as Box } from './dyadicInterval.js'
import type { DriverMeasurementCondition, EnclosureFitParameter, ImpedanceFitStatus, ImpedanceSample } from './impedance.js'
import { IntervalRangeError } from './interval.js'

type Bound = { lower: number; upper: number }

export interface ImpedanceFitCertificate {
  version: 1
  kind: 'driver' | 'enclosure'
  /** Canonical sorted-key JSON binding the fit inputs and options. */
  request: string
  status: ImpedanceFitStatus
  values: readonly number[]
  rmsRelativeErrorBound: Bound
  projectedGradientBound: Bound
  /** Number of squared singular values strictly above sensitivityFloor. */
  sensitivityRank: number
  /** Row-major, invertible lower-triangular preconditioner for full sensitivity rank. */
  preconditioner?: readonly number[]
  /** Nonzero direction with energy per squared norm at most sensitivityFloor. */
  weakDirection?: readonly number[]
  /** Threshold on the squared singular values of the normalized Jacobian. */
  sensitivityFloor: number
}

export type FitRange = { min: number; max: number }
type Dual = { val: Box; der: Box[] }
type Phasor = { re: Dual; im: Dual }
type Sweeps = { samples: readonly ImpedanceSample[]; at(frequency: number): Phasor }[]

const { exact, maximum, minus, one, pi, plus, quotient, root, square, times, zero } = math
const two = exact(2)
const neg = (a: Box) => minus(zero, a)
const absolute = (a: Box) => maximum([zero, a, neg(a)])
const midpoint = (a: Box) => roundRatio(a.lo + a.hi, 2n * one.lo)
const sum = (boxes: readonly Box[]) => boxes.reduce(plus, zero)
const dot = (a: readonly Box[], b: readonly Box[]) => sum(a.map((x, i) => times(x, b[i]!)))

/** Seed derivatives directly in normalized fit coordinates. */
function dualMath(values: readonly number[], bounds: readonly FitRange[]) {
  const derivatives = values.map(() => zero)
  const lift = (val: Box): Dual => ({ val, der: derivatives })
  const constant = (value: number) => lift(exact(value))
  const seed = (value: number, i: number): Dual => {
    const bound = bounds[i]!
    const der = derivatives.slice()
    der[i] = minus(exact(bound.max), exact(bound.min))
    return { val: exact(value), der }
  }
  const add = (a: Dual, b: Dual): Dual =>
    ({ val: plus(a.val, b.val), der: a.der.map((d, i) => plus(d, b.der[i]!)) })
  const sub = (a: Dual, b: Dual): Dual =>
    ({ val: minus(a.val, b.val), der: a.der.map((d, i) => minus(d, b.der[i]!)) })
  const mul = (a: Dual, b: Dual): Dual => ({
    val: times(a.val, b.val),
    der: a.der.map((d, i) => plus(times(d, b.val), times(a.val, b.der[i]!))),
  })
  const div = (a: Dual, b: Dual): Dual => {
    const val = quotient(a.val, b.val)
    return { val, der: a.der.map((d, i) => quotient(minus(d, times(val, b.der[i]!)), b.val)) }
  }
  const squared = (a: Dual): Dual =>
    ({ val: square(a.val), der: a.der.map((d) => times(times(two, a.val), d)) })
  const sqrt = (a: Dual): Dual => {
    const val = root(a.val)
    return { val, der: a.der.map((d) => quotient(d, times(two, val))) }
  }
  const real = (re: Dual): Phasor => ({ re, im: lift(zero) })
  const addComplex = (a: Phasor, b: Phasor): Phasor => ({ re: add(a.re, b.re), im: add(a.im, b.im) })
  const mulComplex = (a: Phasor, b: Phasor): Phasor => ({
    re: sub(mul(a.re, b.re), mul(a.im, b.im)), im: add(mul(a.re, b.im), mul(a.im, b.re)),
  })
  const norm = (a: Phasor) => add(squared(a.re), squared(a.im))
  const divComplex = (a: Phasor, b: Phasor): Phasor => {
    const numerator = mulComplex(a, { re: b.re, im: sub(lift(zero), b.im) })
    const denominator = norm(b)
    return { re: div(numerator.re, denominator), im: div(numerator.im, denominator) }
  }
  return { lift, constant, seed, add, sub, mul, div, squared, sqrt, real, addComplex,
    mulComplex, divComplex, norm, zero: lift(zero), one: lift(one), tau: lift(times(two, pi)) }
}

type DualMath = ReturnType<typeof dualMath>
type DualDriver = { [K in keyof ThieleSmallDriver]: Dual }

function motor(driver: DualDriver, rhoC2: Dual, math: DualMath) {
  const { div, mul, one, squared, tau } = math
  const omega = mul(tau, driver.fsHz)
  const area = squared(driver.sdM2)
  const cms = div(driver.vasM3, mul(rhoC2, area))
  const mass = div(one, mul(squared(omega), cms))
  const omegaMass = mul(omega, mass)
  return { area, omega, stiffness: div(one, cms), mass,
    resistance: div(omegaMass, driver.qms), bl2: div(mul(omegaMass, driver.reOhms), driver.qes) }
}

export function driverFitSweeps(initial: ThieleSmallDriver, medium: CircuitInput['medium'],
  freeAir: readonly ImpedanceSample[], perturbation: DriverMeasurementCondition, perturbed: readonly ImpedanceSample[],
  bounds: readonly FitRange[], values: readonly number[]): Sweeps {
  const math = dualMath(values, bounds)
  const { constant, seed, add, sub, mul, div, squared, real, addComplex, divComplex, one, tau } = math
  const driver: DualDriver = {
    fsHz: seed(values[0]!, 0), vasM3: seed(values[1]!, 1), qes: seed(values[2]!, 2),
    qms: seed(values[3]!, 3), reOhms: seed(values[4]!, 4), leHenries: seed(values[5]!, 5),
    sdM2: constant(initial.sdM2),
  }
  const rhoC2 = mul(constant(medium.densityKgM3), squared(constant(medium.soundSpeedMps)))
  const { stiffness, mass, resistance, bl2 } = motor(driver, rhoC2, math)
  const at = (condition: DriverMeasurementCondition) => {
    const testMass = condition.kind === 'added-mass' ? add(mass, constant(condition.massKg)) : mass
    const testStiffness = condition.kind === 'sealed-box'
      ? mul(stiffness, add(one, div(driver.vasM3, constant(condition.volumeM3)))) : stiffness
    return (frequency: number) => {
      const w = mul(tau, constant(frequency))
      return addComplex({ re: driver.reOhms, im: mul(w, driver.leHenries) },
        divComplex(real(bl2), { re: resistance, im: sub(mul(w, testMass), div(testStiffness, w)) }))
    }
  }
  return [{ samples: freeAir, at: at({ kind: 'free-air' }) }, { samples: perturbed, at: at(perturbation) }]
}

export function enclosureFitSweeps(input: CircuitInput, samples: readonly ImpedanceSample[],
  keys: readonly EnclosureFitParameter[], bounds: readonly FitRange[], values: readonly number[]): Sweeps {
  const math = dualMath(values, bounds)
  const { constant, seed, lift, add, sub, mul, div, squared, sqrt, real, addComplex, mulComplex,
    divComplex, one, zero, tau } = math
  const parameter = (key: EnclosureFitParameter, value: number) => {
    const i = keys.indexOf(key)
    return i < 0 ? constant(value) : seed(values[i]!, i)
  }
  const { medium, port, passiveRadiator: radiator } = input
  const driver: DualDriver = {
    fsHz: constant(input.driver.fsHz), vasM3: constant(input.driver.vasM3), qes: constant(input.driver.qes),
    qms: constant(input.driver.qms), reOhms: constant(input.driver.reOhms),
    leHenries: constant(input.driver.leHenries), sdM2: constant(input.driver.sdM2),
  }
  const count = constant(input.quantity ?? 1)
  const wiring = div(squared(constant(input.seriesDrivers ?? 1)), count)
  const rho = constant(medium.densityKgM3)
  const rhoC2 = mul(rho, squared(constant(medium.soundSpeedMps)))
  const volume = parameter('volumeM3', input.volumeM3)
  const cab = div(volume, rhoC2)
  const { area, omega, stiffness, mass, resistance, bl2 } = motor(driver, rhoC2, math)
  const coupling = mul(count, area)
  // A fitted parameter can change the port resistance. Geometry and the
  // transfer matrix are constant with respect to every supported coordinate.
  const duct = port?.ductPath && distributedPort(port.ductPath, medium.soundSpeedMps, medium.densityKgM3)
  const portMass = duct ? lift(duct.mass) : port
    ? div(mul(rho, parameter('effectiveLengthM', port.effectiveLengthM!)), constant(port.areaM2!)) : zero
  const radiatorMass = radiator ? parameter('radiatorMassKg', radiator.movingMassKg) : zero
  const radiatorArea = radiator ? mul(constant(radiator.quantity ?? 1), squared(constant(radiator.sdM2))) : zero
  const characteristic = port ? sqrt(div(portMass, cab))
    : radiator ? sqrt(div(radiatorMass, mul(radiatorArea, cab)))
    : div(one, mul(mul(omega, cab), sqrt(add(one, div(mul(driver.vasM3, count), volume)))))
  const loss = (key: 'leakageQuality' | 'absorptionQuality', quality: number) =>
    quality === Infinity ? zero : div(one, mul(parameter(key, quality), characteristic))
  const conductance = add(loss('leakageQuality', input.leakageQuality), loss('absorptionQuality', input.absorptionQuality))
  const portResistance = port && port.quality !== Infinity
    ? div(div(portMass, sqrt(mul(portMass, cab))), parameter('portQuality', port.quality)) : zero

  return [{ samples, at(frequency) {
    const w = mul(tau, constant(frequency))
    const base = { re: conductance, im: mul(w, cab) }
    let branch = real(one)
    let admittance = base
    // Clear the branch denominator, including the duct transfer denominator
    // at a pole, before taking the electrical impedance ratio.
    if (port) {
      const response = duct?.response(exact(frequency))
      const throat = response ? lift(response.throatFlow) : one
      branch = { re: mul(portResistance, throat), im: response ? lift(response.reactance) : mul(w, portMass) }
      admittance = addComplex(mulComplex(base, branch), real(throat))
    } else if (radiator) {
      branch = { re: constant(radiator.mechanicalResistanceNsPerM),
        im: sub(mul(w, radiatorMass), div(one, mul(w, constant(radiator.complianceMPerN)))) }
      admittance = addComplex(mulComplex(base, branch), real(radiatorArea))
    }
    const mechanical = addComplex(mulComplex({ re: resistance, im: sub(mul(w, mass), div(stiffness, w)) },
      admittance), mulComplex(real(coupling), branch))
    const electrical = { re: driver.reOhms, im: mul(w, driver.leHenries) }
    return mulComplex(real(wiring), addComplex(electrical, divComplex(mulComplex(real(bl2), admittance), mechanical)))
  } }]
}

export function impedanceFitRequest(...inputs: readonly unknown[]): string {
  return JSON.stringify(inputs, (_, value: unknown) => {
    if (value === Infinity) return '+Infinity'
    if (typeof value === 'object' && value !== null && !Array.isArray(value)) {
      const record = value as Record<string, unknown>
      return Object.fromEntries(Object.keys(record).sort().map((key) => [key, record[key]]))
    }
    return value
  })
}

export function evaluateImpedanceFit(sweeps: Sweeps, bounds: readonly FitRange[], values: readonly number[]) {
  const math = dualMath(values, bounds)
  const { constant, div, sqrt, norm, sub } = math
  const residuals: Dual[] = []
  for (const { samples, at } of sweeps) {
    for (const { frequency, impedanceOhms } of samples) {
      const z = at(frequency)
      if (typeof impedanceOhms === 'number') {
        const magnitude = constant(impedanceOhms)
        residuals.push(div(sub(sqrt(norm(z)), magnitude), magnitude))
      } else {
        const { re, im } = impedanceOhms
        const scale = math.lift(root(plus(square(exact(re)), square(exact(im)))))
        residuals.push(div(sub(z.re, constant(re)), scale), div(sub(z.im, constant(im)), scale))
      }
    }
  }
  const errors = residuals.map(({ val }) => val)
  // Complex measurements contribute separate real and imaginary rows, as
  // in the search's objective.
  const rows = exact(residuals.length)
  const rms = root(quotient(sum(errors.map(square)), rows))
  const columns = values.map((_, i) => residuals.map(({ der }) => der[i]!))
  const projected = columns.map((column, i) => {
    const gradient = quotient(dot(column, errors), rows)
    if (values[i] === bounds[i]!.min) return maximum([zero, neg(gradient)])
    if (values[i] === bounds[i]!.max) return maximum([zero, gradient])
    return absolute(gradient)
  })
  const gram = columns.map((a, row) => columns.map((b, col) => row === col ? sum(a.map(square)) : dot(a, b)))
  const floor = Math.max(residuals.length * 1e-14, midpoint(maximum(gram.map((row, i) => row[i]!))) * 1e-12)
  const shifted = gram.map((row, i) => row.map((entry, j) => i === j ? minus(entry, exact(floor)) : entry))
  return { rms, projected: maximum(projected), columns, floor, shifted,
    active: values.some((value, i) => value === bounds[i]!.min || value === bounds[i]!.max) }
}

type Diagnostics = ReturnType<typeof evaluateImpedanceFit>

/** Reverse LDL elimination. The sign of each enclosed pivot gives the
 * inertia of the shifted Gram matrix. Eliminating from the last row first
 * gives a lower-triangular change of basis with unit diagonal. */
function factor(matrix: Box[][]) {
  const n = matrix.length
  const schur = matrix.map((row) => row.slice())
  const change = matrix.map((row, i) => row.map((_, j): number => i === j ? 1 : 0))
  const negative: number[] = []
  for (let k = n - 1; k >= 0; k--) {
    const pivot = schur[k]![k]!
    if (pivot.hi < 0n) negative.push(k)
    else if (pivot.lo <= 0n) throw new IntervalRangeError()
    for (let i = 0; i < k; i++) {
      const multiplier = quotient(schur[k]![i]!, pivot)
      for (let j = 0; j <= i; j++) {
        const entry = minus(schur[i]![j]!, times(multiplier, schur[k]![j]!))
        schur[i]![j] = entry
        schur[j]![i] = entry
      }
      const weight = midpoint(multiplier)
      for (let row = k; row < n; row++) change[row]![i] = change[row]![i]! - weight * change[row]![k]!
    }
  }
  return { change, negative, rank: n - negative.length }
}

function weakWitness(columns: Box[][], direction: readonly number[], floor: number): boolean {
  const weights = direction.map(exact)
  const norm = sum(weights.map(square))
  if (norm.lo <= 0n) return false
  const energy = sum(columns[0]!.map((_, row) => square(dot(weights, columns.map((col) => col[row]!)))))
  return energy.hi <= times(norm, exact(floor)).lo
}

function fullWitness(matrix: Box[][], entries: readonly number[]): boolean {
  const n = matrix.length
  const columns = matrix.map((_, j) => matrix.map((_, i) => exact(entries[i * n + j]!)))
  const product = columns.map((column) => matrix.map((row) => dot(row, column)))
  const transformed = columns.map((column) => product.map((other) => dot(column, other)))
  // The symmetric congruence is positive definite if every Gershgorin
  // disc lies strictly above zero.
  return transformed.every((row, i) => row[i]!.lo > sum(row.map((entry, j) => i === j ? zero : absolute(entry))).hi)
}

export function classifyImpedanceFit(fullRank: boolean, residualTarget: boolean, stationary: boolean,
  active: boolean, stalled: boolean): ImpedanceFitStatus {
  if (!fullRank) return 'poorly-identified'
  if (residualTarget) return 'residual-target'
  if (stationary) return active ? 'bound-constrained' : 'stationary'
  return stalled ? 'stalled' : 'iteration-limit'
}

function statusAt(d: Diagnostics, rank: number, tolerance: number, stalled: boolean): ImpedanceFitStatus {
  const fullRank = rank === d.columns.length
  const target = exact(tolerance)
  const residualTarget = d.rms.hi <= target.lo
  const stationary = d.projected.hi <= target.lo
  // One decisive lower bound suffices for a stopped search. If both
  // metrics straddle the tolerance, the endpoint has no certified status.
  if (fullRank && !residualTarget && !stationary && d.rms.lo <= target.hi && d.projected.lo <= target.hi)
    throw new IntervalRangeError()
  return classifyImpedanceFit(fullRank, residualTarget, stationary, d.active, stalled)
}

function binaryBound(value: Box): Bound {
  const { lo, hi } = outwardBinary64(value)
  return { lower: Math.max(0, lo), upper: hi }
}

function encloses(bound: Bound, value: Box): boolean {
  return Number.isFinite(bound.lower) && Number.isFinite(bound.upper) && bound.lower >= 0 &&
    bound.lower <= bound.upper && exact(bound.lower).hi <= value.lo && exact(bound.upper).lo >= value.hi
}

function finiteArray(values: unknown, length: number): values is readonly number[] {
  return Array.isArray(values) && values.length === length && Array.from(values).every(Number.isFinite)
}

export function matchesImpedanceFit(certificate: Readonly<ImpedanceFitCertificate>, kind: ImpedanceFitCertificate['kind'],
  request: string, bounds: readonly FitRange[]): boolean {
  return certificate.version === 1 && certificate.kind === kind && certificate.request === request &&
    finiteArray(certificate.values, bounds.length) &&
    certificate.values.every((value, i) => value >= bounds[i]!.min && value <= bounds[i]!.max)
}

export function replayImpedanceFit(d: Diagnostics, certificate: Readonly<ImpedanceFitCertificate>, tolerance: number,
  stoppedEarly: () => boolean, knownRank?: number): boolean {
  const { sensitivityRank: rank, sensitivityFloor: floor, weakDirection, preconditioner } = certificate
  const n = d.columns.length
  if (floor !== d.floor || !encloses(certificate.rmsRelativeErrorBound, d.rms) ||
      !encloses(certificate.projectedGradientBound, d.projected)) return false
  if (certificate.status === 'poorly-identified') {
    if (preconditioner !== undefined || !finiteArray(weakDirection, n) || !weakWitness(d.columns, weakDirection, floor) ||
        rank >= n || rank !== (knownRank ?? factor(d.shifted).rank)) return false
  } else {
    if (weakDirection !== undefined || rank !== n || !finiteArray(preconditioner, n * n) ||
        !preconditioner.every((value, i) => {
          const row = Math.floor(i / n)
          const col = i % n
          return row === col ? value > 0 : row > col || value === 0
        }) || !fullWitness(d.shifted, preconditioner)) return false
  }
  const nonconverged = certificate.status === 'stalled' || certificate.status === 'iteration-limit'
  return certificate.status === statusAt(d, rank, tolerance, nonconverged && stoppedEarly())
}

export function certifyImpedanceFit(d: Diagnostics, kind: ImpedanceFitCertificate['kind'], request: string,
  values: readonly number[], tolerance: number, stalled: boolean, floatingRms: number) {
  const { change, negative, rank } = factor(d.shifted)
  const status = statusAt(d, rank, tolerance, stalled)
  const rmsBound = binaryBound(d.rms)
  // Preserve a zero residual for identical binary64 measurements when the
  // exact physical model also agrees within the caller's tolerance.
  const roundedMatch = floatingRms === 0 && d.rms.hi <= exact(tolerance).lo
  if (roundedMatch) rmsBound.lower = 0
  const certificate: ImpedanceFitCertificate = {
    version: 1, kind, request, status, values: [...values],
    rmsRelativeErrorBound: rmsBound, projectedGradientBound: binaryBound(d.projected),
    sensitivityFloor: d.floor, sensitivityRank: rank,
  }
  if (status === 'poorly-identified') {
    certificate.weakDirection = change.map((row) => row[negative[0]!]!)
  } else certificate.preconditioner = change.flat()
  if (!replayImpedanceFit(d, certificate, tolerance, () => stalled, rank)) throw new IntervalRangeError()
  return { certificate, status, rmsRelativeError: roundedMatch ? 0 : midpoint(d.rms),
    projectedGradient: midpoint(d.projected), sensitivityRank: rank }
}
