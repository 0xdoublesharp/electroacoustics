import { createCircuit, type CircuitInput, type ThieleSmallDriver } from './circuit.js'
import { add, c, div, magnitude, sub, type Complex } from './complex.js'
import { driverMotor } from './driverMotor.js'
import { certifyImpedanceFit, classifyImpedanceFit, driverFitSweeps, enclosureFitSweeps, evaluateImpedanceFit, impedanceFitRequest,
  matchesImpedanceFit, replayImpedanceFit, type FitRange, type ImpedanceFitCertificate } from './impedanceCert.js'
import { enclosedOr } from './interval.js'

export type { ImpedanceFitCertificate } from './impedanceCert.js'

type Medium = CircuitInput['medium']
export type DriverMeasurementCondition =
  | { kind: 'free-air' }
  | { kind: 'added-mass'; massKg: number }
  | { kind: 'sealed-box'; volumeM3: number }

export interface ImpedanceSample {
  frequency: number
  /** Magnitude in ohms, or complex impedance in the exp(jωt) convention. */
  impedanceOhms: number | Complex
}

export interface ImpedanceFitOptions {
  maxIterations?: number
  /** Relative RMS target and projected-gradient tolerance. */
  tolerance?: number
  /** Normalized step size that ends the search. Defaults to tolerance. */
  normalizedStepTolerance?: number
}

export type ImpedanceFitStatus = 'residual-target' | 'stationary' | 'bound-constrained' |
  'poorly-identified' | 'stalled' | 'iteration-limit'

const positive = (x: number) => Number.isFinite(x) && x > 0

/** Evaluate single-driver impedance in free air or with a known perturbation. */
export function createDriverImpedance(driver: ThieleSmallDriver, medium: Medium,
  condition: DriverMeasurementCondition = { kind: 'free-air' }): (frequency: number) => Complex {
  const snapshot = { ...driver }
  const { cms, mms, rms, blSquared } = driverMotor(snapshot, medium)
  if (![snapshot.fsHz, snapshot.vasM3, snapshot.qes, snapshot.qms, snapshot.reOhms, snapshot.sdM2,
    medium.densityKgM3, medium.soundSpeedMps, cms, mms, rms, blSquared].every(positive) ||
    !Number.isFinite(snapshot.leHenries) || snapshot.leHenries < 0)
    throw new RangeError('Invalid driver impedance parameters')

  let mass = mms
  let stiffness = 1 / cms
  if (condition.kind === 'added-mass') {
    if (!positive(condition.massKg)) throw new RangeError('Added mass must be positive and finite')
    mass += condition.massKg
  } else if (condition.kind === 'sealed-box') {
    if (!positive(condition.volumeM3)) throw new RangeError('Test-box volume must be positive and finite')
    stiffness *= 1 + snapshot.vasM3 / condition.volumeM3
  }
  return (frequency) => {
    if (!positive(frequency)) throw new RangeError('Impedance frequency must be positive and finite')
    const w = 2 * Math.PI * frequency
    if (!Number.isFinite(w)) throw new RangeError('Impedance exceeds numeric support')
    const result = add(c(snapshot.reOhms, w * snapshot.leHenries),
      div(c(blSquared), c(rms, w * mass - stiffness / w)))
    if (![result.re, result.im].every(Number.isFinite)) throw new RangeError('Impedance exceeds numeric support')
    return result
  }
}

/** Evaluate the model directly at the measured frequencies. */
export function impedanceResiduals(samples: readonly ImpedanceSample[], impedanceAt: (frequency: number) => Complex) {
  if (!samples.length || samples.length > 4096) throw new RangeError('Supply 1 to 4096 impedance samples')
  return samples.map(({ frequency, impedanceOhms }) => {
    const complex = typeof impedanceOhms !== 'number'
    const scale = complex ? magnitude(impedanceOhms) : impedanceOhms
    if (!positive(frequency) || !positive(scale)) throw new RangeError('Invalid impedance sample')
    const predictedOhms = impedanceAt(frequency)
    const deltaOhms = complex ? sub(predictedOhms, impedanceOhms) : c(magnitude(predictedOhms) - impedanceOhms)
    const relativeError = magnitude(deltaOhms) / scale
    if (!Number.isFinite(relativeError)) throw new RangeError('Impedance residual exceeds numeric support')
    return { frequency, measuredOhms: impedanceOhms, predictedOhms,
      residualOhms: complex ? deltaOhms : deltaOhms.re, relativeError }
  })
}

function fitVector(samples: readonly ImpedanceSample[], impedanceAt: (frequency: number) => Complex): number[] {
  return impedanceResiduals(samples, impedanceAt).flatMap(({ measuredOhms, residualOhms }) => {
    if (typeof residualOhms === 'number') return [residualOhms / (measuredOhms as number)]
    const scale = magnitude(measuredOhms as Complex)
    return [residualOhms.re / scale, residualOhms.im / scale]
  })
}

type FitBound = FitRange & { initial: number }

const dot = (a: readonly number[], b: readonly number[]) => a.reduce((sum, x, i) => sum + x * b[i]!, 0)

/** Solve the damped normal equations by Cholesky factorization. */
function dampedStep(columns: number[][], residuals: number[], damping: number): number[] {
  const n = columns.length
  const factor = columns.map(() => Array<number>(n).fill(0))
  const intermediate: number[] = []
  for (let row = 0; row < n; row++) {
    for (let col = 0; col <= row; col++) {
      let value = dot(columns[row]!, columns[col]!)
      for (let k = 0; k < col; k++) value -= factor[row]![k]! * factor[col]![k]!
      if (row === col) value += damping * (dot(columns[row]!, columns[row]!) + 1e-12)
      factor[row]![col] = row === col ? Math.sqrt(value) : value / factor[col]![col]!
    }
    intermediate[row] = (-dot(columns[row]!, residuals) - dot(factor[row]!.slice(0, row), intermediate)) / factor[row]![row]!
  }
  const step: number[] = []
  for (let i = n - 1; i >= 0; i--) {
    let value = intermediate[i]!
    for (let j = i + 1; j < n; j++) value -= factor[j]![i]! * step[j]!
    step[i] = value / factor[i]![i]!
  }
  return step
}

function fitSettings(bounds: readonly FitBound[], options: ImpedanceFitOptions) {
  const maxIterations = options.maxIterations ?? 100
  const tolerance = options.tolerance ?? 1e-9
  const stepTolerance = options.normalizedStepTolerance ?? tolerance
  if (!Number.isSafeInteger(maxIterations) || maxIterations < 1 || maxIterations > 500 ||
      !positive(tolerance) || tolerance >= 1 || !positive(stepTolerance) || stepTolerance >= 1)
    throw new RangeError('Invalid impedance fit budget or tolerance')
  if (bounds.some(({ min, max, initial }) => ![min, max, initial].every(Number.isFinite) ||
      min < 0 || !(max > min) || initial < min || initial > max))
    throw new RangeError('Invalid impedance fit bounds or initial guess')
  return { maxIterations, tolerance, stepTolerance }
}

type FitSettings = ReturnType<typeof fitSettings>
type FitModel = {
  kind: ImpedanceFitCertificate['kind']
  request: string
  bounds: readonly FitBound[]
  settings: FitSettings
  evaluate(values: number[]): number[]
  enclose(values: readonly number[]): ReturnType<typeof evaluateImpedanceFit>
}

/** Bounded, local least-squares search with finite-difference trial steps. */
function searchFit({ bounds, evaluate, settings }: FitModel) {
  const { maxIterations, tolerance, stepTolerance } = settings
  const unpack = (point: number[]) => point.map((x, i) => {
    const { min, max } = bounds[i]!
    return x === 1 ? max : min + x * (max - min)
  })
  const jacobian = (point: number[], residuals: number[]) => point.map((value, i) => {
    const step = value + 1e-5 <= 1 ? 1e-5 : -1e-5
    const probe = point.slice()
    probe[i] = value + step
    return evaluate(unpack(probe)).map((r, j) => (r - residuals[j]!) / step)
  })
  let point = bounds.map(({ min, max, initial }) => (initial - min) / (max - min))
  let residuals = evaluate(unpack(point))
  let cost = dot(residuals, residuals)
  let iterations = 0
  let damping = 1e-3
  for (; iterations < maxIterations; iterations++) {
    if (Math.sqrt(cost / residuals.length) <= tolerance) break
    const columns = jacobian(point, residuals)
    const step = dampedStep(columns, residuals, damping)
    const candidate = point.map((value, i) => Math.max(0, Math.min(1, value + step[i]!)))
    if (candidate.every((value, i) => Math.abs(value - point[i]!) <= stepTolerance)) break
    const candidateResiduals = evaluate(unpack(candidate))
    const candidateCost = dot(candidateResiduals, candidateResiduals)
    if (candidateCost < cost) {
      point = candidate
      residuals = candidateResiduals
      cost = candidateCost
      damping = Math.max(damping / 3, 1e-9)
    } else damping *= 10
  }

  return { values: unpack(point), iterations, stoppedEarly: iterations < maxIterations,
    residuals, rms: Math.sqrt(cost / residuals.length),
    approximateJacobian: () => jacobian(point, residuals) }
}

function fitParameters<Parameter extends string>(names: readonly Parameter[], model: FitModel) {
  const { kind, request, bounds, settings: { tolerance }, enclose } = model
  const { values, iterations, stoppedEarly, residuals, rms, approximateJacobian } = searchFit(model)
  const activeBounds = values.flatMap<{ parameter: Parameter; bound: 'min' | 'max' }>((value, i) => {
    if (value === bounds[i]!.min) return [{ parameter: names[i]!, bound: 'min' }]
    if (value === bounds[i]!.max) return [{ parameter: names[i]!, bound: 'max' }]
    return []
  })
  const diagnostics = enclosedOr(() => certifyImpedanceFit(enclose(values), kind, request, values, tolerance, stoppedEarly, rms),
    undefined) ?? approximateDiagnostics(values, bounds, approximateJacobian(), residuals, rms, tolerance, stoppedEarly)
  const { status } = diagnostics
  return { values, iterations, activeBounds, ...diagnostics,
    converged: status === 'residual-target' || status === 'stationary' }
}

function approximateDiagnostics(values: readonly number[], bounds: readonly FitBound[], columns: number[][],
  residuals: number[], rmsRelativeError: number, tolerance: number, stepStalled: boolean) {
  let active = false
  const projectedGradient = Math.max(...columns.map((column, i) => {
    const gradient = dot(column, residuals) / residuals.length
    if (values[i] === bounds[i]!.min) {
      active = true
      return Math.max(0, -gradient)
    }
    if (values[i] === bounds[i]!.max) {
      active = true
      return Math.max(0, gradient)
    }
    return Math.abs(gradient)
  }))
  const sensitivityRank = localSensitivityRank(columns, residuals.length)
  const status = classifyImpedanceFit(sensitivityRank === bounds.length,
    rmsRelativeError <= tolerance, projectedGradient <= tolerance, active, stepStalled)
  return { status, rmsRelativeError, projectedGradient, sensitivityRank, certificate: undefined }
}

/** Pivoted QR rank estimate on the normalized coordinate Jacobian. */
function localSensitivityRank(columns: number[][], rows: number): number {
  const pending = [...columns]
  const energy = (column: number[]) => dot(column, column)
  const minimum = Math.max(rows * 1e-14, Math.max(...columns.map(energy)) * 1e-12)
  let rank = 0
  while (pending.length > 0) {
    const pivot = pending.reduce((a, b) => energy(a) >= energy(b) ? a : b)
    const lengthSquared = energy(pivot)
    if (!(lengthSquared > minimum)) break
    pending.splice(pending.indexOf(pivot), 1)
    const basis = pivot.map((value) => value / Math.sqrt(lengthSquared))
    for (const [i, column] of pending.entries()) {
      const projection = dot(basis, column)
      pending[i] = column.map((value, row) => value - projection * basis[row]!)
    }
    rank += 1
  }
  return rank
}

const driverKeys = ['fsHz', 'vasM3', 'qes', 'qms', 'reOhms', 'leHenries'] as const
export interface DriverImpedanceFit extends ImpedanceFitOptions {
  initial: ThieleSmallDriver
  medium: Medium
  freeAir: readonly ImpedanceSample[]
  perturbed: { condition: Exclude<DriverMeasurementCondition, { kind: 'free-air' }>; samples: readonly ImpedanceSample[] }
  bounds?: Partial<Record<typeof driverKeys[number], { min: number; max: number }>>
}

function driverFitModel(options: DriverImpedanceFit) {
  const { initial, medium, freeAir, perturbed } = options
  if ([freeAir, perturbed.samples].some((samples) => new Set(samples.map((point) => point.frequency)).size < 4))
    throw new RangeError('Each driver sweep requires at least four distinct frequencies')
  const bounds = driverKeys.map((key) => ({
    initial: initial[key],
    ...(options.bounds?.[key] ?? (key === 'leHenries'
      ? { min: 0, max: Math.max(initial.leHenries * 4, 0.002) }
      : { min: initial[key] / 4, max: initial[key] * 4 })),
  }))
  if (bounds.slice(0, -1).some(({ min }) => !positive(min))) throw new RangeError('Driver parameter bounds must be positive')
  const withParameters = (values: readonly number[]): ThieleSmallDriver => ({ ...initial,
    fsHz: values[0]!, vasM3: values[1]!, qes: values[2]!, qms: values[3]!,
    reOhms: values[4]!, leHenries: values[5]!,
  })
  return {
    kind: 'driver', request: impedanceFitRequest(options), bounds, settings: fitSettings(bounds, options), withParameters,
    evaluate(values) {
      const driver = withParameters(values)
      return [...fitVector(freeAir, createDriverImpedance(driver, medium)),
        ...fitVector(perturbed.samples, createDriverImpedance(driver, medium, perturbed.condition))]
    },
    enclose(values) {
      return evaluateImpedanceFit(driverFitSweeps(initial, medium, freeAir, perturbed.condition, perturbed.samples,
        bounds, values), bounds, values)
    },
  } satisfies FitModel & { withParameters: typeof withParameters }
}

/** Fit six T/S inputs with fixed Sd using paired free-air and perturbation sweeps. */
export function fitDriverImpedance(options: DriverImpedanceFit) {
  const { medium, freeAir, perturbed } = options
  const model = driverFitModel(options)
  const { values, ...fit } = fitParameters(driverKeys, model)
  const { withParameters } = model
  const driver = withParameters(values)
  return { ...fit, driver, freeAirResiduals: impedanceResiduals(freeAir, createDriverImpedance(driver, medium)),
    perturbedResiduals: impedanceResiduals(perturbed.samples, createDriverImpedance(driver, medium, perturbed.condition)) }
}

export type EnclosureFitParameter = 'volumeM3' | 'leakageQuality' | 'absorptionQuality' | 'portQuality' | 'effectiveLengthM' | 'radiatorMassKg'

type EnclosureFitRange = FitRange & { parameter: EnclosureFitParameter }

function enclosureFitModel(initial: CircuitInput, samples: readonly ImpedanceSample[],
  parameters: readonly EnclosureFitRange[], options: ImpedanceFitOptions) {
  const keys = parameters.map(({ parameter }) => parameter)
  if (!keys.length || new Set(keys).size !== keys.length || (keys.includes('leakageQuality') && keys.includes('absorptionQuality')) ||
      new Set(samples.map(({ frequency }) => frequency)).size <= keys.length)
    throw new RangeError('Select distinct, identifiable enclosure parameters and supply enough frequencies')
  const initialValues: Record<EnclosureFitParameter, number | undefined> = {
    volumeM3: initial.volumeM3, leakageQuality: initial.leakageQuality, absorptionQuality: initial.absorptionQuality,
    portQuality: initial.port?.quality, effectiveLengthM: initial.port?.ductPath ? undefined : initial.port?.effectiveLengthM,
    radiatorMassKg: initial.passiveRadiator?.movingMassKg,
  }
  const bounds = parameters.map(({ parameter, min, max }) => {
    const value = initialValues[parameter]
    if (value === undefined || !positive(min)) throw new RangeError('Parameter requires a positive bound and matching enclosure geometry')
    return { min, max, initial: value }
  })
  const withParameters = (values: readonly number[]): CircuitInput => {
    const result = { ...initial }
    for (const [i, key] of keys.entries()) {
      const value = values[i]!
      if (key === 'portQuality') result.port = { ...result.port!, quality: value }
      else if (key === 'effectiveLengthM') result.port = { ...result.port!, effectiveLengthM: value }
      else if (key === 'radiatorMassKg') result.passiveRadiator = { ...result.passiveRadiator!, movingMassKg: value }
      else result[key] = value
    }
    return result
  }
  return {
    kind: 'enclosure', request: impedanceFitRequest(initial, samples, parameters, options),
    bounds, settings: fitSettings(bounds, options), keys, withParameters,
    evaluate(values) {
      const at = createCircuit(withParameters(values))
      return fitVector(samples, (frequency) => at(frequency).impedanceOhms)
    },
    enclose(values) {
      return evaluateImpedanceFit(enclosureFitSweeps(initial, samples, keys, bounds, values), bounds, values)
    },
  } satisfies FitModel & { keys: typeof keys; withParameters: typeof withParameters }
}

/** Fit caller-selected enclosure parameters while holding the driver and other inputs fixed. */
export function fitEnclosureImpedance(initial: CircuitInput, samples: readonly ImpedanceSample[],
  parameters: readonly EnclosureFitRange[], options: ImpedanceFitOptions = {}) {
  const model = enclosureFitModel(initial, samples, parameters, options)
  const { values, ...fit } = fitParameters(model.keys, model)
  const { withParameters } = model
  const input = withParameters(values)
  const at = createCircuit(input)
  return { ...fit, input, residuals: impedanceResiduals(samples, (frequency) => at(frequency).impedanceOhms) }
}

function verifyFit(model: FitModel, certificate: Readonly<ImpedanceFitCertificate>): boolean {
  if (!matchesImpedanceFit(certificate, model.kind, model.request, model.bounds)) return false
  // Reuse the public model's input and sample validation before exact replay.
  model.evaluate(model.bounds.map(({ initial }) => initial))
  const diagnostics = model.enclose(certificate.values)
  return replayImpedanceFit(diagnostics, certificate, model.settings.tolerance, () => {
    const search = searchFit(model)
    if (search.values.some((value, i) => value !== certificate.values[i]))
      throw new RangeError('Certificate endpoint differs from the search')
    return search.stoppedEarly
  })
}

/** Replay a driver fit certificate against its original request. */
export function verifyDriverImpedanceFitCertificate(options: DriverImpedanceFit,
  certificate: Readonly<ImpedanceFitCertificate>): boolean {
  try {
    return verifyFit(driverFitModel(options), certificate)
  } catch {
    return false
  }
}

/** Replay an enclosure fit certificate against its original request. */
export function verifyEnclosureImpedanceFitCertificate(initial: CircuitInput, samples: readonly ImpedanceSample[],
  parameters: readonly EnclosureFitRange[], certificate: Readonly<ImpedanceFitCertificate>,
  options: ImpedanceFitOptions = {}): boolean {
  try {
    return verifyFit(enclosureFitModel(initial, samples, parameters, options), certificate)
  } catch {
    return false
  }
}
