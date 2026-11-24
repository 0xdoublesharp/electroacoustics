import { expect, it } from 'vitest'
import { div, reciprocal, type Complex } from './complex.js'
import { pressureSplDb } from './pressure.js'
import { createCircuit, type CircuitInput } from './circuit.js'
import { sealedAlignment } from './alignment.js'
import {
  biquadTransfer, bw24AttenuationDb, bw24Transfer, composeFilters, designBiquad,
  lr24AttenuationDb, lr24Transfer, type BiquadCoefficients, type ParametricEq,
} from './filters.js'
import {
  boundDuctPathPeakVelocityRatio, boundDuctPathTuning, ductPathImpedance,
  ductPathPeakVelocityRatio, ductPathTuning, type DuctPath,
} from './ductAcoustics.js'
import { passiveRadiatorMassForTuning, passiveRadiatorResonanceHz, passiveRadiatorTuningHz } from './passiveRadiator.js'
import { circuitFixture, odeFixture } from './testFixtures.js'

// Exact rational arithmetic for checking rounding and pressures outside the
// fixed-point range. Decode IEEE 754 directly from the input bit patterns.
type Ratio = readonly [numerator: bigint, denominator: bigint]
const buffer = new DataView(new ArrayBuffer(8))
function bits(value: number): bigint {
  buffer.setFloat64(0, value)
  return buffer.getBigUint64(0)
}
function fromBits(value: bigint): number {
  buffer.setBigUint64(0, value)
  return buffer.getFloat64(0)
}
const abs = (x: bigint) => x < 0n ? -x : x
function binaryRatio(value: number): Ratio {
  const word = bits(value)
  const exponent = Number((word >> 52n) & 0x7ffn)
  const fraction = word & ((1n << 52n) - 1n)
  const mantissa = fraction + (exponent === 0 ? 0n : 1n << 52n)
  const signed = word >> 63n ? -mantissa : mantissa
  const shift = BigInt(Math.max(1, exponent) - 1075)
  return scaleRatio([signed, 1n], shift)
}
function scaleRatio([n, d]: Ratio, exponent: bigint): Ratio {
  return exponent >= 0n ? [n << exponent, d] : [n, d << -exponent]
}
const ratioSum = ([a, b]: Ratio, [c, d]: Ratio): Ratio => [a * d + b * c, b * d]
const ratioProduct = ([a, b]: Ratio, [c, d]: Ratio): Ratio => [a * c, b * d]
const ratioDivide = ([a, b]: Ratio, [c, d]: Ratio): Ratio => [a * d, b * c]
const ratioSquare = (x: Ratio) => ratioProduct(x, x)
const ratioNegate = ([a, b]: Ratio): Ratio => [-a, b]
const ratioCompare = ([a, b]: Ratio, [c, d]: Ratio) => a * d - b * c
function exactQuotient(a: Complex, b: Complex): readonly [Ratio, Ratio] {
  const ar = binaryRatio(a.re), ai = binaryRatio(a.im)
  const br = binaryRatio(b.re), bi = binaryRatio(b.im)
  const norm = ratioSum(ratioSquare(br), ratioSquare(bi))
  return [
    ratioDivide(ratioSum(ratioProduct(ar, br), ratioProduct(ai, bi)), norm),
    ratioDivide(ratioSum(ratioProduct(ai, br), ratioNegate(ratioProduct(ar, bi))), norm),
  ]
}

// Compare the exact distances to both adjacent magnitudes. An equal distance
// requires an even significand, independently of the quotient's exponent.
function expectNearest(actual: number, [n, d]: Ratio) {
  expect(Number.isFinite(actual)).toBe(true)
  if (n === 0n) {
    expect(actual).toBe(0)
    return
  }
  expect(actual < 0 || Object.is(actual, -0)).toBe(n < 0n)
  const word = bits(Math.abs(actual))
  const distance = ([a, b]: Ratio): Ratio => [abs(a * d - abs(n) * b), b * d]
  const error = distance(binaryRatio(Math.abs(actual)))
  const neighbors = [word + 1n, ...(word === 0n ? [] : [word - 1n])]
  for (const neighbor of neighbors) {
    const neighborValue = fromBits(neighbor)
    const neighborRatio: Ratio = Number.isFinite(neighborValue)
      ? binaryRatio(neighborValue) : [1n << 1024n, 1n]
    const difference = ratioCompare(error, distance(neighborRatio))
    expect(difference <= 0n).toBe(true)
    if (difference === 0n) expect(word & 1n).toBe(0n)
  }
}

it('rounds exact complex quotients to nearest-even across the binary64 range', () => {
  const min = Number.MIN_VALUE, large = Number.MAX_VALUE / 4, ulp = Number.EPSILON
  const cases: [Complex, Complex][] = [
    [{ re: min, im: 3 * min }, { re: 2 * min, im: -min }],
    [{ re: large, im: -2 * large }, { re: 3 * large, im: large }],
    [{ re: min, im: large }, { re: 1, im: 0 }],
    [{ re: 3, im: -4 }, { re: 4, im: 3 }],
    [{ re: 1 + ulp, im: -1 }, { re: 1 - ulp, im: 1 }],
    [{ re: 1, im: 1 + ulp }, { re: 1, im: 1 }],
    [{ re: 1 + ulp, im: 1 + 2 * ulp }, { re: 1, im: 1 }],
    [{ re: -min, im: 3 * min }, { re: 2, im: 0 }],
  ]
  for (const [a, b] of cases) {
    const exact = exactQuotient(a, b)
    const actual = div(a, b)
    expectNearest(actual.re, exact[0])
    expectNearest(actual.im, exact[1])
  }
  for (const z of [{ re: large, im: large }, { re: 2 ** -1024, im: 2 ** -1024 }, { re: 0, im: -3 }]) {
    const exact = exactQuotient({ re: 1, im: 0 }, z)
    const actual = reciprocal(z)
    expectNearest(actual.re, exact[0])
    expectNearest(actual.im, exact[1])
  }
  const overflowThreshold: Ratio = [(1n << 1024n) - (1n << 970n), 1n]
  const tinyDivisor = { re: min, im: 0 }
  for (const a of [{ re: min, im: 1 }, { re: 1, im: 0 }]) {
    const exact = exactQuotient(a, tinyDivisor)
    expect(exact.some((part) => ratioCompare(part, overflowThreshold) >= 0n)).toBe(true)
    expect(() => div(a, tinyDivisor)).toThrow(RangeError)
  }
  expect(() => reciprocal(tinyDivisor)).toThrow(RangeError)
})

// 320-bit fixed point for ordinary-scale reference calculations, with π from
// Machin's identity and elementary functions from convergent power series.
const precision = 320n
const unit = 1n << precision
const fixedRatio = ([n, d]: Ratio) => n * unit / d
const fixed = (x: number) => fixedRatio(binaryRatio(x))
const realNumber = (x: bigint) => Number(x) / Number(unit)
const product = (a: bigint, b: bigint) => a * b / unit
const quotient = (a: bigint, b: bigint) => a * unit / b
const square = (x: bigint) => product(x, x)
function squareRoot(x: bigint): bigint {
  if (x === 0n) return 0n
  const radicand = x * unit
  let estimate = 1n << BigInt(Math.ceil(radicand.toString(2).length / 2))
  for (;;) {
    const next = (estimate + radicand / estimate) / 2n
    if (next >= estimate) return estimate
    estimate = next
  }
}
function arctangentReciprocal(n: bigint): bigint {
  let term = unit / n, sum = 0n
  for (let k = 1n; term !== 0n; k += 2n) {
    sum += term / k
    term /= -(n * n)
  }
  return sum
}
const pi = 16n * arctangentReciprocal(5n) - 4n * arctangentReciprocal(239n)
const tau = 2n * pi
function sinCos(angle: bigint): readonly [bigint, bigint] {
  let sine = angle, cosine = unit
  let sinTerm = angle, cosTerm = unit
  const minusAngleSquared = -square(angle)
  for (let n = 2n; sinTerm !== 0n || cosTerm !== 0n; n += 2n) {
    cosTerm = product(cosTerm, minusAngleSquared) / (n * (n - 1n))
    sinTerm = product(sinTerm, minusAngleSquared) / (n * (n + 1n))
    cosine += cosTerm
    sine += sinTerm
  }
  return [sine, cosine]
}
function logMantissa(x: bigint): bigint {
  const z = quotient(x - unit, x + unit)
  const zSquared = square(z)
  let sum = 0n
  for (let term = z, k = 1n; term !== 0n; term = product(term, zSquared), k += 2n) sum += term / k
  return 2n * sum
}
const log2 = logMantissa(2n * unit)
function logRatio([n, d]: Ratio): bigint {
  let exponent = BigInt(n.toString(2).length - d.toString(2).length)
  let mantissa = fixedRatio(scaleRatio([n, d], -exponent))
  if (mantissa < unit) {
    mantissa *= 2n
    exponent--
  }
  return logMantissa(mantissa) + exponent * log2
}
const log10 = logRatio([10n, 1n])
function powerOfTen(exponent: bigint): bigint {
  const argument = product(log10, exponent)
  let sum = unit
  for (let term = unit, i = 1n; term !== 0n; i++) {
    term = product(term, argument) / i
    sum += term
  }
  return sum
}

// Log of the exact squared pressure ratio, with clamping in rational space.
const pressureFloorSquared = ratioSquare(binaryRatio(1e-12))
const referencePaSquared = ratioSquare(binaryRatio(20e-6))
function splReference(re: Ratio, im: Ratio): number {
  const power = ratioSum(ratioSquare(re), ratioSquare(im))
  const clamped = ratioCompare(power, pressureFloorSquared) < 0n ? pressureFloorSquared : power
  return realNumber(10n * quotient(logRatio(ratioDivide(clamped, referencePaSquared)), log10))
}
function expectError(actual: number, expected: number, tolerance: number, label?: string) {
  expect(Math.abs(actual - expected), label).toBeLessThanOrEqual(tolerance)
}

it('matches the exact pressure-ratio logarithm through overflow and floor edges', () => {
  for (const [re, im] of [
    [Number.MAX_VALUE, -Number.MAX_VALUE], [1e305, 1e-250], [2e250, 3e250],
    [0, 0], [Number.MIN_VALUE, Number.MIN_VALUE], [3e-13, 4e-13], [6e-13, 8e-13], [3e-12, 4e-12],
  ] as const) {
    expectError(pressureSplDb({ re, im }), splReference(binaryRatio(re), binaryRatio(im)), 2e-12)
  }
  const atUnit = pressureSplDb({ re: 3, im: -4 })
  for (const exponent of [-40, -1, 70, 1000]) {
    const scale = 2 ** exponent
    const expectedDifference = realNumber(20n * BigInt(exponent) * quotient(log2, log10))
    expectError(pressureSplDb({ re: 3 * scale, im: -4 * scale }) - atUnit, expectedDifference, 2e-12)
  }
})

// Fixed-point complex arithmetic shared by the independent filter and nodal solvers.
type Phasor = readonly [real: bigint, imaginary: bigint]
const phasor = (re: bigint, im = 0n): Phasor => [re, im]
const zero = phasor(0n), one = phasor(unit)
const plus = ([a, b]: Phasor, [c, d]: Phasor): Phasor => [a + c, b + d]
const negative = ([a, b]: Phasor): Phasor => [-a, -b]
const minus = (a: Phasor, b: Phasor) => plus(a, negative(b))
const scale = ([a, b]: Phasor, x: bigint): Phasor => [product(a, x), product(b, x)]
const times = ([a, b]: Phasor, [c, d]: Phasor): Phasor => [product(a, c) - product(b, d), product(a, d) + product(b, c)]
const norm = ([a, b]: Phasor) => square(a) + square(b)
function over(a: Phasor, b: Phasor): Phasor {
  const [re, im] = times(a, [b[0], -b[1]])
  const denominator = norm(b)
  return [quotient(re, denominator), quotient(im, denominator)]
}
function expectPhasor(actual: Complex, expected: Phasor, tolerance: number, floor = 1) {
  for (const [component, target] of [[actual.re, expected[0]], [actual.im, expected[1]]] as const) {
    const targetNumber = realNumber(target)
    expectError(component, targetNumber, tolerance * Math.max(floor, Math.abs(targetNumber)))
  }
}

function polar(angle: bigint): Phasor {
  const [sine, cosine] = sinCos(angle)
  return [cosine, sine]
}

type Coefficients = readonly [b0: bigint, b1: bigint, b2: bigint, a1: bigint, a2: bigint]
const coefficientKeys = ['b0', 'b1', 'b2', 'a1', 'a2'] as const
function biquadReference(frequency: number, sampleRate: number, [b0, b1, b2, a1, a2]: Coefficients): Phasor {
  const z = 2 * frequency === sampleRate ? phasor(-unit) : polar(-product(tau, quotient(fixed(frequency), fixed(sampleRate))))
  const zSquared = times(z, z)
  return over(plus(plus(phasor(b0), scale(z, b1)), scale(zSquared, b2)),
    plus(plus(one, scale(z, a1)), scale(zSquared, a2)))
}

it('meets the biquad per-component 2^-40 contract at nulls, endpoints, and near poles', () => {
  const sampleRate = 48000
  const a2 = 1 - 1e-6
  const nearDc = 1 - a2 - 2 ** -40
  const cases: [BiquadCoefficients, number[]][] = [
    [{ kind: 'biquad', b0: 1e-10, b1: -2.5e-11, b2: 5e-11, a1: 0, a2 }, [0, 12000 * (1 - 1e-7), 12000, 12000 * (1 + 1e-7), 24000]],
    [{ kind: 'biquad', b0: 1, b1: -0.25, b2: 0.5, a1: 0, a2 }, [11800, 12200]],
    [{ kind: 'biquad', b0: 1, b1: -2, b2: 1, a1: -nearDc, a2: -a2 }, [0, 1e-7, 0.01, 24000]],
    [{ kind: 'biquad', b0: 1e-10, b1: 2e-10, b2: 1e-10, a1: nearDc, a2: -a2 }, [0, 24000 - 1e-7, 24000]],
    [{ kind: 'biquad', b0: 0, b1: 0, b2: 0, a1: 0, a2 }, [0, 12000, 24000]],
  ]
  for (const [coefficients, frequencies] of cases) {
    const { b0, b1, b2, a1, a2 } = coefficients
    const exactCoefficients = [fixed(b0), fixed(b1), fixed(b2), fixed(a1), fixed(a2)] as const
    for (const frequency of frequencies) {
      let actual: Complex
      try {
        actual = biquadTransfer(frequency, sampleRate, coefficients)
      } catch (cause) {
        throw new Error(`Biquad at ${frequency} Hz, a1=${a1}, a2=${a2}`, { cause })
      }
      const [re, im] = biquadReference(frequency, sampleRate, exactCoefficients)
      for (const [component, target] of [[actual.re, re], [actual.im, im]] as const) {
        const allowance = (abs(target) > unit ? abs(target) : unit) >> 40n
        expect(abs(fixed(component) - target) <= allowance, `${frequency} Hz: ${component} versus ${realNumber(target)}`).toBe(true)
      }
    }
  }
  // The larger numerator makes the same near-pole response too uncertain to
  // certify at the evaluator's current precision.
  expect(() => biquadTransfer(12000 * (1 - 1e-7), sampleRate,
    { kind: 'biquad', b0: 1, b1: -0.25, b2: 0.5, a1: 0, a2 })).toThrow(RangeError)
})

function designReference(stage: ParametricEq, sampleRate: number): Coefficients {
  const amplitude = powerOfTen(fixed(stage.gainDb) / 40n)
  const frequency = quotient(fixed(stage.frequencyHz), fixed(sampleRate))
  const mirrored = stage.kind === 'high-shelf'
  const [sine, cosine] = sinCos(product(tau, mirrored ? unit / 2n - frequency : frequency))
  if (stage.kind === 'peaking') {
    const alpha = quotient(sine, 2n * fixed(stage.q))
    const amplitudeAlpha = product(alpha, amplitude), inverseAlpha = quotient(alpha, amplitude)
    const a0 = unit + inverseAlpha
    return [quotient(unit + amplitudeAlpha, a0), quotient(-2n * cosine, a0),
      quotient(unit - amplitudeAlpha, a0), quotient(-2n * cosine, a0), quotient(unit - inverseAlpha, a0)]
  }
  // Frequency inversion (z -> -z) maps a low shelf into a high shelf.
  const edge = product(sine, squareRoot(product(square(amplitude) + unit, quotient(unit, fixed(stage.slope)) - unit) + 2n * amplitude))
  const sum = amplitude + unit, difference = amplitude - unit
  const bCenter = sum - product(difference, cosine), aCenter = sum + product(difference, cosine)
  const a0 = aCenter + edge
  const sign = mirrored ? -1n : 1n
  return [quotient(product(amplitude, bCenter + edge), a0),
    quotient(2n * sign * product(amplitude, difference - product(sum, cosine)), a0),
    quotient(product(amplitude, bCenter - edge), a0),
    quotient(-2n * sign * (difference + product(sum, cosine)), a0), quotient(aCenter - edge, a0)]
}

function analogReference(frequency: number, cutoff: number, kind: 'lowpass' | 'highpass' | 'butterworth'): Phasor {
  const s = phasor(0n, quotient(fixed(frequency), fixed(cutoff)))
  const sSquared = times(s, s)
  const quadratic = (damping: bigint) => plus(plus(one, scale(s, damping)), sSquared)
  const sqrt2 = squareRoot(2n * unit)
  const factors = kind === 'butterworth'
    ? [quadratic(squareRoot(2n * unit - sqrt2)), quadratic(squareRoot(2n * unit + sqrt2))] as const
    : [quadratic(sqrt2), quadratic(sqrt2)] as const
  return over(kind === 'lowpass' ? one : times(sSquared, sSquared), times(...factors))
}

it('matches fourth-order analog transfer and attenuation over fourteen decades', () => {
  const cutoff = 100
  for (const ratio of [1e-7, 1e-3, 0.5, 1, 2, 1e3, 1e7]) {
    const frequency = cutoff * ratio
    const cases = [
      { kind: 'highpass', transfer: lr24Transfer(frequency, cutoff, 'highpass'), db: lr24AttenuationDb(frequency, cutoff, 'highpass') },
      { kind: 'lowpass', transfer: lr24Transfer(frequency, cutoff, 'lowpass'), db: lr24AttenuationDb(frequency, cutoff, 'lowpass') },
      { kind: 'butterworth', transfer: bw24Transfer(frequency, cutoff), db: bw24AttenuationDb(frequency, cutoff) },
    ] as const
    for (const { kind, transfer, db } of cases) {
      const expected = analogReference(frequency, cutoff, kind)
      expectPhasor(transfer, expected, 3e-14, realNumber(squareRoot(norm(expected))))
      const exactDb = realNumber(10n * quotient(logRatio([norm(expected), unit]), log10))
      expectError(db, exactDb, Math.abs(exactDb) * 3e-13, `${kind}, frequency ratio ${ratio}`)
    }
  }
})

it('matches high-precision EQ design and a mixed analog and digital filter cascade', () => {
  const sampleRate = 48000
  const stages = [
    { kind: 'peaking', frequencyHz: 480, gainDb: 9, q: 4 },
    { kind: 'low-shelf', frequencyHz: 1200, gainDb: 6, slope: 0.75 },
    { kind: 'high-shelf', frequencyHz: 9000, gainDb: -5, slope: 0.8 },
  ] as const
  const expectedCoefficients = stages.map((stage) => designReference(stage, sampleRate))
  for (const [i, stage] of stages.entries()) {
    const designed = designBiquad(stage, sampleRate)
    for (const [j, key] of coefficientKeys.entries())
      expectError(designed[key], realNumber(expectedCoefficients[i]![j]!), 1e-14, `${stage.kind} ${key}`)
  }
  const gainDb = -2, delaySeconds = 0.00003125
  for (const frequency of [7, 480, 5000, 24000]) {
    const analog = times(analogReference(frequency, 60, 'butterworth'), analogReference(frequency, 3000, 'lowpass'))
    const delayedGain = scale(polar(-product(tau, product(fixed(frequency), fixed(delaySeconds)))), powerOfTen(fixed(gainDb) / 20n))
    const expected = expectedCoefficients.reduce((response, coefficients) =>
      times(response, biquadReference(frequency, sampleRate, coefficients)), times(analog, delayedGain))
    const actual = composeFilters(frequency, { highpassType: 'BW24', highpassHz: 60, lowpassHz: 3000,
      gainDb, delaySeconds, digital: { sampleRateHz: sampleRate, stages } })
    expectPhasor(actual, expected, 2e-12)
  }
})

// Solve a complex augmented system with pivoting. The unknowns are current
// per driver, cone velocity, cavity pressure, and auxiliary outward flow.
function solveNodal(rows: Phasor[][]): Phasor[] {
  const size = rows.length
  for (let column = 0; column < size; column++) {
    let pivot = column
    for (let i = column + 1; i < size; i++) {
      if (norm(rows[i]![column]!) > norm(rows[pivot]![column]!)) pivot = i
    }
    const pivotRow = rows[pivot]!
    rows[pivot] = rows[column]!
    const normalized = pivotRow.map((entry) => over(entry, pivotRow[column]!))
    rows[column] = normalized
    for (const [i, row] of rows.entries()) {
      if (i === column) continue
      const factor = row[column]!
      rows[i] = row.map((entry, j) => minus(entry, times(factor, normalized[j]!)))
    }
  }
  return rows.map((row) => row[size]!)
}

function circuitReference(input: CircuitInput, frequency: number, omega = product(tau, fixed(frequency))) {
  const { driver, passiveRadiator: radiator, port } = input
  const speed = fixed(input.medium.soundSpeedMps), density = fixed(input.medium.densityKgM3)
  const bulkModulus = product(density, square(speed))
  const cavityCompliance = quotient(fixed(input.volumeM3), bulkModulus)
  const coneArea = fixed(driver.sdM2), driverCount = BigInt(input.quantity ?? 1)
  const series = BigInt(input.seriesDrivers ?? 1), totalConeArea = coneArea * driverCount
  const driverStiffness = quotient(product(bulkModulus, square(coneArea)), fixed(driver.vasM3))
  const resonance = product(tau, fixed(driver.fsHz))
  const coneMass = quotient(driverStiffness, square(resonance))
  const coneMechanical = phasor(quotient(driverStiffness, product(resonance, fixed(driver.qms))),
    product(omega, coneMass) - quotient(driverStiffness, omega))
  const motor = squareRoot(quotient(product(product(resonance, coneMass), fixed(driver.reOhms)), fixed(driver.qes)))
  const blocked = phasor(fixed(driver.reOhms), product(omega, fixed(driver.leHenries)))

  const lockedConeTuning = squareRoot(quotient(driverStiffness +
    quotient(square(coneArea) * driverCount, cavityCompliance), coneMass))
  let characteristic = quotient(unit, product(lockedConeTuning, cavityCompliance))
  let auxiliary = one
  if (port) {
    const mass = quotient(product(density, fixed(port.effectiveLengthM!)), fixed(port.areaM2!))
    characteristic = squareRoot(quotient(mass, cavityCompliance))
    auxiliary = phasor(port.quality === Infinity ? 0n : quotient(characteristic, fixed(port.quality)), product(omega, mass))
  } else if (radiator) {
    const areaSquared = square(fixed(radiator.sdM2)) * BigInt(radiator.quantity ?? 1)
    const mass = fixed(radiator.movingMassKg)
    characteristic = squareRoot(quotient(mass, product(cavityCompliance, areaSquared)))
    auxiliary = [quotient(fixed(radiator.mechanicalResistanceNsPerM), areaSquared),
      quotient(product(omega, mass) - quotient(unit, product(omega, fixed(radiator.complianceMPerN))), areaSquared)]
  }
  const conductance = (quality: number) => quality === Infinity ? 0n : quotient(unit, product(fixed(quality), characteristic))
  const leak = conductance(input.leakageQuality)
  const shunt = phasor(leak + conductance(input.absorptionQuality), product(omega, cavityCompliance))
  const voltage = fixed(input.voltageRms)
  const [driverCurrent, velocity, pressure, branchFlow] = solveNodal([
    [blocked, phasor(motor), zero, zero, phasor(voltage / series)],
    [phasor(-motor), coneMechanical, phasor(-coneArea), zero, zero],
    [zero, phasor(totalConeArea), shunt, one, zero],
    [zero, zero, port || radiator ? negative(one) : zero, auxiliary, zero],
  ]) as [Phasor, Phasor, Phasor, Phasor]
  const current = scale(driverCurrent, unit * (driverCount / series))
  const cone = scale(velocity, totalConeArea)
  const netFlow = plus(plus(cone, branchFlow), scale(pressure, leak))
  const pressureAtOneMeter = times(netFlow, phasor(0n,
    quotient(product(density, omega), input.radiationSolidAngle === undefined ? tau : fixed(input.radiationSolidAngle))))
  const distance = binaryRatio(input.distanceM ?? 1)
  return {
    current, cone, branchFlow, pressure,
    impedance: over(phasor(voltage), current),
    splDb: splReference(ratioDivide([pressureAtOneMeter[0], unit], distance),
      ratioDivide([pressureAtOneMeter[1], unit], distance)),
  }
}

it('preserves circuit SPL at extreme distances and clamps at the pressure floor', () => {
  const frequency = 37
  const atOneMeter = createCircuit(circuitFixture)(frequency).splDb
  for (const distanceM of [1e-305, 1e-150, 1, 1e8, 1e250]) {
    const input = { ...circuitFixture, distanceM }
    const actual = createCircuit(input)(frequency).splDb
    expectError(actual, circuitReference(input, frequency).splDb, 2e-12)
    if (distanceM < 1e250) {
      const difference = realNumber(-20n * quotient(logRatio(binaryRatio(distanceM)), log10))
      expectError(actual - atOneMeter, difference, 2e-12)
    } else {
      expectError(actual, splReference([0n, 1n], [0n, 1n]), 2e-12)
    }
  }
})

it('matches an independent nodal solve for sealed, vented, and radiator circuits with different wiring', () => {
  const radiator = { movingMassKg: 0.061, complianceMPerN: 0.001, mechanicalResistanceNsPerM: 1.25, sdM2: 0.04, quantity: 2 }
  const port = { areaM2: 0.012, effectiveLengthM: 0.3, quality: 13 }
  const cases = [
    { ...circuitFixture, quantity: 4, seriesDrivers: 4, leakageQuality: 12, absorptionQuality: 24 },
    { ...circuitFixture, port, quantity: 4, seriesDrivers: 1, leakageQuality: 12, absorptionQuality: 24 },
    { ...circuitFixture, passiveRadiator: radiator, quantity: 4, seriesDrivers: 2, leakageQuality: 12, absorptionQuality: 24 },
  ]
  for (const input of cases) {
    const at = createCircuit(input)
    for (const frequency of [12, 33, 83]) {
      const reference = circuitReference(input, frequency)
      const point = at(frequency)
      expectPhasor(point.impedanceOhms, reference.impedance, 3e-13)
      expectPhasor(point.currentAmps, reference.current, 3e-13)
      expectPhasor(point.coneVolumeVelocityM3s, reference.cone, 3e-13)
      expectPhasor(point.radiatorVolumeVelocityM3s ?? point.mouthVolumeVelocityM3s, reference.branchFlow, 3e-13)
      expectError(point.splDb, reference.splDb, 2e-12)
    }
  }
  const { medium, volumeM3 } = circuitFixture
  const stiffness = quotient(unit, fixed(radiator.complianceMPerN))
  const mass = fixed(radiator.movingMassKg)
  const cavityStiffness = quotient(product(fixed(medium.densityKgM3), square(fixed(medium.soundSpeedMps))), fixed(volumeM3))
  const totalStiffness = stiffness + product(2n * square(fixed(radiator.sdM2)), cavityStiffness)
  expectError(passiveRadiatorResonanceHz(radiator), realNumber(quotient(squareRoot(quotient(stiffness, mass)), tau)), 2e-14)
  expectError(passiveRadiatorTuningHz(radiator, volumeM3, medium),
    realNumber(quotient(squareRoot(quotient(totalStiffness, mass)), tau)), 2e-14)
  const targetHz = 35
  const fitted = passiveRadiatorMassForTuning(radiator, volumeM3, medium, targetHz)
  expectError(fitted.movingMassKg, realNumber(quotient(totalStiffness, square(product(tau, fixed(targetHz))))), 2e-16)
})

it('handles an exact lossless vent cancellation and a lossless radiator free notch', () => {
  // At ω=1, the vent's unit inertance cancels the unit cavity compliance.
  // The same ω is the free resonance of a unit-mass, unit-compliance radiator.
  const frequency = 1 / (2 * Math.PI)
  expect(2 * Math.PI * frequency).toBe(1)
  const base = { ...circuitFixture, volumeM3: 1, medium: { densityKgM3: 1, soundSpeedMps: 1 },
    driver: { ...circuitFixture.driver, fsHz: 0.125, vasM3: 0.5, sdM2: 0.25 } }
  const vented = { ...base, port: { areaM2: 1, effectiveLengthM: 1, quality: Infinity } }
  const ventReference = circuitReference(vented, frequency, unit)
  const ventPoint = createCircuit(vented)(frequency)
  expect(ventPoint.coneExcursionPeakM).toBe(0)
  expectPhasor(ventPoint.coneVolumeVelocityM3s, ventReference.cone, 2e-15)
  expectPhasor(ventPoint.currentAmps, ventReference.current, 2e-15)
  expectPhasor(ventPoint.mouthVolumeVelocityM3s, ventReference.branchFlow, 2e-15)
  expectPhasor(ventPoint.impedanceOhms, phasor(fixed(base.driver.reOhms)), 2e-15)

  const passiveRadiator = { movingMassKg: 1, complianceMPerN: 1, mechanicalResistanceNsPerM: 0, sdM2: 0.5, quantity: 2 }
  const passive = { ...base, passiveRadiator }
  const radiatorReference = circuitReference(passive, frequency, unit)
  const radiatorPoint = createCircuit(passive)(frequency)
  expect(abs(radiatorReference.pressure[0]) + abs(radiatorReference.pressure[1]) < unit >> 250n).toBe(true)
  expectPhasor(radiatorPoint.radiatorVolumeVelocityM3s!, radiatorReference.branchFlow, 2e-15)
  expectPhasor(radiatorPoint.coneVolumeVelocityM3s, negative(radiatorReference.branchFlow), 2e-15)
  expectError(radiatorPoint.splDb, radiatorReference.splDb, 2e-12)
  expectError(radiatorPoint.splDb, splReference([0n, 1n], [0n, 1n]), 2e-12)
})

it('resolves near-pole impedance cancellation at high mechanical Q', () => {
  const input = { ...circuitFixture, driver: { ...circuitFixture.driver, qms: 1e8 } }
  const { driver } = input
  const nominal = driver.fsHz * Math.sqrt(1 + driver.vasM3 / input.volumeM3)
  const at = createCircuit(input)
  for (const frequency of [nominal * (1 - 1e-9), nominal, nominal * (1 + 1e-9)]) {
    const actual = at(frequency)
    const expected = circuitReference(input, frequency)
    const impedanceScale = realNumber(squareRoot(norm(expected.impedance)))
    expect(impedanceScale).toBeGreaterThan(1e9)
    expectPhasor(actual.impedanceOhms, expected.impedance, 8e-8, impedanceScale)
    expectPhasor(actual.currentAmps, expected.current, 8e-8, realNumber(squareRoot(norm(expected.current))))
  }
})

const ductSpeed = 343, ductDensity = 1.2
const cutoffHz = 120
const inertanceFactor = 1.17, complianceFactor = 1.08
const sectionK = (2 * Math.PI * cutoffHz / ductSpeed) * Math.sqrt(inertanceFactor * complianceFactor)
const taperInlet = 0.008, taperOutlet = 0.032
const taperLength = Math.log(Math.sqrt(taperOutlet / taperInlet)) / sectionK
const taperedPath: DuctPath = {
  count: 2, inletCorrectionMeters: 0.027, outletCorrectionMeters: 0.036,
  junctionInertanceLengthsMeters: [0.018, -0.009], inertanceFactor, complianceFactor,
  sections: [
    { profile: 'straight', lengthMeters: 0.23, inletAreaSquareMeters: 0.012, outletAreaSquareMeters: 0.012 },
    { profile: 'conical', lengthMeters: 0.19, inletAreaSquareMeters: 0.012, outletAreaSquareMeters: taperInlet },
    { profile: 'exponential', lengthMeters: taperLength, inletAreaSquareMeters: taperInlet, outletAreaSquareMeters: taperOutlet },
  ],
}

function bisectZero(evaluate: (x: number) => number, low: number, high: number) {
  const initialSign = Math.sign(evaluate(low))
  expect(initialSign * evaluate(high)).toBeLessThan(0)
  for (let i = 0; i < 38; i++) {
    const middle = (low + high) / 2
    if (initialSign * evaluate(middle) > 0) low = middle
    else high = middle
  }
  return (low + high) / 2
}

it('agrees with RK4 for corrected parallel ducts across cutoff and on both sides of a pole', () => {
  // With mouth flow fixed to one, inlet flow crosses zero at the impedance pole.
  const flowAt = (frequency: number) => 1 / odeFixture(taperedPath, frequency, 1024).ratio
  const pole = bisectZero(flowAt, 50, 150)
  expect(Math.log(Math.sqrt(taperOutlet / taperInlet)) / taperLength).toBe(sectionK)
  const frequencies = [0.5 * cutoffHz, cutoffHz, 1.5 * cutoffHz, pole * (1 - 1e-5), pole * (1 + 1e-5)]
  for (const frequency of frequencies) {
    const coarse = odeFixture(taperedPath, frequency, 2048)
    const reference = odeFixture(taperedPath, frequency, 4096)
    const actual = ductPathImpedance(taperedPath, frequency, ductSpeed, ductDensity, 17)
    const referenceReactance = reference.reactance / taperedPath.count
    expectError(coarse.reactance / reference.reactance, 1, 2e-8, `RK4 step-halving at ${frequency} Hz`)
    expect(actual.impedance.re).toBe(17)
    expectError(actual.impedance.im / referenceReactance, 1, 2e-8, `reactance at ${frequency} Hz`)
    expectError(actual.mouthFlowRatio.re / reference.ratio, 1, 2e-8, `mouth flow at ${frequency} Hz`)
    if (Math.abs(frequency / pole - 1) < 2e-5) expect(Math.abs(actual.mouthFlowRatio.re)).toBeGreaterThan(1e4)
    const peak = ductPathPeakVelocityRatio(taperedPath, frequency, ductSpeed, ductDensity)
    expectError(peak / reference.peak, 1, 2e-7, `peak airspeed at ${frequency} Hz`)

    const bounded = boundDuctPathPeakVelocityRatio(taperedPath, frequency, ductSpeed, ductDensity, { relativeTolerance: 0.005 })
    if (bounded.status !== 'resolved') throw new Error(`Peak bound at ${frequency} Hz: ${bounded.reason}`)
    // The RK4 sample grid resolves interior extrema to this relative slack.
    const samplingSlack = Math.abs(coarse.peak - reference.peak) + 2e-7 * reference.peak
    expect(bounded.lower).toBeLessThanOrEqual(reference.peak + samplingSlack)
    expect(bounded.upper).toBeGreaterThanOrEqual(reference.peak - samplingSlack)
    expect((bounded.upper - bounded.lower) / bounded.lower).toBeLessThanOrEqual(0.005)
  }
})

it('encloses the independent fundamental tuning of the corrected three-section duct', () => {
  const volumeM3 = 0.10
  const residual = (frequency: number) => {
    const { reactance } = odeFixture(taperedPath, frequency, 2048)
    const cavitySusceptance = 2 * Math.PI * frequency * volumeM3 / (ductDensity * ductSpeed ** 2)
    return cavitySusceptance * reactance / taperedPath.count - 1
  }
  const reference = bisectZero(residual, 1, 50)
  expectError(ductPathTuning(taperedPath, volumeM3, ductSpeed), reference, 1e-9)
  const bound = boundDuctPathTuning(taperedPath, volumeM3, ductSpeed)
  if (bound.status !== 'resolved') throw new Error(`Tuning bound: ${bound.reason}`)
  expect(residual(bound.lower)).toBeLessThan(0)
  expect(residual(bound.upper)).toBeGreaterThan(0)
  expect((bound.upper - bound.lower) / bound.lower).toBeLessThanOrEqual(1e-5)
})

function impedancePeak(input: CircuitInput, low: number, high: number): number {
  const at = createCircuit(input)
  const magnitude = (frequency: number) => {
    const { re, im } = at(frequency).impedanceOhms
    return Math.hypot(re, im)
  }
  const endpoints = [magnitude(low), magnitude(high)]
  for (let i = 0; i < 36; i++) {
    const left = low + (high - low) / 3, right = high - (high - low) / 3
    if (magnitude(left) < magnitude(right)) low = left
    else high = right
  }
  const peak = (low + high) / 2
  expect(magnitude(peak)).toBeGreaterThan(Math.max(...endpoints))
  return peak
}

it('predicts the THOR sealed resonance within 0.5 Hz of the impedance-derived measurement', () => {
  // Peerless 830500 data sheet and Linkwitz's completed, unstuffed 47 L box.
  // https://madisound.com/pdf/peerless/830500.pdf
  // https://www.linkwitzlab.com/thor-design.htm
  // https://www.linkwitzlab.com/thor-measmt.htm
  const input = { ...circuitFixture, volumeM3: 0.047,
    driver: { fsHz: 18.1, vasM3: 0.1392, qts: 0.20, qms: 3.70, qes: 0.21, reOhms: 3.5, leHenries: 0, sdM2: 0.0466 } }
  const { fcHz } = sealedAlignment(input.driver, input.volumeM3)
  // Use the same zero-inductance model as the impedance-derived pole estimate.
  expectError(impedancePeak(input, 28, 45), fcHz, 1e-5)
  expectError(fcHz, 36.03, 0.01)
  expectError(fcHz, Math.sqrt(19 * 67), 0.5)
})

it('reproduces the Illinois vented model and its larger upper-peak measurement discrepancy', () => {
  // Thomas Jerome, Physics 406, Spring 2016, pp. 9 and 13. The report's
  // appendix gives Le in mH and specifies one flush end per vent.
  // https://courses.physics.illinois.edu/phys406/sp2017/Student_Projects/Spring16/Thomas_Jerome_Physics_406_Final_Report_Sp16.pdf
  const radiusM = 0.0254
  const input = { ...circuitFixture, volumeM3: 3.158 * 0.3048 ** 3, leakageQuality: 5.301,
    driver: { fsHz: 66.23, vasM3: 0.04268, qms: 2.442, qes: 1.395, reOhms: 7.2, leHenries: 0.0003, sdM2: Math.PI * 0.08 ** 2 },
    port: { areaM2: 2 * Math.PI * radiusM ** 2, effectiveLengthM: 0.0635 + (0.61 + 0.85) * radiusM, quality: Infinity } }
  const lower = impedancePeak(input, 22, 33), upper = impedancePeak(input, 60, 100)
  expectError(lower, 28.74, 0.05)
  expectError(upper, 83.83, 0.05)
  expectError(lower, 28.91, 0.25)
  // The report gives a high-biased free-air Fs as one possible cause of the gap.
  expect(upper - 72.62).toBeGreaterThan(10)
  expectError(upper, 72.62, 12)
})

it('predicts the PURIFI SPK16 test-box impedance peaks within 0.5 Hz of the measured trace', () => {
  // First-fit baseline in “Box Model Parameter Identification”. Recover the
  // radiator compliance from its fitted free resonance and moving mass. Sum
  // the two blocked inductances for the low-frequency single-Le model.
  // https://purifi-audio.com/blog/tech-notes-1/spk16-reference-design-12
  const movingMassKg = 0.03956
  const input = { ...circuitFixture, volumeM3: 0.02211, leakageQuality: 53.77, absorptionQuality: 101.9,
    driver: { fsHz: 29.82, vasM3: 0.0229, qms: 4.974, qes: 0.3349, reOhms: 3.565,
      leHenries: (0.8432 + 0.304) * 1e-3, sdM2: 0.01327 },
    passiveRadiator: { movingMassKg, complianceMPerN: 1 / (movingMassKg * (2 * Math.PI * 25.75) ** 2),
      mechanicalResistanceNsPerM: 1.088, sdM2: 0.01327, quantity: 2 } }
  const lower = impedancePeak(input, 22, 33), upper = impedancePeak(input, 45, 70)
  expectError(lower, 28.11, 0.05)
  expectError(upper, 56.24, 0.05)
  expectError(lower, 28, 0.5)
  expectError(upper, 56, 0.5)
})
