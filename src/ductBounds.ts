import { dyadicIntervals as math, outwardBinary64, type DyadicInterval as Box } from './dyadicInterval.js'
import type { DuctPath } from './ductAcoustics.js'
import { enclosedOr, IntervalRangeError } from './interval.js'

const { exact, minus, one, pi, plus, quotient, root, square, times, zero } = math
const scale = one.lo
const two = exact(2)
const four = exact(4)
const tau = times(two, pi)
const integerMax = (a: bigint, b: bigint) => a > b ? a : b
const absolute = ({ lo, hi }: Box): Box => ({
  lo: integerMax(0n, integerMax(lo, -hi)), hi: integerMax(-lo, hi),
})
const containsZero = (box: Box) => box.lo <= 0n && box.hi >= 0n
const range = (lo: number, hi: number): Box => ({ lo: exact(lo).lo, hi: exact(hi).hi })

type Position = (fraction: Box) => Box

function positive(value: number): boolean {
  return Number.isFinite(value) && value > 0
}
// Numerical support limits, deliberately wider than cabinet-scale geometry.
// Reject unsupported requests before allocating or searching, rather than
// silently emitting nonfinite responses or blocking a UI update.
export function inRange(value: number, low: number, high: number) {
  return Number.isFinite(value) && value >= low && value <= high
}
export function validateAcoustic(
  frequency: number,
  soundSpeed: number,
  density: number,
) {
  if (
    !inRange(frequency, 1e-6, 1e6) ||
    !inRange(soundSpeed, 1, 1e6) ||
    !inRange(density, 1e-6, 1e6)
  )
    throw new RangeError(
      'Duct frequency or medium exceeds supported numerical range',
    )
}
export function junctionLength(lengths: readonly number[]) {
  return lengths.reduce((a, b) => a + b, 0)
}
function validateExtensions(path: DuctPath) {
  const junctions = path.junctionInertanceLengthsMeters
  if (
    junctions !== undefined &&
    (!Array.isArray(junctions) ||
      junctions.length > 128 ||
      ![...junctions].every((x) => inRange(x, -1000, 1000)))
  )
    throw new RangeError('Duct junction inertances must be finite and bounded')
  for (const factor of [path.inertanceFactor, path.complianceFactor])
    if (factor !== undefined && !inRange(factor, 1e-3, 1e3))
      throw new RangeError('Duct boundary-layer factors must be positive')
}
export function validateDuctPath(path: DuctPath) {
  validateExtensions(path)
  if (
    !Number.isInteger(path.count) ||
    path.count <= 0 ||
    path.count > 10000 ||
    !Array.isArray(path.sections) ||
    path.sections.length > 128 ||
    !path.sections.length ||
    !Number.isFinite(path.inletCorrectionMeters) ||
    path.inletCorrectionMeters < 0 ||
    !Number.isFinite(path.outletCorrectionMeters) ||
    path.outletCorrectionMeters < 0
  )
    throw new RangeError(
      'Invalid duct path or more than 128 sections / 10000 parallel ducts',
    )
  if (path.inletCorrectionMeters > 1000 || path.outletCorrectionMeters > 1000)
    throw new RangeError(
      'Duct end correction exceeds supported 1000 meter range',
    )
  for (const s of path.sections) {
    if (
      ![
        s.lengthMeters,
        s.inletAreaSquareMeters,
        s.outletAreaSquareMeters,
      ].every(positive) ||
      !['straight', 'conical', 'exponential'].includes(s.profile) ||
      (s.profile === 'straight' &&
        s.inletAreaSquareMeters !== s.outletAreaSquareMeters)
    )
      throw new RangeError('Invalid duct section')
    if (
      !inRange(s.lengthMeters, 1e-9, 1000) ||
      !inRange(s.inletAreaSquareMeters, 1e-10, 1e4) ||
      !inRange(s.outletAreaSquareMeters, 1e-10, 1e4) ||
      !inRange(s.outletAreaSquareMeters / s.inletAreaSquareMeters, 1e-8, 1e8)
    )
      throw new RangeError(
        'Duct section exceeds supported length, area, or taper numerical range',
      )
  }
  if (
    path.junctionInertanceLengthsMeters !== undefined &&
    !(rawEquivalentLength(path) > 0)
  )
    throw new RangeError(
      'Duct junction inertances leave a non-positive total effective inertance',
    )
}

export function rawEquivalentLength(path: DuctPath): number {
  const inlet = path.sections[0]!.inletAreaSquareMeters
  const mouth = path.sections.at(-1)!.outletAreaSquareMeters
  const sections = path.sections.reduce((sum, s) => {
    const ratio = s.outletAreaSquareMeters / s.inletAreaSquareMeters
    const factor =
      ratio === 1
        ? 1
        : s.profile === 'conical'
          ? 1 / Math.sqrt(ratio)
          : -Math.expm1(-Math.log(ratio)) / Math.log(ratio)
    return sum + ((s.lengthMeters * inlet) / s.inletAreaSquareMeters) * factor
  }, 0)
  const base =
    path.inletCorrectionMeters +
    (path.outletCorrectionMeters * inlet) / mouth +
    (path.inertanceFactor === undefined
      ? sections
      : sections * path.inertanceFactor)
  return path.junctionInertanceLengthsMeters === undefined
    ? base
    : base + junctionLength(path.junctionInertanceLengthsMeters)
}

export function validateDuctTuning(path: DuctPath, volume: number, speed: number) {
  validateDuctPath(path)
  if (!inRange(volume, 1e-12, 1e9) || !inRange(speed, 1, 1e6))
    throw new RangeError('Invalid cavity parameters')
}

/** C(t) = cos(sqrt(t)), S(t) = sinc(sqrt(t)) with their real hyperbolic
 * continuations for t < 0. The power series remains regular at cutoff.
 */
function wave(t: Box): [Box, Box] {
  if (absolute(t).hi > scale << 20n) throw new IntervalRangeError()
  let doublings = 0
  while (absolute(t).hi > scale) {
    t = quotient(t, four)
    doublings += 1
  }
  const negative = minus(zero, t)
  let c = one
  let s = one
  for (let n = 11; n > 0; n -= 1) {
    c = plus(one, quotient(times(negative, c), exact(2 * n * (2 * n - 1))))
    s = plus(one, quotient(times(negative, s), exact(2 * n * (2 * n + 1))))
  }
  // The absolute tail of each series on |t| ≤ 1 is at most 2/24!.
  const error = scale >> 70n
  c = plus(c, { lo: -error, hi: error })
  s = plus(s, { lo: -error, hi: error })
  for (let n = 0; n < doublings; n += 1) {
    s = times(s, c)
    c = minus(times(two, square(c)), one)
  }
  return [c, s]
}

/** Log by range reduction and the odd atanh series. */
export function ductLogRatio(value: Box): Box {
  const expt = value.lo.toString(2).length - scale.toString(2).length
  const reduced = quotient(value, exact(2 ** expt))
  const t = quotient(minus(reduced, one), plus(reduced, one))
  if (2n * absolute(t).hi > scale) throw new IntervalRangeError()
  const t2 = square(t)
  let poly = zero
  for (let k = 39; k >= 0; k -= 1)
    poly = plus(quotient(one, exact(2 * k + 1)), times(t2, poly))
  // On |t| ≤ 1/2 the remaining geometric tail is below 2^-79.
  const tail = scale >> 79n
  const log2 = range(0.6931471803, 0.6931471808)
  return plus(plus(times(times(two, t), poly), { lo: -tail, hi: tail }), times(exact(expt), log2))
}

type State = { pressurePerOmega: Box; flow: Box }

function sections(path: DuctPath, speed: number, density: number) {
  const rho = exact(density)
  const inertance = exact(path.inertanceFactor ?? 1)
  const waveNumberPerHz = quotient(times(tau,
    root(times(inertance, exact(path.complianceFactor ?? 1)))), exact(speed))
  const sectionDensity = times(rho, inertance)
  const count = exact(path.count)
  const mouth = exact(path.sections.at(-1)!.outletAreaSquareMeters)
  const outlet = quotient(times(rho, exact(path.outletCorrectionMeters)), mouth)
  const inlet = quotient(times(rho, (path.junctionInertanceLengthsMeters ?? [])
    .reduce((sum, length) => plus(sum, exact(length)), exact(path.inletCorrectionMeters))),
    exact(path.sections[0]!.inletAreaSquareMeters))

  const models = path.sections.map(({ inletAreaSquareMeters: si, outletAreaSquareMeters: so, lengthMeters, profile }) => {
    const inletArea = exact(si)
    const rIn = root(inletArea)
    const rOut = root(exact(so))
    const length = exact(lengthMeters)
    const exponential = profile === 'exponential'
    const radialSlope = quotient(minus(rOut, rIn), length)
    const growth = exponential ? quotient(ductLogRatio(quotient(rOut, rIn)), length) : zero
    const outletSlope = exponential ? growth : quotient(radialSlope, rOut)
    function position(k2: Box, fraction: Box, state: State) {
      const radius = exponential ? times(rIn, math.exp(times(times(growth, length), fraction))) :
        plus(rIn, times(minus(rOut, rIn), fraction))
      const ratio = quotient(rOut, radius)
      const inletSlope = exponential ? growth : quotient(radialSlope, radius)
      const q2 = minus(k2, square(growth))
      const remaining = times(length, minus(one, fraction))
      const [cosine, sinc] = wave(times(q2, square(remaining)))
      const sineOverQ = times(remaining, sinc)
      const area = times(radius, rOut)
      const a = times(ratio, minus(cosine, times(outletSlope, sineOverQ)))
      const b = times(quotient(sectionDensity, area), sineOverQ)
      const c = times(quotient(area, sectionDensity), plus(
        times(plus(q2, times(inletSlope, outletSlope)), sineOverQ),
        times(minus(outletSlope, inletSlope), cosine)))
      const d = quotient(plus(cosine, times(inletSlope, sineOverQ)), ratio)
      return {
        pressurePerOmega: plus(times(a, state.pressurePerOmega), times(b, state.flow)),
        flow: minus(times(d, state.flow), times(c, state.pressurePerOmega)),
        area: square(radius),
      }
    }
    return position
  }).reverse()

  return (frequencies: Box) => {
    const k2 = square(times(waveNumberPerHz, frequencies))
    let state: State = { pressurePerOmega: outlet, flow: one }
    const positions = models.map((position) => {
      const downstream = state
      state = position(k2, zero, state)
      return (fraction: Box) => {
        const value = position(k2, fraction, downstream)
        return quotient(absolute(value.flow), value.area)
      }
    })
    const numeratorPerOmega = plus(state.pressurePerOmega, times(inlet, state.flow))
    return { count, numeratorPerOmega, denominator: state.flow, positions }
  }
}

export function distributedPort(path: DuctPath, speed: number, rho: number) {
  const at = sections(path, speed, rho)
  // At zero frequency the flow is constant and pressure per angular
  // frequency is the integrated acoustic mass with the end corrections.
  const dc = at(zero)
  return {
    mass: quotient(dc.numeratorPerOmega, dc.count),
    response(frequency: Box) {
      const { numeratorPerOmega, denominator, count, positions } = at(frequency)
      return {
        throatFlow: times(count, denominator),
        reactance: times(times(tau, frequency), numeratorPerOmega),
        peak: () => spatialPeak(positions, scale >> 11n, 64, true).bound,
      }
    },
  }
}

export interface DuctBoundOptions {
  relativeTolerance?: number
  maxSplits?: number
}

interface FrequencySpan {
  minHz: number
  maxHz: number
}

interface FractionSpan {
  minFraction: number
  maxFraction: number
}

interface VelocityWitness {
  sectionIndex: number
  fraction: number
}

export interface DuctTuningCertificate {
  version: 1
  request: string
  lower: number
  upper: number
  earlierSpans: readonly FrequencySpan[]
  relativeTolerance: number
}

export interface DuctPeakVelocityCertificate {
  version: 1
  request: string
  lower: number
  upper: number
  /** Section index in the original path, from throat to mouth. */
  witness: VelocityWitness
  sectionSpans: readonly (readonly FractionSpan[])[]
  relativeTolerance: number
}

export type DuctBound<C = DuctTuningCertificate | DuctPeakVelocityCertificate> =
  | { status: 'resolved'; lower: number; upper: number; splits: number; certificate: C }
  | { status: 'unresolved'; reason: 'numeric-range' | 'pole' | 'bracket' | 'subdivision-budget' | 'certificate-rejected'; splits: number }

const tuningTolerance = 1e-5
const peakVelocityTolerance = 0.001

function settings(options: DuctBoundOptions, defaultTolerance: number) {
  if (options === null || typeof options !== 'object' || Array.isArray(options))
    throw new TypeError('Duct bound options must be an object')
  const { relativeTolerance = defaultTolerance, maxSplits = 4096 } = options
  if (!Number.isFinite(relativeTolerance) || relativeTolerance <= 0 || relativeTolerance >= 0.1 ||
      !Number.isSafeInteger(maxSplits) || maxSplits < 0 || maxSplits > 8192)
    throw new RangeError('Invalid duct bound tolerance or subdivision budget')
  return { relativeTolerance, maxSplits }
}

function requestKey(path: DuctPath, parameters: readonly number[], options: Required<DuctBoundOptions>): string {
  // Write the modeled fields in a fixed order, independent of the caller's
  // property order or unrelated metadata. Options use their effective values.
  const {
    complianceFactor, count, inertanceFactor, inletCorrectionMeters,
    junctionInertanceLengthsMeters, outletCorrectionMeters, sections,
  } = path
  const geometry = {
    complianceFactor, count, inertanceFactor, inletCorrectionMeters,
    junctionInertanceLengthsMeters, outletCorrectionMeters,
    sections: sections.map(({ inletAreaSquareMeters, lengthMeters, outletAreaSquareMeters, profile }) =>
      ({ inletAreaSquareMeters, lengthMeters, outletAreaSquareMeters, profile })),
  }
  return JSON.stringify([geometry, ...parameters, options.relativeTolerance, options.maxSplits])
}

function withinTolerance(lower: number, upper: number, relativeTolerance: number) {
  const low = exact(lower).lo
  return (exact(upper).hi - low) * scale <= low * exact(relativeTolerance).lo
}

function tuningResidual(path: DuctPath, volume: number, speed: number) {
  const at = sections(path, speed, 1)
  const compliance = quotient(exact(volume), square(exact(speed)))
  return (lo: number, hi: number) => {
    const frequency = range(lo, hi)
    const { count, numeratorPerOmega, denominator } = at(frequency)
    return { denominator, value: minus(times(times(square(times(tau, frequency)), compliance),
      numeratorPerOmega), times(count, denominator)) }
  }
}

/** Replay the bracket and the exclusion of all earlier roots. */
export function verifyDuctTuningCertificate(path: DuctPath, volumeM3: number, soundSpeed: number,
  certificate: Readonly<DuctTuningCertificate>, options: DuctBoundOptions = {}): boolean {
  try {
    validateDuctTuning(path, volumeM3, soundSpeed)
    const effective = settings(options, tuningTolerance)
    const { version, request, lower, upper, earlierSpans, relativeTolerance } = certificate
    if (version !== 1 || request !== requestKey(path, [volumeM3, soundSpeed], effective) ||
        relativeTolerance !== effective.relativeTolerance ||
        !positive(lower) || !(upper > lower) || !withinTolerance(lower, upper, relativeTolerance) ||
        !Array.isArray(earlierSpans) || earlierSpans.length === 0 || earlierSpans.length > effective.maxSplits + 1)
      return false
    const residual = tuningResidual(path, volumeM3, soundSpeed)
    if (residual(lower, lower).value.hi >= 0n || residual(upper, upper).value.lo < 0n ||
        containsZero(residual(lower, upper).denominator))
      return false
    let left = 0
    for (const { minHz, maxHz } of earlierSpans) {
      if (minHz !== left || !(maxHz > left) || maxHz > lower || residual(left, maxHz).value.hi >= 0n)
        return false
      left = maxHz
    }
    return left === lower
  } catch {
    return false
  }
}

export function tuningBounds(path: DuctPath, volume: number, speed: number, estimate: number,
  options: DuctBoundOptions): DuctBound<DuctTuningCertificate> {
  const effective = settings(options, tuningTolerance)
  const { relativeTolerance, maxSplits } = effective
  let splits = 0
  return enclosedOr((): DuctBound<DuctTuningCertificate> => {
    const residual = tuningResidual(path, volume, speed)
    const radius = estimate * relativeTolerance * 0.45
    const lower = estimate - radius
    const upper = estimate + radius
    if (!(lower > 0 && lower < upper) ||
        residual(lower, lower).value.hi >= 0n || residual(upper, upper).value.lo < 0n)
      return { status: 'unresolved', reason: 'bracket', splits }
    if (containsZero(residual(lower, upper).denominator))
      return { status: 'unresolved', reason: 'pole', splits }
    const earlierSpans: FrequencySpan[] = []
    const earlier: [number, number][] = [[0, lower]]
    while (earlier.length > 0) {
      const [lo, hi] = earlier.pop()!
      if (enclosedOr(() => residual(lo, hi).value.hi < 0n, false)) {
        earlierSpans.push({ minHz: lo, maxHz: hi })
        continue
      }
      const midpoint = lo + (hi - lo) / 2
      if (splits === maxSplits || midpoint <= lo || midpoint >= hi)
        return { status: 'unresolved', reason: 'subdivision-budget', splits }
      earlier.push([midpoint, hi], [lo, midpoint])
      splits += 1
    }
    const certificate: DuctTuningCertificate = {
      version: 1, request: requestKey(path, [volume, speed], effective),
      lower, upper, earlierSpans, relativeTolerance,
    }
    if (!verifyDuctTuningCertificate(path, volume, speed, certificate, options))
      return { status: 'unresolved', reason: 'certificate-rejected', splits }
    return { status: 'resolved', lower, upper, splits, certificate }
  }, { status: 'unresolved', reason: 'numeric-range', splits })
}

function normalizedPositions(path: DuctPath, frequency: number, speed: number, density: number) {
  const { denominator, positions, count } = sections(path, speed, density)(exact(frequency))
  if (containsZero(denominator)) return null
  const normalization = times(absolute(denominator), count)
  return positions.map((evaluate): Position => (fraction) => quotient(evaluate(fraction), normalization))
}

/** Replay a point witness and the upper envelope of every section. */
export function verifyDuctPeakVelocityCertificate(path: DuctPath, frequency: number, soundSpeed: number,
  density: number, certificate: Readonly<DuctPeakVelocityCertificate>, options: DuctBoundOptions = {}): boolean {
  try {
    validateDuctPath(path)
    validateAcoustic(frequency, soundSpeed, density)
    const effective = settings(options, peakVelocityTolerance)
    const { version, request, lower, upper, witness, sectionSpans, relativeTolerance } = certificate
    if (version !== 1 || request !== requestKey(path, [frequency, soundSpeed, density], effective) ||
        relativeTolerance !== effective.relativeTolerance ||
        !positive(lower) || !(upper >= lower) || !withinTolerance(lower, upper, relativeTolerance) ||
        !Array.isArray(sectionSpans) || sectionSpans.length !== path.sections.length)
      return false
    const { sectionIndex, fraction } = witness
    if (!Number.isInteger(sectionIndex) || sectionIndex < 0 || sectionIndex >= path.sections.length ||
        !inRange(fraction, 0, 1))
      return false
    const positions = normalizedPositions(path, frequency, soundSpeed, density)
    if (positions === null || positions.at(-1 - sectionIndex)!(exact(fraction)).lo < exact(lower).hi)
      return false
    const ceiling = exact(upper).lo
    let remaining = path.sections.length + effective.maxSplits
    for (let i = 0; i < sectionSpans.length; i += 1) {
      const spans = sectionSpans[i]!
      if (!Array.isArray(spans) || spans.length > remaining) return false
      remaining -= spans.length
      const evaluate = positions.at(-1 - i)!
      let left = 0
      for (const { minFraction, maxFraction } of spans) {
        if (minFraction !== left || !(maxFraction > left) || maxFraction > 1 ||
            evaluate(range(left, maxFraction)).hi > ceiling)
          return false
        left = maxFraction
      }
      if (left !== 1) return false
    }
    return true
  } catch {
    return false
  }
}

export function peakVelocityBounds(path: DuctPath, frequency: number, speed: number, rho: number,
  options: DuctBoundOptions): DuctBound<DuctPeakVelocityCertificate> {
  const effective = settings(options, peakVelocityTolerance)
  const { relativeTolerance, maxSplits } = effective
  return enclosedOr((): DuctBound<DuctPeakVelocityCertificate> => {
    const positions = normalizedPositions(path, frequency, speed, rho)
    if (positions === null) return { status: 'unresolved', reason: 'pole', splits: 0 }
    const { bound, splits, witness, pending } = spatialPeak(positions, exact(relativeTolerance).lo, maxSplits, false)
    const { lo: lower, hi: upper } = outwardBinary64(bound)
    if (!withinTolerance(lower, upper, relativeTolerance))
      return { status: 'unresolved', reason: 'subdivision-budget', splits }
    const sectionSpans = path.sections.map((): FractionSpan[] => [])
    for (const { index, lo, hi } of pending)
      sectionSpans[positions.length - 1 - index]!.push({ minFraction: lo, maxFraction: hi })
    const certificate: DuctPeakVelocityCertificate = {
      version: 1, request: requestKey(path, [frequency, speed, rho], effective),
      lower, upper, relativeTolerance, sectionSpans,
      witness: { sectionIndex: positions.length - 1 - witness.sectionIndex, fraction: witness.fraction },
    }
    if (!verifyDuctPeakVelocityCertificate(path, frequency, speed, rho, certificate, options))
      return { status: 'unresolved', reason: 'certificate-rejected', splits }
    return { status: 'resolved', lower, upper, splits, certificate }
  }, { status: 'unresolved', reason: 'numeric-range', splits: 0 })
}

/** Each position box covers the whole frequency span. The lower bound
 * uses a single witness position whose bound holds at every frequency.
 */
function spatialPeak(positions: readonly Position[], tolerance: bigint, maxSplits: number, joint: boolean) {
  let floor = positions[0]!(one).lo
  let witness = { sectionIndex: 0, fraction: 1 }
  const bound = (index: number, lo: number, hi: number) => {
    const evaluate = positions[index]!
    const middle = lo + (hi - lo) / 2
    const sample = evaluate(exact(middle))
    if (sample.lo > floor) {
      floor = sample.lo
      witness = { sectionIndex: index, fraction: middle }
    }
    return { index, lo, hi, middle, sample, ceiling: evaluate(range(lo, hi)).hi }
  }
  const pending = positions.map((_, index) => bound(index, 0, 1))
  let splits = 0
  for (;;) {
    const worst = pending.reduce((a, b) => a.ceiling >= b.ceiling ? a : b)
    // When frequency variation dominates, the outer search should refine it.
    const variation = joint ? worst.sample.hi - worst.sample.lo : 0n
    if ((worst.ceiling - floor - variation) * scale <= floor * tolerance || splits === maxSplits)
      return { bound: { lo: floor, hi: worst.ceiling }, splits, witness, pending }
    pending.splice(pending.indexOf(worst), 1, bound(worst.index, worst.lo, worst.middle),
      bound(worst.index, worst.middle, worst.hi))
    splits += 1
  }
}
