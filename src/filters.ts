import { centeredBiquad } from './biquadArithmetic.js'
import { mul, type Complex } from './complex.js'
import { dyadicIntervals, verifiedRepresentative } from './dyadicInterval.js'
import { enclosedOr } from './interval.js'

export type FilterTransfer = Complex

export type Lr24Kind = 'highpass' | 'lowpass'
export type HighPassFilterType = 'LR24' | 'BW24'

export interface BiquadCoefficients {
  kind: 'biquad'
  b0: number
  b1: number
  b2: number
  a1: number
  a2: number
}

export type ParametricEq = { frequencyHz: number; gainDb: number } & (
  | { kind: 'peaking'; q: number }
  | { kind: 'low-shelf' | 'high-shelf'; slope: number }
)

export interface DigitalFilterChain {
  sampleRateHz: number
  stages: readonly (ParametricEq | BiquadCoefficients)[]
}

export interface FilterChain {
  highpassHz?: number
  /** Omitted type preserves the existing Linkwitz-Riley high-pass. */
  highpassType?: HighPassFilterType
  lowpassHz?: number
  gainDb?: number
  /** Pure time delay. It changes phase but not magnitude-based limits. */
  delaySeconds?: number
  digital?: Readonly<DigitalFilterChain>
}

const positive = (value: number) => Number.isFinite(value) && value > 0

function validateFrequency(frequency: number, label: string): void {
  if (!positive(frequency))
    throw new RangeError(`${label} must be finite and greater than zero.`)
}

function validateBiquad({ b0, b1, b2, a1, a2 }: BiquadCoefficients): void {
  if (![b0, b1, b2, a1, a2].every(Number.isFinite) || Math.abs(a2) >= 1 ||
      1 + a2 <= Math.abs(a1))
    throw new RangeError('Biquad coefficients must be finite with poles strictly inside the unit circle')
}

/** Normalized, bilinear-transform EQ coefficients. See the W3C Audio EQ Cookbook. */
export function designBiquad(stage: Readonly<ParametricEq>, sampleRateHz: number): BiquadCoefficients {
  validateFrequency(sampleRateHz, 'Sample rate')
  validateFrequency(stage.frequencyHz, 'EQ frequency')
  if (stage.frequencyHz >= sampleRateHz / 2 || !Number.isFinite(stage.gainDb))
    throw new RangeError('EQ requires a finite gain and frequency below Nyquist')

  const amplitude = 10 ** (stage.gainDb / 40)
  const w = 2 * Math.PI * (stage.frequencyHz / sampleRateHz)
  const cos = Math.cos(w)
  const sin = Math.sin(w)
  let b0: number, b1: number, b2: number, a0: number, a1: number, a2: number
  if (stage.kind === 'peaking') {
    validateFrequency(stage.q, 'Peaking Q')
    const alpha = sin / (2 * stage.q)
    b0 = 1 + alpha * amplitude
    b1 = -2 * cos
    b2 = 1 - alpha * amplitude
    a0 = 1 + alpha / amplitude
    a1 = b1
    a2 = 1 - alpha / amplitude
  } else {
    if ((stage.kind !== 'low-shelf' && stage.kind !== 'high-shelf') ||
        !positive(stage.slope) || stage.slope > 1)
      throw new RangeError('Shelf slope must be greater than zero and at most one')
    const sum = amplitude + 1
    const difference = amplitude - 1
    const edge = sin * Math.sqrt((amplitude ** 2 + 1) * (1 / stage.slope - 1) + 2 * amplitude)
    const sign = stage.kind === 'low-shelf' ? 1 : -1
    b0 = amplitude * (sum - sign * difference * cos + edge)
    b1 = 2 * sign * amplitude * (difference - sign * sum * cos)
    b2 = amplitude * (sum - sign * difference * cos - edge)
    a0 = sum + sign * difference * cos + edge
    a1 = -2 * sign * (difference + sign * sum * cos)
    a2 = sum + sign * difference * cos - edge
  }
  const result: BiquadCoefficients = { kind: 'biquad', b0: b0 / a0, b1: b1 / a0,
    b2: b2 / a0, a1: a1 / a0, a2: a2 / a0 }
  validateBiquad(result)
  return result
}

/** Evaluate the normalized unit-circle transfer with a verified per-component error.
 * Each error is at most 2^-40 × max(1, |exact component|).
 */
export function biquadTransfer(frequencyHz: number, sampleRateHz: number, coefficients: Readonly<BiquadCoefficients>): Complex {
  validateFrequency(sampleRateHz, 'Sample rate')
  if (!Number.isFinite(frequencyHz) || frequencyHz < 0 || 2 * frequencyHz > sampleRateHz)
    throw new RangeError('Biquad frequency must be between DC and Nyquist')
  validateBiquad(coefficients)
  const result = enclosedOr(() => {
    const math = dyadicIntervals
    const { exact, minus, pi, plus, quotient, square, times, zero } = math
    const two = exact(2)
    let versine = zero
    let sine = zero
    if (2 * frequencyHz === sampleRateHz) versine = two
    else if (frequencyHz > 0) {
      const [sinHalf, cosHalf] = math.firstQuadrant(times(pi, quotient(exact(frequencyHz), exact(sampleRateHz))))
      versine = times(two, square(sinHalf))
      sine = times(two, times(sinHalf, cosHalf))
    }
    const { numReal, numImag, denReal, denImag } = centeredBiquad(coefficients, versine, sine, math)
    const norm = plus(square(denReal), square(denImag))
    const re = quotient(plus(times(numReal, denReal), times(numImag, denImag)), norm)
    const im = quotient(minus(times(numImag, denReal), times(numReal, denImag)), norm)
    return { re: verifiedRepresentative(re), im: verifiedRepresentative(im) }
  }, null)
  if (result === null) throw new RangeError('Biquad response exceeds the supported numeric range')
  return result
}

/** Fourth-order Linkwitz-Riley voltage transfer using exp(j omega t). */
export function lr24Transfer(
  frequency: number,
  cutoff: number,
  kind: Lr24Kind,
): FilterTransfer {
  validateFrequency(frequency, 'Filter frequency')
  validateFrequency(cutoff, 'Filter cutoff')
  if (kind !== 'highpass' && kind !== 'lowpass')
    throw new RangeError('Filter kind must be highpass or lowpass.')
  const aboveCutoff = frequency >= cutoff
  const boundedRatio = aboveCutoff ? cutoff / frequency : frequency / cutoff
  const fourthPower = boundedRatio ** 4
  const magnitude =
    (kind === 'lowpass') === aboveCutoff
      ? fourthPower / (1 + fourthPower)
      : 1 / (1 + fourthPower)
  const phaseMagnitude =
    2 * Math.atan2(Math.SQRT2 * boundedRatio, 1 - boundedRatio * boundedRatio)
  const phase = aboveCutoff ? phaseMagnitude : -phaseMagnitude
  return {
    re: magnitude * Math.cos(phase),
    im: magnitude * Math.sin(phase),
  }
}

/** Stable LR24 magnitude in dB, including extreme frequency ratios. */
export function lr24AttenuationDb(
  frequency: number,
  cutoff: number,
  kind: Lr24Kind,
): number {
  validateFrequency(frequency, 'Filter frequency')
  validateFrequency(cutoff, 'Filter cutoff')
  if (kind !== 'highpass' && kind !== 'lowpass')
    throw new RangeError('Filter kind must be highpass or lowpass.')
  const logRatio =
    4 *
    (kind === 'lowpass'
      ? Math.log(frequency) - Math.log(cutoff)
      : Math.log(cutoff) - Math.log(frequency))
  return (
    (-20 / Math.LN10) *
    (Math.max(0, logRatio) + Math.log1p(Math.exp(-Math.abs(logRatio))))
  )
}

/** Fourth-order Butterworth high-pass voltage transfer using exp(j omega t). */
export function bw24Transfer(
  frequency: number,
  cutoff: number,
): FilterTransfer {
  validateFrequency(frequency, 'Filter frequency')
  validateFrequency(cutoff, 'Filter cutoff')
  // Evaluate the normalized polynomial on a ratio <= 1 to avoid overflow.
  const aboveCutoff = frequency >= cutoff
  const ratio = aboveCutoff ? cutoff / frequency : frequency / cutoff
  const numerator = aboveCutoff ? 1 : ratio ** 4
  if (numerator === 0) return { re: 0, im: 0 }
  const a = Math.sqrt(4 + 2 * Math.SQRT2)
  const b = 2 + Math.SQRT2
  const re = 1 - b * ratio ** 2 + ratio ** 4
  const im = (aboveCutoff ? -1 : 1) * a * (ratio - ratio ** 3)
  const denominator = re ** 2 + im ** 2
  return {
    re: (numerator * re) / denominator,
    im: (-numerator * im) / denominator,
  }
}

/** Stable BW24 magnitude in dB, including extreme frequency ratios. */
export function bw24AttenuationDb(frequency: number, cutoff: number): number {
  validateFrequency(frequency, 'Filter frequency')
  validateFrequency(cutoff, 'Filter cutoff')
  const logRatio = 8 * (Math.log(cutoff) - Math.log(frequency))
  return (
    (-10 / Math.LN10) *
    (Math.max(0, logRatio) + Math.log1p(Math.exp(-Math.abs(logRatio))))
  )
}

export function composeFilters(
  frequency: number,
  chain: Readonly<FilterChain> = {},
): FilterTransfer {
  validateFrequency(frequency, 'Filter frequency')
  if (
    chain.highpassType !== undefined &&
    chain.highpassType !== 'LR24' &&
    chain.highpassType !== 'BW24'
  )
    throw new RangeError('High-pass filter type must be LR24 or BW24.')
  const gainDb = chain.gainDb ?? 0
  const delaySeconds = chain.delaySeconds ?? 0
  if (!Number.isFinite(gainDb))
    throw new RangeError('Filter gain must be finite.')
  if (!Number.isFinite(delaySeconds) || delaySeconds < 0)
    throw new RangeError('Filter delay must be finite and nonnegative.')

  let transfer = { re: 1, im: 0 }
  for (const [cutoff, kind] of [
    [chain.highpassHz, 'highpass'],
    [chain.lowpassHz, 'lowpass'],
  ] as const) {
    if (cutoff === undefined) continue
    const stage =
      kind === 'highpass' && chain.highpassType === 'BW24'
        ? bw24Transfer(frequency, cutoff)
        : lr24Transfer(frequency, cutoff, kind)
    transfer = {
      re: transfer.re * stage.re - transfer.im * stage.im,
      im: transfer.re * stage.im + transfer.im * stage.re,
    }
  }
  if (chain.digital) {
    const { sampleRateHz, stages } = chain.digital
    validateFrequency(sampleRateHz, 'Sample rate')
    if (frequency > sampleRateHz / 2) throw new RangeError('Digital filter frequency exceeds Nyquist')
    for (const stage of stages) {
      const coefficients = stage.kind === 'biquad' ? stage : designBiquad(stage, sampleRateHz)
      transfer = mul(transfer, biquadTransfer(frequency, sampleRateHz, coefficients))
    }
  }
  const gain = 10 ** (gainDb / 20)
  const phase = -2 * Math.PI * frequency * delaySeconds
  const delayed = { re: gain * Math.cos(phase), im: gain * Math.sin(phase) }
  const result = {
    re: transfer.re * delayed.re - transfer.im * delayed.im,
    im: transfer.re * delayed.im + transfer.im * delayed.re,
  }
  if (!Number.isFinite(result.re) || !Number.isFinite(result.im))
    throw new RangeError('Filter settings exceed the supported numeric range.')
  return result
}
