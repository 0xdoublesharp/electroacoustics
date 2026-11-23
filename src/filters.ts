import type { Complex } from './complex.js'

export type FilterTransfer = Complex

export type Lr24Kind = 'highpass' | 'lowpass'
export type HighPassFilterType = 'LR24' | 'BW24'

export interface FilterChain {
  highpassHz?: number
  /** Omitted type preserves the existing Linkwitz-Riley high-pass. */
  highpassType?: HighPassFilterType
  lowpassHz?: number
  gainDb?: number
  /** Pure time delay. It changes phase but not magnitude-based limits. */
  delaySeconds?: number
}

const positive = (value: number) => Number.isFinite(value) && value > 0

function validateFrequency(frequency: number, label: string): void {
  if (!positive(frequency))
    throw new RangeError(`${label} must be finite and greater than zero.`)
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
