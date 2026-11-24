import { centeredBiquad } from './biquadArithmetic.js'
import { biquadTransfer, designBiquad, type FilterChain } from './filters.js'
import type { IntervalMath } from './interval.js'

export function bandFilter<T>(filter: Readonly<FilterChain> = {}, maxHz: number, math: IntervalMath<T>) {
  const { exact, exp, firstQuadrant, ln10, one, pi, plus, quotient, root, square, times } = math
  const two = exact(2)
  const fourth = (x: T) => square(square(x))
  const { highpassHz, highpassType, lowpassHz, gainDb = 0, delaySeconds = 0, digital } = filter
  if ((highpassType !== undefined && highpassType !== 'BW24' && highpassType !== 'LR24') ||
      !Number.isFinite(gainDb) || !Number.isFinite(delaySeconds) || delaySeconds < 0 ||
      [highpassHz, lowpassHz].some((cutoff) =>
        cutoff !== undefined && (!Number.isFinite(cutoff) || cutoff <= 0)))
    throw new RangeError('Invalid band filter settings')
  const stages = digital?.stages.map((stage) => {
    if (stage.kind !== 'biquad') return designBiquad(stage, digital.sampleRateHz)
    biquadTransfer(0, digital.sampleRateHz, stage)
    return stage
  }) ?? []
  const sampleRate = digital?.sampleRateHz
  if (sampleRate !== undefined &&
      (!Number.isFinite(sampleRate) || sampleRate <= 0 || 2 * maxHz > sampleRate))
    throw new RangeError('Band filter requires positive sample rate and frequencies at or below Nyquist')

  if (stages.some(({ b0, b1, b2 }) => b0 === 0 && b1 === 0 && b2 === 0)) return null
  const fixedGain = gainDb === 0 ? one : exp(times(quotient(exact(gainDb), exact(20)), ln10))
  return (frequency: T): T => {
    let gain = fixedGain
    if (highpassHz !== undefined) {
      const ratio4 = fourth(quotient(exact(highpassHz), frequency))
      gain = times(gain, highpassType === 'BW24'
        ? quotient(one, root(plus(one, square(ratio4))))
        : quotient(one, plus(one, ratio4)))
    }
    if (lowpassHz !== undefined)
      gain = times(gain, quotient(one, plus(one, fourth(quotient(frequency, exact(lowpassHz))))))
    if (sampleRate !== undefined) {
      const [sinHalf, cosHalf] = firstQuadrant(times(pi, quotient(frequency, exact(sampleRate))))
      const versine = times(two, square(sinHalf))
      const sine = times(two, times(sinHalf, cosHalf))
      for (const stage of stages) {
        const { numReal, numImag, denReal, denImag } = centeredBiquad(stage, versine, sine, math)
        const numerator = root(plus(square(numReal), square(numImag)))
        const denominator = root(plus(square(denReal), square(denImag)))
        gain = times(gain, quotient(numerator, denominator))
      }
    }
    return gain
  }
}
