import { describe, expect, it } from 'vitest'
import {
  composeFilters,
  lr24AttenuationDb,
  lr24Transfer,
  bw24Transfer,
  bw24AttenuationDb,
} from './filters'

describe('BW24 high-pass', () => {
  it('matches fourth-order Butterworth magnitude and phase', () => {
    for (const ratio of [0.01, 0.5, 1, 2, 100]) {
      const transfer = bw24Transfer(100 * ratio, 100)
      const magnitude = 1 / Math.sqrt(1 + ratio ** -8)
      expect(Math.hypot(transfer.re, transfer.im)).toBeCloseTo(magnitude, 12)
      expect(bw24AttenuationDb(100 * ratio, 100)).toBeCloseTo(
        20 * Math.log10(magnitude),
        10,
      )
    }
    const cutoff = bw24Transfer(100, 100)
    expect(cutoff.re).toBeCloseTo(-Math.SQRT1_2, 12)
    expect(cutoff.im).toBeCloseTo(0, 12)
    // Independent fourth-order denominator: s^4 + a*s^3 + b*s^2 + a*s + 1.
    const a = Math.sqrt(4 + 2 * Math.SQRT2)
    const b = 2 + Math.SQRT2
    const r = 0.5
    const re = r ** 4 - b * r ** 2 + 1
    const im = a * (r - r ** 3)
    const below = bw24Transfer(50, 100)
    expect(below.re).toBeCloseTo((r ** 4 * re) / (re ** 2 + im ** 2), 12)
    expect(below.im).toBeCloseTo((-(r ** 4) * im) / (re ** 2 + im ** 2), 12)
  })

  it('selects BW24 in a chain while retaining an LR24 low-pass', () => {
    const transfer = composeFilters(100, {
      highpassHz: 100,
      highpassType: 'BW24',
      lowpassHz: 100,
    })
    expect(transfer.re).toBeCloseTo(Math.SQRT1_2 / 2, 12)
    expect(transfer.im).toBeCloseTo(0, 12)
  })

  it('validates input and keeps extreme finite ratios stable', () => {
    for (const invalid of [0, -1, NaN, Infinity]) {
      expect(() => bw24Transfer(invalid, 20)).toThrow()
      expect(() => bw24Transfer(20, invalid)).toThrow()
      expect(() => bw24AttenuationDb(invalid, 20)).toThrow()
      expect(() => bw24AttenuationDb(20, invalid)).toThrow()
    }
    expect(() =>
      composeFilters(20, { highpassHz: 20, highpassType: 'junk' as 'BW24' }),
    ).toThrow(/type/i)
    expect(bw24Transfer(Number.MIN_VALUE, Number.MAX_VALUE)).toEqual({
      re: 0,
      im: 0,
    })
    expect(bw24Transfer(Number.MAX_VALUE, Number.MIN_VALUE)).toEqual({
      re: 1,
      im: 0,
    })
    expect(
      Number.isFinite(bw24AttenuationDb(Number.MIN_VALUE, Number.MAX_VALUE)),
    ).toBe(true)
  })
})

describe('LR24 filters', () => {
  it('rejects an invalid filter kind consistently in transfer and attenuation APIs', () => {
    expect(() => lr24Transfer(20, 10, 'bandpass' as 'lowpass')).toThrow(/kind/i)
    expect(() => lr24AttenuationDb(20, 10, 'bandpass' as 'lowpass')).toThrow(
      /kind/i,
    )
  })

  it('matches independent analytic magnitudes and phases with exp(j omega t)', () => {
    for (const kind of ['lowpass', 'highpass'] as const) {
      const cutoff = lr24Transfer(100, 100, kind)
      expect(cutoff.re).toBeCloseTo(-0.5, 12)
      expect(cutoff.im).toBeCloseTo(0, 12)
    }

    const low = lr24Transfer(50, 100, 'lowpass')
    const high = lr24Transfer(50, 100, 'highpass')
    expect(Math.hypot(low.re, low.im)).toBeCloseTo(16 / 17, 12)
    const expectedPhase = -2 * Math.atan((Math.SQRT2 * 0.5) / (1 - 0.5 ** 2))
    expect(Math.atan2(low.im, low.re)).toBeCloseTo(expectedPhase, 12)
    expect(Math.hypot(high.re, high.im)).toBeCloseTo(1 / 17, 12)
    expect(Math.atan2(high.im, high.re)).toBeCloseTo(expectedPhase, 12)
    expect(lr24AttenuationDb(50, 100, 'highpass')).toBeCloseTo(
      20 * Math.log10(1 / 17),
      12,
    )
  })

  it('composes HPF, LPF, gain, and delay as complex voltage transfer', () => {
    const transfer = composeFilters(100, {
      highpassHz: 100,
      lowpassHz: 100,
      gainDb: 6.020599913279624,
      delaySeconds: 0.0025,
    })
    expect(transfer.re).toBeCloseTo(0, 12)
    expect(transfer.im).toBeCloseTo(-0.5, 12)
  })

  it('rejects invalid frequencies, cutoffs, gain, and delay', () => {
    expect(() => lr24Transfer(0, 20, 'highpass')).toThrow()
    expect(() => lr24Transfer(20, Infinity, 'lowpass')).toThrow()
    expect(() => composeFilters(20, { highpassHz: -1 })).toThrow()
    expect(() => composeFilters(20, { gainDb: NaN })).toThrow()
    expect(() => composeFilters(20, { delaySeconds: -1 })).toThrow()
    expect(() => lr24Transfer(20, 10, 'bandpass' as 'lowpass')).toThrow()
  })

  it('keeps extreme finite ratios inside the supported numeric range', () => {
    const low = lr24Transfer(Number.MAX_VALUE, Number.MIN_VALUE, 'lowpass')
    const high = lr24Transfer(Number.MAX_VALUE, Number.MIN_VALUE, 'highpass')
    expect(low).toEqual({ re: 0, im: 0 })
    expect(high.re).toBeCloseTo(1)
    expect(high.im).toBeCloseTo(0)
  })
})
