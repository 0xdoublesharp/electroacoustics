import { binary64Dyad, roundRatio } from './binary64.js'

/** RMS phasors, exp(j omega t). */
export interface Complex {
  re: number
  im: number
}
export const c = (re: number, im = 0): Complex => ({ re, im })
export const add = (a: Complex, b: Complex): Complex =>
  c(a.re + b.re, a.im + b.im)
export const sub = (a: Complex, b: Complex): Complex =>
  c(a.re - b.re, a.im - b.im)
export const mul = (a: Complex, b: Complex): Complex =>
  c(a.re * b.re - a.im * b.im, a.im * b.re + a.re * b.im)
/** Correctly rounded quotient of finite binary64 phasors. */
export function div(a: Complex, b: Complex): Complex {
  if (![a.re, a.im, b.re, b.im].every(Number.isFinite))
    throw new RangeError('Complex division exceeds the supported numeric range')
  const integer = (value: number) => {
    const { significand, exponent } = binary64Dyad(value)
    return significand << BigInt(exponent + 1074)
  }
  const [ar, ai, br, bi] = [integer(a.re), integer(a.im), integer(b.re), integer(b.im)]
  const denominator = br * br + bi * bi
  if (denominator === 0n) throw new RangeError('Complex division exceeds the supported numeric range')
  // The common factor 2⁻²¹⁴⁸ cancels before either component is rounded.
  const re = roundRatio(ar * br + ai * bi, denominator)
  const im = roundRatio(ai * br - ar * bi, denominator)
  if (!Number.isFinite(re) || !Number.isFinite(im))
    throw new RangeError('Complex division exceeds the supported numeric range')
  return c(re, im)
}
export const reciprocal = (a: Complex): Complex => div(c(1), a)
export const magnitude = (a: Complex): number => Math.hypot(a.re, a.im)
