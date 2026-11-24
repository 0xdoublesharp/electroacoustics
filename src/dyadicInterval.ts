import { binary64Dyad, roundRatio } from './binary64.js'
import { binary64Intervals, IntervalRangeError, type IntervalMath } from './interval.js'

/** An enclosure whose endpoints are exact integers divided by 2^160. */
export interface DyadicInterval {
  lo: bigint
  hi: bigint
}

const precision = 160
const scale = 1n << BigInt(precision)
const zero = { lo: 0n, hi: 0n }
const one = { lo: scale, hi: scale }

const min = (a: bigint, b: bigint) => a <= b ? a : b
const max = (a: bigint, b: bigint) => a >= b ? a : b

function floor(numerator: bigint, denominator: bigint): bigint {
  const truncated = numerator / denominator
  const remainder = numerator % denominator
  return remainder !== 0n && (remainder < 0n) !== (denominator < 0n)
    ? truncated - 1n : truncated
}

const ceil = (numerator: bigint, denominator: bigint) => -floor(-numerator, denominator)

function exact(value: number): DyadicInterval {
  if (!Number.isFinite(value)) throw new IntervalRangeError()
  const { significand, exponent } = binary64Dyad(value)
  const shift = BigInt(-exponent - precision)
  const lower = significand >> shift
  // BigInt right shift rounds toward minus infinity, even for negative inputs.
  return { lo: lower, hi: -(-significand >> shift) }
}

const plus = (a: DyadicInterval, b: DyadicInterval): DyadicInterval =>
  ({ lo: a.lo + b.lo, hi: a.hi + b.hi })
const minus = (a: DyadicInterval, b: DyadicInterval): DyadicInterval =>
  ({ lo: a.lo - b.hi, hi: a.hi - b.lo })

function times(a: DyadicInterval, b: DyadicInterval): DyadicInterval {
  const p = a.lo * b.lo
  const q = a.lo * b.hi
  const r = a.hi * b.lo
  const s = a.hi * b.hi
  return { lo: floor(min(min(p, q), min(r, s)), scale),
    hi: ceil(max(max(p, q), max(r, s)), scale) }
}

function quotient(a: DyadicInterval, b: DyadicInterval): DyadicInterval {
  if (b.lo <= 0n && b.hi >= 0n) throw new IntervalRangeError()
  const reciprocal = { lo: floor(scale * scale, b.hi), hi: ceil(scale * scale, b.lo) }
  return times(a, reciprocal)
}

function square(a: DyadicInterval): DyadicInterval {
  const near = max(0n, max(a.lo, -a.hi))
  const far = max(-a.lo, a.hi)
  return { lo: floor(near * near, scale), hi: ceil(far * far, scale) }
}

function integerSqrt(value: bigint): bigint {
  if (value === 0n) return value
  let upper = 1n << BigInt(Math.ceil(value.toString(2).length / 2))
  for (;;) {
    const candidate = (upper + value / upper) >> 1n
    if (candidate >= upper) return upper
    upper = candidate
  }
}

function root(a: DyadicInterval): DyadicInterval {
  const lo = integerSqrt(max(0n, a.lo) * scale)
  const highSquare = a.hi * scale
  const hi = integerSqrt(highSquare)
  return { lo, hi: hi * hi === highSquare ? hi : hi + 1n }
}

// The exponential and trigonometric Taylor remainders below are less than
// 2^-55. The bound covers the exact real function before dyadic rounding.
const remainder = 1n << BigInt(precision - 55)
const taylorError = { lo: -remainder, hi: remainder }
const pi = { lo: exact(3.141592653589793).lo, hi: exact(3.141592653589794).hi }
const ln10 = { lo: exact(2.3025850925).lo, hi: exact(2.3025850935).hi }

function exp(a: DyadicInterval): DyadicInterval {
  let squarings = 0
  let argument = a
  if (max(-a.lo, a.hi) > 1024n * scale) throw new IntervalRangeError()
  while (max(-argument.lo, argument.hi) > scale) {
    argument = quotient(argument, exact(2))
    squarings += 1
  }
  let sum = one
  for (let n = 18; n > 0; n -= 1)
    sum = plus(one, quotient(times(argument, sum), exact(n)))
  sum = plus(sum, taylorError)
  for (let n = 0; n < squarings; n += 1) sum = square(sum)
  return sum
}

function firstQuadrant(angle: DyadicInterval): [DyadicInterval, DyadicInterval] {
  function at(x: bigint, degree: 0 | 1) {
    const argument = { lo: x, hi: x }
    const negativeSquare = minus(zero, square(argument))
    let polynomial = one
    for (let n = 11; n > 0; n -= 1) {
      const exponent = 2 * n + degree
      polynomial = plus(one, quotient(times(negativeSquare, polynomial),
        exact(exponent * (exponent - 1))))
    }
    return plus(times(polynomial, degree === 0 ? one : argument), taylorError)
  }
  const left = max(0n, angle.lo)
  const right = min(ceil(pi.hi, 2n), angle.hi)
  return [
    { lo: max(0n, at(left, 1).lo), hi: 2n * right >= pi.lo ? scale : min(scale, at(right, 1).hi) },
    { lo: max(0n, at(right, 0).lo), hi: min(scale, at(left, 0).hi) },
  ]
}

export const dyadicIntervals: IntervalMath<DyadicInterval> = {
  exact, zero, one, pi, ln10, plus, minus, times, quotient, square, root, exp, firstQuadrant,
  maximum: (values) => values.reduce((a, b) => ({ lo: max(a.lo, b.lo), hi: max(a.hi, b.hi) })),
}

/** Convert exact endpoints to binary64 and widen by one representable step. */
export function outwardBinary64(bound: DyadicInterval) {
  const math = binary64Intervals
  return {
    lo: math.plus(math.exact(roundRatio(bound.lo, scale)), math.zero).lo,
    hi: math.plus(math.exact(roundRatio(bound.hi, scale)), math.zero).hi,
  }
}

/** Return a binary64 value whose error is no more than
 * 2^-40 × max(1, |x|) for every exact x in the enclosure.
 */
export function verifiedRepresentative(a: DyadicInterval): number {
  const candidate = roundRatio(a.lo + a.hi, 2n * scale)
  const rounded = exact(candidate)
  const error = max(rounded.hi - a.lo, a.hi - rounded.lo)
  const reference = max(scale, max(a.lo, -a.hi))
  if (error > reference >> 40n) throw new IntervalRangeError()
  return candidate
}
