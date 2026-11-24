// Closed binary64 enclosures for exact real operations. An intermediate outside
// the finite range or a divisor containing zero requires subdivision.
export interface Interval {
  lo: number
  hi: number
}

export class IntervalRangeError extends Error {}

export interface IntervalMath<T> {
  exact(value: number): T
  zero: T
  one: T
  pi: T
  ln10: T
  plus(a: T, b: T): T
  minus(a: T, b: T): T
  times(a: T, b: T): T
  quotient(a: T, b: T): T
  square(a: T): T
  root(a: T): T
  exp(a: T): T
  firstQuadrant(a: T): [T, T]
  maximum(values: readonly T[]): T
}

export function enclosedOr<T>(evaluate: () => T, fallback: T): T {
  try {
    return evaluate()
  } catch (error) {
    if (error instanceof IntervalRangeError) return fallback
    throw error
  }
}

const bits = new DataView(new ArrayBuffer(8))

function up(value: number): number {
  if (!Number.isFinite(value)) throw new IntervalRangeError()
  if (value === 0) return Number.MIN_VALUE
  bits.setFloat64(0, value)
  bits.setBigUint64(0, bits.getBigUint64(0) + (value < 0 ? -1n : 1n))
  const next = bits.getFloat64(0)
  if (!Number.isFinite(next)) throw new IntervalRangeError()
  return next
}

const down = (value: number) => -up(-value)
export const exact = (value: number): Interval => ({ lo: value, hi: value })
export const zero = exact(0)
export const one = exact(1)
export const pi: Interval = { lo: 3.141592653589793, hi: 3.141592653589794 }
export const ln10: Interval = { lo: 2.3025850925, hi: 2.3025850935 }

export const plus = (a: Interval, b: Interval): Interval =>
  ({ lo: down(a.lo + b.lo), hi: up(a.hi + b.hi) })
export const minus = (a: Interval, b: Interval): Interval =>
  ({ lo: down(a.lo - b.hi), hi: up(a.hi - b.lo) })

export function times(a: Interval, b: Interval): Interval {
  const products = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
  return { lo: down(Math.min(...products)), hi: up(Math.max(...products)) }
}

export function quotient(a: Interval, b: Interval): Interval {
  if (b.lo <= 0 && b.hi >= 0) throw new IntervalRangeError()
  const quotients = [a.lo / b.lo, a.lo / b.hi, a.hi / b.lo, a.hi / b.hi]
  return { lo: down(Math.min(...quotients)), hi: up(Math.max(...quotients)) }
}

export function square(a: Interval): Interval {
  const near = Math.max(0, a.lo, -a.hi)
  const far = Math.max(-a.lo, a.hi)
  return { lo: Math.max(0, down(near * near)), hi: up(far * far) }
}

export function root(a: Interval): Interval {
  const lo = Math.max(0, down(down(Math.sqrt(Math.max(0, a.lo)))))
  const hi = up(up(Math.sqrt(a.hi)))
  // Verify the bounds using rounded division, so even subnormal inputs
  // can be checked without squaring a tiny endpoint.
  if ((lo > 0 && lo > down(a.lo / lo)) || hi < up(a.hi / hi))
    throw new IntervalRangeError()
  return { lo, hi }
}

export function exp(a: Interval): Interval {
  let argument = a
  let squarings = 0
  while (Math.max(-argument.lo, argument.hi) > 1) {
    argument = quotient(argument, exact(2))
    squarings += 1
  }
  // Taylor's remainder for |x| ≤ 1 is bounded by 3/19! < 3e-17.
  let sum = one
  for (let n = 18; n > 0; n -= 1)
    sum = plus(one, quotient(times(argument, sum), exact(n)))
  sum = plus(sum, { lo: -3e-17, hi: 3e-17 })
  for (let n = 0; n < squarings; n += 1) sum = square(sum)
  return sum
}

/** Enclose sin and cos on angles known to lie in [0, π/2]. */
export function firstQuadrant(angle: Interval): [Interval, Interval] {
  function at(x: number, degree: 0 | 1) {
    // The argument is at most 2. The first omitted term is at most
    // 2^24/24! for cosine and 2^25/25! for sine, both below 3e-17.
    const negativeSquare = minus(zero, square(exact(x)))
    let polynomial = one
    for (let n = 11; n > 0; n -= 1) {
      const exponent = 2 * n + degree
      polynomial = plus(one, quotient(times(negativeSquare, polynomial),
        exact(exponent * (exponent - 1))))
    }
    return plus(times(polynomial, exact(degree === 0 ? 1 : x)), { lo: -3e-17, hi: 3e-17 })
  }
  const left = Math.max(0, angle.lo)
  const right = Math.min(pi.hi / 2, angle.hi)
  return [
    { lo: Math.max(0, at(left, 1).lo), hi: right >= pi.lo / 2 ? 1 : Math.min(1, at(right, 1).hi) },
    { lo: Math.max(0, at(right, 0).lo), hi: Math.min(1, at(left, 0).hi) },
  ]
}

export const binary64Intervals: IntervalMath<Interval> = {
  exact, zero, one, pi, ln10, plus, minus, times, quotient, square, root, exp, firstQuadrant,
  maximum: (values) => ({
    lo: Math.max(...values.map((value) => value.lo)),
    hi: Math.max(...values.map((value) => value.hi)),
  }),
}
