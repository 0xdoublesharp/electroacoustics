import type { BiquadCoefficients } from './filters.js'
import type { IntervalMath } from './interval.js'

/** Numerator and denominator after multiplying both by z on the unit circle. */
export function centeredBiquad<T>(
  { b0, b1, b2, a1, a2 }: Readonly<BiquadCoefficients>, versine: T, sine: T,
  { exact, minus, one, plus, times }: IntervalMath<T>,
) {
  const bSum = plus(exact(b0), exact(b2))
  const aSum = plus(one, exact(a2))
  return {
    numReal: minus(plus(exact(b1), bSum), times(bSum, versine)),
    denReal: minus(plus(exact(a1), aSum), times(aSum, versine)),
    numImag: times(minus(exact(b0), exact(b2)), sine),
    denImag: times(minus(one, exact(a2)), sine),
  }
}
