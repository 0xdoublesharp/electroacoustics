const bits = new DataView(new ArrayBuffer(8))
const fractionMask = (1n << 52n) - 1n

/** Decompose a finite binary64 value without performing floating-point arithmetic. */
export function binary64Dyad(value: number): { significand: bigint; exponent: number } {
  bits.setFloat64(0, value)
  const encoded = bits.getBigUint64(0)
  const biasedExponent = Number((encoded >> 52n) & 2047n)
  const mantissa = (encoded & fractionMask) + (biasedExponent === 0 ? 0n : 1n << 52n)
  return {
    significand: encoded >> 63n === 0n ? mantissa : -mantissa,
    exponent: Math.max(biasedExponent, 1) - 1075,
  }
}

/** Round an exact ratio with a positive divisor to binary64, ties to even. */
export function roundRatio(numerator: bigint, denominator: bigint): number {
  if (numerator === 0n) return 0
  const magnitude = numerator < 0n ? -numerator : numerator
  let exponent = magnitude.toString(2).length - denominator.toString(2).length
  if (exponent >= 0 ? magnitude < denominator << BigInt(exponent)
    : magnitude << BigInt(-exponent) < denominator) exponent -= 1

  const unitExponent = Math.max(exponent - 52, -1074)
  const dividend = magnitude << BigInt(Math.max(0, -unitExponent))
  const divisor = denominator << BigInt(Math.max(0, unitExponent))
  const whole = dividend / divisor
  const twiceRemainder = 2n * (dividend % divisor)
  const roundsUp = twiceRemainder > divisor || (twiceRemainder === divisor && whole % 2n === 1n)
  const rounded = whole + BigInt(roundsUp)
  return (numerator < 0n ? -1 : 1) * Number(rounded) * 2 ** unitExponent
}
