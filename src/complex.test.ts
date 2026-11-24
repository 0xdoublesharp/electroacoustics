import { expect, it } from 'vitest'
import { add, c, div, sub } from './index'

it('subtracts RMS phasors component by component without mutating them', () => {
  const a = c(2, -3)
  const b = c(-4, 5)
  const difference = sub(a, b)
  expect(difference).toEqual(c(6, -8))
  expect(add(difference, b)).toEqual(a)
  expect(a).toEqual(c(2, -3))
  expect(b).toEqual(c(-4, 5))
})

it('divides very large and very small phasors without overflowing their squared magnitude', () => {
  for (const scale of [1e-200, 1e-155, 1e160, 1e300]) {
    const actual = div({ re: 2 * scale, im: 3 * scale }, { re: scale, im: scale })
    expect(actual.re).toBeCloseTo(2.5, 14)
    expect(actual.im).toBeCloseTo(0.5, 14)
  }
  expect(div({ re: Number.MAX_VALUE, im: 0 }, { re: 2, im: 0 }).re).toBe(Number.MAX_VALUE / 2)
  expect(div(c(0), c(3))).toEqual(c(0))
  expect(div(c(1.5e308, 0), c(0.5, 0.5))).toEqual(c(1.5e308, -1.5e308))
  expect(div(c(1e-300), c(1e10, 1e10)).re).toBe(5e-311)
  expect(div(c(1e300, 1e-100), c(1))).toEqual(c(1e300, 1e-100))
  expect(div(c(0), c(1e-200))).toEqual(c(0))
  const tiny = div(c(2e-220, 3e-220), c(1e-150, 1e-150))
  expect(tiny.re / 1e-70).toBeCloseTo(2.5, 14)
  expect(tiny.im / 1e-70).toBeCloseTo(0.5, 14)
})

it('preserves a subnormal quotient component alongside a normal component', () => {
  expect(div(c(Number.MIN_VALUE, 1), c(0, 0.5))).toEqual(c(2, -2 * Number.MIN_VALUE))
})

it('rounds a quotient built from two nearly cancelling products', () => {
  const offset = 2 ** -52
  // The exact real numerator is -offset², with denominator 2-2*offset+offset².
  // The closest binary64 result is one representable step below -2^-105.
  expect(div(c(1 + offset, -1), c(1 - offset, 1)).re).toBe(-(2 ** -105 + 2 ** -157))
})

it('rounds halfway values to even and rejects unrepresentable quotients', () => {
  expect(div(c(Number.MIN_VALUE), c(2)).re).toBe(0)
  expect(div(c(3 * Number.MIN_VALUE), c(2)).re).toBe(2 * Number.MIN_VALUE)
  expect(div(c(-Number.MIN_VALUE), c(2)).re).toBe(-0)
  expect(() => div(c(1), c(Number.MIN_VALUE))).toThrow(/numeric range/)
  expect(() => div(c(1), c(0))).toThrow(/numeric range/)
  expect(() => div(c(Infinity), c(1))).toThrow(/numeric range/)
  expect(() => div(c(0, Number.MAX_VALUE), c(0.5))).toThrow(/numeric range/)
})
