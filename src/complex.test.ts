import { expect, it } from 'vitest'
import { add, c, sub } from './index'

it('subtracts RMS phasors component by component without mutating them', () => {
  const a = c(2, -3)
  const b = c(-4, 5)
  const difference = sub(a, b)
  expect(difference).toEqual(c(6, -8))
  expect(add(difference, b)).toEqual(a)
  expect(a).toEqual(c(2, -3))
  expect(b).toEqual(c(-4, 5))
})
