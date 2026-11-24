import { expect, it } from 'vitest'
import * as api from './index.js'

it('round-trips an ideal sealed alignment with two drivers', () => {
  const driver = { fsHz: 25, vasM3: 0.08, qts: 0.4, quantity: 2 }
  const box = api.sealedVolumeForQtc(driver, 0.8)
  expect(box.volumeM3).toBeCloseTo(0.16 / 3, 12)
  expect(box.fcHz).toBe(50)
  expect(api.sealedAlignment(driver, box.volumeM3)).toEqual(box)
  expect(box.f3Hz).toBeLessThan(box.fcHz)
  expect(() => api.sealedVolumeForQtc(driver, 0.4)).toThrow(RangeError)
})

it('round-trips both lumped and distributed vent tuning', () => {
  const path = {
    count: 2,
    inletCorrectionMeters: 0.05,
    outletCorrectionMeters: 0.05,
    sections: [{ profile: 'straight' as const, lengthMeters: 0.3,
      inletAreaSquareMeters: 0.01, outletAreaSquareMeters: 0.01 }],
  }
  const volume = api.ductVolumeForTuning(path, 30, 343)
  expect(api.ductPathTuning(path, volume, 343)).toBeCloseTo(30, 8)
  const length = api.ventLengthForTuning(0.02, volume, 30, 343)
  expect(api.ventTuningHz(0.02, volume, length, 343)).toBeCloseTo(30, 10)
  expect(() => api.ductVolumeForTuning(path, 550, 343)).toThrow(RangeError)
})

it('rejects invalid geometry and roots above the fundamental branch', () => {
  const driver = { fsHz: 25, vasM3: 0.08, qts: 0.4 }
  const { volumeM3 } = api.sealedVolumeForQtc(driver, 0.6)
  expect(api.sealedAlignment(driver, volumeM3).qtc).toBeCloseTo(0.6)
  expect(() => api.sealedAlignment({ ...driver, quantity: 1.2 }, volumeM3)).toThrow(/quantity/)
  expect(() => api.ventLengthForTuning(0, volumeM3, 30, 343)).toThrow(RangeError)
  const path = { count: 1, inletCorrectionMeters: 0, outletCorrectionMeters: 0,
    sections: [{ profile: 'straight' as const, lengthMeters: 1,
      inletAreaSquareMeters: 0.01, outletAreaSquareMeters: 0.01 }] }
  expect(() => api.ductVolumeForTuning(path, 370, 343)).toThrow(/fundamental/)
})

it('solves distributed physical length with changing cavity volume', () => {
  const pathForLength = (length: number) => ({ count: 1, inletCorrectionMeters: 0.02,
    outletCorrectionMeters: 0.02, sections: [{ profile: 'straight' as const, lengthMeters: length,
      inletAreaSquareMeters: 0.01, outletAreaSquareMeters: 0.01 }] })
  const volumeForLength = (length: number) => 0.07 - 0.01 * length
  const targetHz = api.ductPathTuning(pathForLength(0.4), volumeForLength(0.4), 343)
  const setup = { minLengthM: 0.1, maxLengthM: 0.9, targetHz, soundSpeedMps: 343, pathForLength, volumeForLength }
  const solution = api.solveDuctLengthForTuning(setup)
  expect(solution.status).toBe('root')
  expect(solution.lengthM).toBeCloseTo(0.4, 8)
  expect(solution.iterations).toBe(30)
  const { minLengthM, maxLengthM } = solution.bracket
  expect(maxLengthM - minLengthM).toBeLessThanOrEqual(1e-9)
  expect(api.ductPathTuning(pathForLength(minLengthM), volumeForLength(minLengthM), 343)).toBeGreaterThanOrEqual(targetHz)
  expect(api.ductPathTuning(pathForLength(maxLengthM), volumeForLength(maxLengthM), 343)).toBeLessThanOrEqual(targetHz)
  expect(api.solveDuctLengthForTuning({ ...setup, minLengthM: 0.5 })).toMatchObject({
    status: 'shortest-tunes-low', lengthM: 0.5, bracket: { minLengthM: 0.5, maxLengthM: 0.9 }, iterations: 0,
  })
  expect(api.solveDuctLengthForTuning({ ...setup, maxLengthM: 0.2 })).toMatchObject({
    status: 'longest-tunes-high', lengthM: 0.2, bracket: { minLengthM: 0.1, maxLengthM: 0.2 }, iterations: 0,
  })
  expect(api.solveDuctLengthForTuning({ ...setup, toleranceM: 0.01 }).lengthM).toBeCloseTo(0.4, 2)
  expect(() => api.solveDuctLengthForTuning({ ...setup, minLengthM: 1 })).toThrow(/bracket/)
  const oneStep = { ...setup, minLengthM: 0.25, maxLengthM: 0.75, maxIterations: 1 }
  expect(api.solveDuctLengthForTuning(oneStep)).toMatchObject({
    status: 'budget-exhausted', lengthM: 0.375, bracket: { minLengthM: 0.25, maxLengthM: 0.5 }, iterations: 1,
  })
  expect(api.solveDuctLengthForTuning({ ...oneStep, toleranceM: 0.25 })).toMatchObject({ status: 'root', iterations: 1 })
  for (const maxIterations of [0, -1, 201, 1.5, NaN, Infinity, 2 ** 53])
    expect(() => api.solveDuctLengthForTuning({ ...setup, maxIterations })).toThrow(/iterations/i)

  // Adjacent endpoints straddle a midpoint tie that rounds to either endpoint.
  for (const low of [0.5, 0.5 + Number.EPSILON / 2]) {
    const high = low + Number.EPSILON / 2
    const box = {
      ...setup, minLengthM: low, maxLengthM: high, maxIterations: 200,
      targetHz: api.ductPathTuning(pathForLength(low), volumeForLength(low), 343),
    }
    expect(api.solveDuctLengthForTuning({ ...box, toleranceM: Number.MIN_VALUE })).toMatchObject({
      status: 'resolution-limit', bracket: { minLengthM: low, maxLengthM: high }, iterations: 0,
    })
    expect(api.solveDuctLengthForTuning({ ...box, toleranceM: high - low })).toMatchObject({ status: 'root', iterations: 0 })
  }
})
