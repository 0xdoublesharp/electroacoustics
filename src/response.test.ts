import { expect, it } from 'vitest'
import * as api from './index.js'
import { circuitFixture } from './testFixtures.js'

it('summarizes explicit and band-peak references on an irregular grid', () => {
  const points = [20, 30, 45, 60, 80].map((frequency, index) => ({
    frequency,
    splDb: [70, 80, 84, 86, 85][index]!,
    impedanceOhms: api.c(index === 2 ? 3 : 5, index === 2 ? 4 : 3),
    pressurePa: api.c(Math.cos(-2 * Math.PI * frequency * 0.012),
      Math.sin(-2 * Math.PI * frequency * 0.012)),
  }))
  const result = api.summarizeResponse(points, {
    band: { minHz: 30, maxHz: 80 }, reference: { kind: 'band-peak' },
  })
  expect(result.referenceSplDb).toBe(86)
  expect(result.f3Hz).toBeCloseTo(41.25)
  expect(result.f6Hz).toBe(30)
  expect(result.f10Hz).toBe(26)
  expect(result.rippleDb).toBe(6)
  expect(result.minimumImpedance).toEqual({ value: 5, frequency: 45 })
  expect(result.maxGroupDelayMs).toBeCloseTo(12, 10)
  expect(api.summarizeResponse(points, { reference: { kind: 'explicit', splDb: 100 } }).f3Hz).toBeNull()
})

it('scales the mass-controlled reference with wiring, distance and radiation convention', () => {
  const baseline = api.massControlledSplDb(circuitFixture)
  const changed = api.massControlledSplDb({ ...circuitFixture, quantity: 2, seriesDrivers: 2,
    distanceM: 2, radiationSolidAngle: 4 * Math.PI })
  expect(changed - baseline).toBeCloseTo(-20 * Math.log10(4), 10)
  expect(() => api.massControlledSplDb({ ...circuitFixture, voltageRms: 0 })).toThrow(RangeError)
  expect(() => api.massControlledSplDb({ ...circuitFixture, distanceM: 0 })).toThrow(RangeError)
})

it('keeps exact pressure nulls out of group delay and validates sample and band inputs', () => {
  const points = [20, 40, 60].map((frequency, index) => ({ frequency,
    pressurePa: api.c(index === 1 ? 1 : 0), splDb: 80, impedanceOhms: api.c(6) }))
  expect(api.responseGroupDelayMs(points)).toEqual([null, null, null])
  const options = { reference: { kind: 'band-peak' as const } }
  expect(api.summarizeResponse(points, options).maxGroupDelayMs).toBeNull()
  expect(() => api.summarizeResponse([], options)).toThrow(/Invalid response band/)
  expect(() => api.summarizeResponse(points, { ...options, band: { minHz: 21, maxHz: 22 } })).toThrow(/no samples/)
  expect(() => api.summarizeResponse(points, { reference: { kind: 'explicit', splDb: NaN } })).toThrow(/reference/)
  expect(() => api.responseGroupDelayMs([points[0]!, points[0]!])).toThrow(/increasing/)
  expect(() => api.summarizeResponse([{ ...points[0]!, splDb: NaN }], options)).toThrow(/sample/)
})
