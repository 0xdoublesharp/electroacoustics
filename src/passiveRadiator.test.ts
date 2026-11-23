import { expect, it } from 'vitest'
import * as api from './index.js'
import { circuitFixture } from './testFixtures.js'

const radiator = { movingMassKg: 0.05, complianceMPerN: 0.001,
  mechanicalResistanceNsPerM: 0, sdM2: 0.04, quantity: 2 }

it('inverts passive radiator tuning and remains finite at the radiator and box resonances', () => {
  const { medium, volumeM3 } = circuitFixture
  const tuning = api.passiveRadiatorMassForTuning(radiator, volumeM3, medium, 35)
  const input = { ...circuitFixture, passiveRadiator: { ...radiator, movingMassKg: tuning.movingMassKg },
    leakageQuality: Infinity, absorptionQuality: Infinity }
  const at = api.createCircuit(input)
  expect(api.referenceResonanceHz(input)).toBeCloseTo(35, 10)
  expect(at(35).coneExcursionPeakM).toBeCloseTo(0, 12)
  expect(at(35).radiatorExcursionPeakM).toBeGreaterThan(0)
  const freeHz = api.passiveRadiatorResonanceHz(input.passiveRadiator)
  expect(at(freeHz).splDb).toBeLessThan(-90)
  expect(at(freeHz).portVelocityPeakMps).toBe(0)
  const swept = api.sweepCircuit(input, { minHz: 10, maxHz: 100, maxPoints: 300 })
  expect(swept.points.some((point) => point.frequency === freeHz)).toBe(true)
  const operating = api.operatingSourceFromCircuit(input, [at(35)], { xmaxMeters: 0.02, ratedPowerWattsPerDriver: 0 })
  expect(api.analyzeOutputLimit(operating, { maxRadiatorExcursionPeakM: 0.001 }).points[0]!.limitingFactor)
    .toBe('radiator-excursion')
  const filtered = api.sweepCircuit(input, { minHz: 35, maxHz: 100, filter: { gainDb: -6.020599913279624 } })
  expect(filtered.points[0]!.radiatorExcursionPeakM).toBeCloseTo(at(35).radiatorExcursionPeakM! / 2, 11)
})

it('rejects conflicting topology and nonphysical or unrepresentable radiator inputs', () => {
  const { medium, volumeM3 } = circuitFixture
  const { quantity: _, ...single } = radiator
  expect(api.passiveRadiatorResonanceHz(single)).toBeCloseTo(Math.sqrt(1 / 0.001 / 0.05) / (2 * Math.PI))
  expect(() => api.createCircuit({ ...circuitFixture, passiveRadiator: radiator,
    port: { areaM2: 0.01, effectiveLengthM: 0.3, quality: 7 } })).toThrow(/Choose/)
  expect(() => api.passiveRadiatorResonanceHz({ ...radiator, mechanicalResistanceNsPerM: -1 })).toThrow(RangeError)
  expect(() => api.passiveRadiatorTuningHz(radiator, 0, medium)).toThrow(/cavity/)
  expect(() => api.passiveRadiatorTuningHz({ ...radiator, sdM2: Number.MAX_VALUE }, volumeM3, medium)).toThrow(/stiffness/)
  expect(() => api.passiveRadiatorTuningHz({ ...radiator, movingMassKg: Number.MIN_VALUE }, volumeM3, medium)).toThrow(/tuning/)
  expect(() => api.passiveRadiatorMassForTuning(radiator, volumeM3, medium, 0)).toThrow(/target/)
  expect(() => api.passiveRadiatorMassForTuning(radiator, volumeM3, medium, Number.MAX_VALUE)).toThrow(/mass/)
})
