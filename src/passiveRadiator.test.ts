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
it('returns a finite free resonance when only the intermediate mass ratio would overflow', () => {
  const inputs = { ...radiator, movingMassKg: 1e-300, complianceMPerN: 1e-100 }
  expect(api.passiveRadiatorResonanceHz(inputs) / 1e200).toBeCloseTo(1 / (2 * Math.PI), 13)
  expect(() => api.passiveRadiatorResonanceHz({ ...inputs, movingMassKg: Number.MIN_VALUE,
    complianceMPerN: Number.MIN_VALUE })).toThrow(/numeric support/)
})

it('balances copper, cone, cavity, and radiator losses for a wired cabinet', () => {
  const input = { ...circuitFixture, quantity: 4, seriesDrivers: 2,
    leakageQuality: 14, absorptionQuality: 22,
    passiveRadiator: { ...radiator, mechanicalResistanceNsPerM: 1.5 } }
  const { driver, medium, passiveRadiator: r } = input
  const { densityKgM3: rho, soundSpeedMps: speed } = medium
  const compliance = driver.vasM3 / (rho * speed ** 2 * driver.sdM2 ** 2)
  const omegaFree = 2 * Math.PI * driver.fsHz
  const coneResistance = 1 / (omegaFree * compliance * driver.qms)
  const cavityCompliance = input.volumeM3 / (rho * speed ** 2)
  const characteristic = Math.sqrt(r.movingMassKg / (r.quantity * r.sdM2 ** 2 * cavityCompliance))
  const lossConductance = (1 / input.leakageQuality + 1 / input.absorptionQuality) / characteristic
  const at = api.createCircuit(input)

  for (const frequency of [12, api.passiveRadiatorResonanceHz(r), api.referenceResonanceHz(input), 100]) {
    const point = at(frequency)
    const omega = 2 * Math.PI * frequency
    const coneFlow = point.coneVolumeVelocityM3s
    const radiatorFlow = point.radiatorVolumeVelocityM3s!
    const coneVelocity = Math.hypot(coneFlow.re, coneFlow.im) / (input.quantity * driver.sdM2)
    const radRe = -radiatorFlow.re / (r.quantity * r.sdM2)
    const radIm = -radiatorFlow.im / (r.quantity * r.sdM2)
    const radReactance = omega * r.movingMassKg - 1 / (omega * r.complianceMPerN)
    const pressure = Math.hypot(r.mechanicalResistanceNsPerM * radRe - radReactance * radIm,
      r.mechanicalResistanceNsPerM * radIm + radReactance * radRe) / r.sdM2
    const totalLoss = point.coilLossWatts + input.quantity * coneResistance * coneVelocity ** 2 +
      lossConductance * pressure ** 2 + r.quantity * r.mechanicalResistanceNsPerM * (radRe ** 2 + radIm ** 2)
    expect(point.realInputPowerWatts).toBeCloseTo(totalLoss, 11)
  }
})
