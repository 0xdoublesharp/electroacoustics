import { expect, it } from 'vitest'
import * as api from './index.js'
import { circuitFixture } from './testFixtures.js'

const frequencies = Array.from({ length: 36 }, (_, i) => 8 * 2 ** (i / 7))
const condition = { kind: 'added-mass' as const, massKg: 0.08 }

it('fits paired impedance sweeps against a separately computed moving-mass model', () => {
  const { driver, medium } = circuitFixture
  const cms = driver.vasM3 / (medium.densityKgM3 * medium.soundSpeedMps ** 2 * driver.sdM2 ** 2)
  const mms = 1 / ((2 * Math.PI * driver.fsHz) ** 2 * cms)
  const r = 2 * Math.PI * driver.fsHz * mms / driver.qms
  const bl2 = 2 * Math.PI * driver.fsHz * mms * driver.reOhms / driver.qes
  function samples(addedMass: number) {
    return frequencies.map((frequency) => {
      const w = 2 * Math.PI * frequency
      const x = w * (mms + addedMass) - 1 / (w * cms)
      return { frequency, impedanceOhms: { re: driver.reOhms + bl2 * r / (r*r + x*x),
        im: w * driver.leHenries - bl2 * x / (r*r + x*x) } }
    })
  }
  const fit = api.fitDriverImpedance({
    initial: { ...driver, fsHz: driver.fsHz * 1.12, vasM3: driver.vasM3 * 1.2,
      reOhms: driver.reOhms * 0.9, qms: driver.qms * 0.8 }, medium,
    freeAir: samples(0), perturbed: { condition, samples: samples(condition.massKg) },
  })
  expect(fit.converged).toBe(true)
  expect(fit.rmsRelativeError).toBeLessThan(1e-6)
  expect(fit.driver.fsHz).toBeCloseTo(driver.fsHz, 5)
  expect(fit.driver.vasM3).toBeCloseTo(driver.vasM3, 6)
})

it('fits an enclosure loss from measured magnitude and returns per-point residuals', () => {
  const measured = api.createCircuit({ ...circuitFixture, leakageQuality: 15 })
  const samples = frequencies.map((frequency) => ({ frequency,
    impedanceOhms: api.magnitude(measured(frequency).impedanceOhms) }))
  const fit = api.fitEnclosureImpedance({ ...circuitFixture, leakageQuality: 7 }, samples,
    [{ parameter: 'leakageQuality', min: 2, max: 30 }])
  expect(fit.input.leakageQuality).toBeCloseTo(15, 4)
  expect(fit.residuals).toHaveLength(frequencies.length)
  expect(fit.rmsRelativeError).toBeLessThan(1e-8)
})

it('recovers from an overshooting fit step with wider leakage bounds', () => {
  const target = { ...circuitFixture, leakageQuality: 15 }
  const at = api.createCircuit(target)
  const samples = frequencies.map((frequency) => ({ frequency, impedanceOhms: at(frequency).impedanceOhms }))
  const fit = api.fitEnclosureImpedance({ ...target, leakageQuality: 1000 }, samples,
    [{ parameter: 'leakageQuality', min: 0.01, max: 2000 }])
  expect(fit.converged).toBe(true)
  expect(fit.input.leakageQuality).toBeCloseTo(15, 4)
})

it('matches the sealed circuit and checks measurement inputs and numeric limits', () => {
  const { driver, medium, volumeM3 } = circuitFixture
  const frequency = 31
  const driverAt = api.createDriverImpedance(driver, medium, { kind: 'sealed-box', volumeM3 })
  const box = api.createCircuit(circuitFixture)(frequency).impedanceOhms
  expect(driverAt(frequency).re).toBeCloseTo(box.re, 12)
  expect(driverAt(frequency).im).toBeCloseTo(box.im, 12)
  expect(() => driverAt(0)).toThrow(/frequency/)
  expect(() => driverAt(Number.MAX_VALUE)).toThrow(/numeric support/)
  expect(() => api.createDriverImpedance({ ...driver, leHenries: -1 }, medium)).toThrow(/parameters/)
  expect(() => api.createDriverImpedance(driver, medium, { kind: 'added-mass', massKg: 0 })).toThrow(/mass/)
  expect(() => api.createDriverImpedance(driver, medium, { kind: 'sealed-box', volumeM3: 0 })).toThrow(/volume/)
  expect(() => api.impedanceResiduals([], driverAt)).toThrow(/samples/)
  expect(() => api.impedanceResiduals([{ frequency, impedanceOhms: 0 }], driverAt)).toThrow(/sample/)
  expect(() => api.impedanceResiduals([{ frequency, impedanceOhms: 1 }], () => api.c(Infinity))).toThrow(/numeric support/)
})

it('rejects ambiguous loss fits and enforces bounds, geometry, and iteration budgets', () => {
  const at = api.createCircuit({ ...circuitFixture, leakageQuality: 15 })
  const samples = frequencies.map((frequency) => ({ frequency, impedanceOhms: at(frequency).impedanceOhms }))
  const initial = { ...circuitFixture, leakageQuality: 7 }
  const bounds = { parameter: 'leakageQuality' as const, min: 2, max: 30 }
  expect(api.fitEnclosureImpedance(initial, samples, [bounds], { maxIterations: 1 }).converged).toBe(false)
  const limited = api.fitEnclosureImpedance(initial, samples, [{ ...bounds, max: 8 }])
  expect(limited.input.leakageQuality).toBe(8)
  expect(limited.rmsRelativeError).toBeGreaterThan(0)
  expect(() => api.fitEnclosureImpedance(initial, samples, [bounds], { maxIterations: 0 })).toThrow(/budget/)
  expect(() => api.fitEnclosureImpedance(initial, samples, [{ ...bounds, max: 3 }])).toThrow(/bounds/)
  expect(() => api.fitEnclosureImpedance(initial, samples, [bounds, { ...bounds, parameter: 'absorptionQuality' }])).toThrow(/identifiable/)
  expect(() => api.fitEnclosureImpedance(initial, samples, [{ ...bounds, parameter: 'effectiveLengthM' }])).toThrow(/geometry/)
  const { driver, medium } = initial
  const options = { initial: driver, medium, freeAir: samples, perturbed: { condition, samples } }
  expect(() => api.fitDriverImpedance({ ...options, freeAir: samples.slice(0, 3) })).toThrow(/distinct frequencies/)
  expect(() => api.fitDriverImpedance({ ...options, bounds: { fsHz: { min: 0, max: 35 } } })).toThrow(/positive/)
})

it('supports fitting lumped vent parameters and passive radiator mass', () => {
  const port = { areaM2: 0.01, effectiveLengthM: 0.33, quality: 7 }
  const vented = api.createCircuit({ ...circuitFixture, port })
  const samples = frequencies.map((frequency) => ({ frequency, impedanceOhms: vented(frequency).impedanceOhms }))
  const ventFit = api.fitEnclosureImpedance({ ...circuitFixture, port: { ...port, quality: 9, effectiveLengthM: 0.37 } }, samples,
    [{ parameter: 'portQuality', min: 2, max: 30 }, { parameter: 'effectiveLengthM', min: 0.2, max: 0.6 }])
  expect(ventFit.input.port!.quality).toBeCloseTo(port.quality, 4)
  expect(ventFit.input.port!.effectiveLengthM).toBeCloseTo(port.effectiveLengthM, 6)
  const passiveRadiator = { movingMassKg: 0.1, complianceMPerN: 0.001, sdM2: 0.03, mechanicalResistanceNsPerM: 1 }
  const passive = api.createCircuit({ ...circuitFixture, passiveRadiator })
  const fit = api.fitEnclosureImpedance({ ...circuitFixture, passiveRadiator: { ...passiveRadiator, movingMassKg: 0.13 } },
    frequencies.map((frequency) => ({ frequency, impedanceOhms: passive(frequency).impedanceOhms })),
    [{ parameter: 'radiatorMassKg', min: 0.07, max: 0.16 }])
  expect(fit.input.passiveRadiator!.movingMassKg).toBeCloseTo(0.1, 6)
  const distributed = { ...circuitFixture, port: { quality: 7, ductPath: { count: 1, inletCorrectionMeters: 0,
    outletCorrectionMeters: 0, sections: [{ lengthMeters: 0.3, inletAreaSquareMeters: 0.01,
      outletAreaSquareMeters: 0.01, profile: 'straight' as const }] } } }
  expect(() => api.fitEnclosureImpedance(distributed, samples,
    [{ parameter: 'effectiveLengthM', min: 0.2, max: 0.6 }])).toThrow(/geometry/)
})
