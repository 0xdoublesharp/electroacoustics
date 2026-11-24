import { expect, it, vi } from 'vitest'
import { dyadicIntervals } from './dyadicInterval.js'
import * as exactFit from './impedanceCert.js'
import * as api from './index.js'
import { IntervalRangeError } from './interval.js'
import { circuitFixture } from './testFixtures.js'

const frequencies = Array.from({ length: 36 }, (_, i) => 8 * 2 ** (i / 7))
const condition = { kind: 'added-mass' as const, massKg: 0.08 }

function enclosureSamples(input: api.CircuitInput, sampleFrequencies = frequencies) {
  const at = api.createCircuit(input)
  return sampleFrequencies.map((frequency) => ({ frequency, impedanceOhms: at(frequency).impedanceOhms }))
}

function jsonCertificate(certificate: api.ImpedanceFitCertificate | undefined): api.ImpedanceFitCertificate {
  expect(certificate).toBeDefined()
  return JSON.parse(JSON.stringify(certificate))
}

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
  const request = {
    initial: { ...driver, fsHz: driver.fsHz * 1.12, vasM3: driver.vasM3 * 1.2,
      reOhms: driver.reOhms * 0.9, qms: driver.qms * 0.8 }, medium,
    freeAir: samples(0), perturbed: { condition, samples: samples(condition.massKg) },
  }
  const fit = api.fitDriverImpedance(request)
  expect(fit.converged).toBe(true)
  expect(fit.rmsRelativeError).toBeLessThan(1e-6)
  expect(fit.driver.fsHz).toBeCloseTo(driver.fsHz, 5)
  expect(fit.driver.vasM3).toBeCloseTo(driver.vasM3, 6)
  const certificate = jsonCertificate(fit.certificate)
  expect(certificate.kind).toBe('driver')
  expect(certificate.status).toBe('residual-target')
  expect(certificate.sensitivityRank).toBe(6)
  expect(api.verifyDriverImpedanceFitCertificate(request, certificate)).toBe(true)
  expect(api.verifyDriverImpedanceFitCertificate(request, { ...certificate, kind: 'enclosure' })).toBe(false)
  expect(api.verifyDriverImpedanceFitCertificate({ ...request, tolerance: 1e-7 }, certificate)).toBe(false)
  expect(api.verifyDriverImpedanceFitCertificate(request, null!)).toBe(false)
})

it('fits an enclosure loss from measured magnitude and returns per-point residuals', () => {
  const measured = api.createCircuit({ ...circuitFixture, leakageQuality: 15 })
  const samples = frequencies.map((frequency) => ({ frequency,
    impedanceOhms: api.magnitude(measured(frequency).impedanceOhms) }))
  const initial = { ...circuitFixture, leakageQuality: 7 }
  const bounds = [{ parameter: 'leakageQuality' as const, min: 2, max: 30 }]
  const fit = api.fitEnclosureImpedance(initial, samples, bounds)
  expect(fit.input.leakageQuality).toBeCloseTo(15, 4)
  expect(fit.residuals).toHaveLength(frequencies.length)
  expect(fit.rmsRelativeError).toBeLessThan(1e-8)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, bounds, jsonCertificate(fit.certificate))).toBe(true)
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
  const inductive = api.createDriverImpedance({ ...driver, leHenries: 1e190 }, medium)
  expect(() => inductive(1e140)).toThrow(/numeric support/)
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
  const options = { maxIterations: 1 }
  const short = api.fitEnclosureImpedance(initial, samples, [bounds], options)
  const shortCertificate = jsonCertificate(short.certificate)
  expect(short.converged).toBe(false)
  expect(short.status).toBe('iteration-limit')
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, [bounds], shortCertificate, options)).toBe(true)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, [bounds],
    { ...shortCertificate, status: 'stalled' }, options)).toBe(false)
  const forcedStop = jsonCertificate(api.fitEnclosureImpedance(initial, samples, [bounds],
    { ...options, normalizedStepTolerance: 0.99 }).certificate)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, [bounds],
    { ...forcedStop, request: shortCertificate.request, status: 'iteration-limit' }, options))
    .toBe(false)
  const constrained = [{ ...bounds, max: 8 }]
  const limited = api.fitEnclosureImpedance(initial, samples, constrained)
  expect(limited.status).toBe('bound-constrained')
  expect(limited.activeBounds).toEqual([{ parameter: 'leakageQuality', bound: 'max' }])
  expect(limited.converged).toBe(false)
  expect(limited.input.leakageQuality).toBe(8)
  expect(limited.rmsRelativeError).toBeGreaterThan(0)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, constrained, jsonCertificate(limited.certificate))).toBe(true)
  const lower = [{ ...bounds, min: 20 }]
  const startAboveTarget = { ...initial, leakageQuality: 25 }
  const lowerFit = api.fitEnclosureImpedance(startAboveTarget, samples, lower)
  expect(lowerFit.activeBounds).toEqual([{ parameter: 'leakageQuality', bound: 'min' }])
  expect(lowerFit.status).toBe('bound-constrained')
  expect(api.verifyEnclosureImpedanceFitCertificate(startAboveTarget, samples, lower, jsonCertificate(lowerFit.certificate))).toBe(true)
  expect(() => api.fitEnclosureImpedance(initial, samples, [bounds], { maxIterations: 0 })).toThrow(/budget/)
  expect(() => api.fitEnclosureImpedance(initial, samples, [{ ...bounds, max: 3 }])).toThrow(/bounds/)
  expect(() => api.fitEnclosureImpedance(initial, samples, [bounds, { ...bounds, parameter: 'absorptionQuality' }])).toThrow(/identifiable/)
  expect(() => api.fitEnclosureImpedance(initial, samples, [{ ...bounds, parameter: 'effectiveLengthM' }])).toThrow(/geometry/)
  const { driver, medium } = initial
  const driverOptions = { initial: driver, medium, freeAir: samples, perturbed: { condition, samples } }
  expect(() => api.fitDriverImpedance({ ...driverOptions, freeAir: samples.slice(0, 3) })).toThrow(/distinct frequencies/)
  expect(() => api.fitDriverImpedance({ ...driverOptions, bounds: { fsHz: { min: 0, max: 35 } } })).toThrow(/positive/)
})

it('distinguishes a noisy local fit from a stopped step with a nonzero gradient', () => {
  const target = api.createCircuit({ ...circuitFixture, leakageQuality: 15 })
  const samples = frequencies.map((frequency, index) => ({
    frequency,
    impedanceOhms: api.magnitude(target(frequency).impedanceOhms) * (1 + 0.003 * Math.cos(index)),
  }))
  const initial = { ...circuitFixture, leakageQuality: 7 }
  const bounds = [{ parameter: 'leakageQuality' as const, min: 2, max: 30 }]
  const fit = api.fitEnclosureImpedance(initial, samples, bounds)
  expect(fit.status).toBe('stationary')
  expect(fit.sensitivityRank).toBe(1)
  expect(fit.rmsRelativeError).toBeGreaterThan(0.001)
  expect(fit.input.leakageQuality).toBeCloseTo(15, 0)
  const stationary = jsonCertificate(fit.certificate)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, bounds, stationary)).toBe(true)
  const options = { normalizedStepTolerance: 0.5 }
  const stalled = api.fitEnclosureImpedance(initial, samples, bounds, options)
  expect(stalled.status).toBe('stalled')
  expect(stalled.converged).toBe(false)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, bounds, jsonCertificate(stalled.certificate), options)).toBe(true)
})

it('reports a weakly identified parameter even when a sparse sweep matches the initial model', () => {
  const at = api.createCircuit(circuitFixture)
  const samples = [1e7, 2e7].map((frequency) => ({ frequency, impedanceOhms: at(frequency).impedanceOhms }))
  const bounds = [{ parameter: 'volumeM3' as const, min: 0.04, max: 0.09 }]
  const fit = api.fitEnclosureImpedance(circuitFixture, samples, bounds)
  expect(fit.rmsRelativeError).toBe(0)
  expect(fit.status).toBe('poorly-identified')
  expect(fit.sensitivityRank).toBe(0)
  expect(fit.converged).toBe(false)
  const certificate = jsonCertificate(fit.certificate)
  expect(api.verifyEnclosureImpedanceFitCertificate(circuitFixture, samples, bounds, certificate)).toBe(true)
  for (const tampered of [
    { weakDirection: [0] }, { weakDirection: [NaN] }, { weakDirection: [1, 2] }, { preconditioner: [1] },
    { sensitivityRank: 1 }, { sensitivityRank: -1 }, { sensitivityFloor: certificate.sensitivityFloor + 1 },
  ]) {
    expect(api.verifyEnclosureImpedanceFitCertificate(circuitFixture, samples, bounds, { ...certificate, ...tampered })).toBe(false)
  }
})

it('supports fitting lumped vent parameters and passive radiator mass', () => {
  const port = { areaM2: 0.01, effectiveLengthM: 0.33, quality: 7 }
  const vented = api.createCircuit({ ...circuitFixture, port })
  const samples = frequencies.map((frequency) => ({ frequency, impedanceOhms: vented(frequency).impedanceOhms }))
  const initialVent = { ...circuitFixture, port: { ...port, quality: 9, effectiveLengthM: 0.37 } }
  const ventBounds: { parameter: api.EnclosureFitParameter; min: number; max: number }[] =
    [{ parameter: 'portQuality', min: 2, max: 30 }, { parameter: 'effectiveLengthM', min: 0.2, max: 0.6 }]
  const ventFit = api.fitEnclosureImpedance(initialVent, samples, ventBounds)
  expect(ventFit.input.port!.quality).toBeCloseTo(port.quality, 4)
  expect(ventFit.input.port!.effectiveLengthM).toBeCloseTo(port.effectiveLengthM, 6)
  const ventCertificate = jsonCertificate(ventFit.certificate)
  expect(api.verifyEnclosureImpedanceFitCertificate(initialVent, samples, ventBounds, ventCertificate)).toBe(true)
  const invalid = ventCertificate.preconditioner!.slice()
  invalid[1] = 0.25
  expect(api.verifyEnclosureImpedanceFitCertificate(initialVent, samples, ventBounds,
    { ...ventCertificate, preconditioner: invalid })).toBe(false)
  expect(api.verifyEnclosureImpedanceFitCertificate(initialVent, samples, ventBounds,
    { ...ventCertificate, preconditioner: [1, 0, 1000, 1] })).toBe(false)
  const passiveRadiator = { movingMassKg: 0.1, complianceMPerN: 0.001, sdM2: 0.03, mechanicalResistanceNsPerM: 1 }
  const passive = api.createCircuit({ ...circuitFixture, passiveRadiator })
  const initialPassive = { ...circuitFixture, passiveRadiator: { ...passiveRadiator, movingMassKg: 0.13 } }
  const passiveSamples = frequencies.map((frequency) => ({ frequency, impedanceOhms: passive(frequency).impedanceOhms }))
  const passiveBounds = [{ parameter: 'radiatorMassKg' as const, min: 0.07, max: 0.16 }]
  const fit = api.fitEnclosureImpedance(initialPassive, passiveSamples, passiveBounds)
  expect(fit.input.passiveRadiator!.movingMassKg).toBeCloseTo(0.1, 6)
  expect(api.verifyEnclosureImpedanceFitCertificate(initialPassive, passiveSamples, passiveBounds,
    jsonCertificate(fit.certificate))).toBe(true)
  const distributed = { ...circuitFixture, port: { quality: 7, ductPath: { count: 1, inletCorrectionMeters: 0,
    outletCorrectionMeters: 0, sections: [{ lengthMeters: 0.3, inletAreaSquareMeters: 0.01,
      outletAreaSquareMeters: 0.01, profile: 'straight' as const }] } } }
  expect(() => api.fitEnclosureImpedance(distributed, samples,
    [{ parameter: 'effectiveLengthM', min: 0.2, max: 0.6 }])).toThrow(/geometry/)
})

it('certifies a paired sealed-box driver fit with sparse magnitude and complex samples', () => {
  const { driver, medium, volumeM3 } = circuitFixture
  const condition = { kind: 'sealed-box' as const, volumeM3 }
  const free = api.createDriverImpedance(driver, medium)
  const sealed = api.createDriverImpedance(driver, medium, condition)
  const request: api.DriverImpedanceFit = {
    initial: { ...driver, qes: driver.qes * 0.92 }, medium,
    freeAir: [15, 22, 38, 82, 136].map((frequency) => ({ frequency, impedanceOhms: api.magnitude(free(frequency)) })),
    perturbed: { condition, samples: [18, 35, 44, 90, 145].map((frequency) => ({ frequency, impedanceOhms: sealed(frequency) })) },
    bounds: { qes: { min: 0.1, max: 1.5 } },
  }
  const fit = api.fitDriverImpedance(request)
  expect(fit.status).toBe('residual-target')
  expect(fit.driver.qes).toBeCloseTo(driver.qes, 6)
  expect(api.verifyDriverImpedanceFitCertificate(request, jsonCertificate(fit.certificate))).toBe(true)
})

it('certifies distributed-duct loss and volume with finite absorption and series wiring', () => {
  const { driver, medium } = circuitFixture
  const target: api.CircuitInput = {
    ...circuitFixture, driver, medium, quantity: 4, seriesDrivers: 2, absorptionQuality: 14,
    port: { quality: 8, ductPath: { count: 2, inletCorrectionMeters: 0.02, outletCorrectionMeters: 0.023, sections: [
      { lengthMeters: 0.17, inletAreaSquareMeters: 0.01, outletAreaSquareMeters: 0.013, profile: 'conical' },
      { lengthMeters: 0.19, inletAreaSquareMeters: 0.013, outletAreaSquareMeters: 0.016, profile: 'exponential' },
    ] } },
  }
  const samples = enclosureSamples(target)
  const initial = { ...target, volumeM3: target.volumeM3 * 1.04, absorptionQuality: 15, port: { ...target.port!, quality: 10 } }
  const bounds = [
    { parameter: 'portQuality' as const, min: 4, max: 20 },
    { parameter: 'volumeM3' as const, min: 0.04, max: 0.09 },
    { parameter: 'absorptionQuality' as const, min: 8, max: 40 },
  ]
  const fit = api.fitEnclosureImpedance(initial, samples, bounds)
  expect(fit.status).toBe('residual-target')
  expect(fit.input.volumeM3).toBeCloseTo(target.volumeM3, 5)
  expect(fit.input.port!.quality).toBeCloseTo(target.port!.quality, 4)
  expect(fit.input.absorptionQuality).toBeCloseTo(target.absorptionQuality, 4)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, bounds, jsonCertificate(fit.certificate))).toBe(true)
})

it('certifies the weak sensitivity rank and rejects well-observed directions', () => {
  const initial = { ...circuitFixture, port: { areaM2: 0.01, effectiveLengthM: 0.3, quality: Infinity } }
  const { volumeM3 } = initial
  const samples = enclosureSamples(initial, [22, 37, 61])
  const bounds = [
    { parameter: 'volumeM3' as const, min: volumeM3, max: volumeM3 * (1 + 1e-9) },
    { parameter: 'effectiveLengthM' as const, min: 0.2, max: 0.5 },
  ]
  const fit = api.fitEnclosureImpedance(initial, samples, bounds)
  const certificate = jsonCertificate(fit.certificate)
  expect(fit.sensitivityRank).toBe(1)
  expect(fit.status).toBe('poorly-identified')
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, bounds, certificate)).toBe(true)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, bounds,
    { ...certificate, weakDirection: [0, 1] })).toBe(false)
})

it('binds replay to the original request and fails closed on invalid proof fields', () => {
  const initial = { ...circuitFixture, leakageQuality: 12 }
  const samples = enclosureSamples({ ...initial, leakageQuality: 14 }, [19, 33, 52])
  const bounds = [{ parameter: 'leakageQuality' as const, min: 7, max: 26 }]
  const options = { tolerance: 1e-8, maxIterations: 100 }
  const certificate = jsonCertificate(api.fitEnclosureImpedance(initial, samples, bounds, options).certificate)
  const verify = (candidate: unknown) =>
    api.verifyEnclosureImpedanceFitCertificate(initial, samples, bounds, candidate as api.ImpedanceFitCertificate, options)
  expect(verify(certificate)).toBe(true)
  const reversedOptions = { maxIterations: 100, tolerance: 1e-8 }
  const { leakageQuality, ...rest } = initial
  expect(api.verifyEnclosureImpedanceFitCertificate({ leakageQuality, ...rest },
    samples, bounds, certificate, reversedOptions)).toBe(true)
  expect(api.verifyEnclosureImpedanceFitCertificate({ ...initial, absorptionQuality: 40 }, samples, bounds,
    certificate, options)).toBe(false)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, [...samples].reverse(), bounds, certificate, options)).toBe(false)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, [], certificate, options)).toBe(false)
  for (const tampered of [
    { request: '[]' }, { version: 2 }, { kind: 'driver' }, { status: 'stationary' }, { status: 'unknown' },
    { values: [6] }, { values: [27] }, { values: [20] }, { values: Array(1) }, { values: [Infinity] },
    { values: [] }, { values: '14' }, { sensitivityRank: 0 }, { weakDirection: [1] },
    { preconditioner: [0] }, { preconditioner: [Infinity] }, { preconditioner: null },
    { rmsRelativeErrorBound: null }, { rmsRelativeErrorBound: { lower: NaN, upper: 1 } },
    { rmsRelativeErrorBound: { lower: 0, upper: Infinity } },
    { rmsRelativeErrorBound: { lower: -1, upper: 1 } },
    { rmsRelativeErrorBound: { lower: 1, upper: 0 } },
    { rmsRelativeErrorBound: { lower: 1, upper: 2 } },
    { rmsRelativeErrorBound: { lower: 0, upper: 0 } },
    { projectedGradientBound: { lower: 1, upper: 2 } },
  ]) expect(verify({ ...certificate, ...tampered })).toBe(false)
  for (const malformed of [null, undefined, {}, 1, []]) expect(verify(malformed)).toBe(false)
})

it('encloses the RMS and an independently differentiated normalized leakage gradient', () => {
  const initial = { ...circuitFixture, leakageQuality: 7 }
  const samples = enclosureSamples({ ...initial, leakageQuality: 15 }, [25, 43, 72])
  const bounds = [{ parameter: 'leakageQuality' as const, min: 2, max: 30 }]
  const options = { normalizedStepTolerance: 0.99 }
  const fit = api.fitEnclosureImpedance(initial, samples, bounds, options)
  const certificate = jsonCertificate(fit.certificate)
  expect(fit.iterations).toBe(0)
  expect(certificate.values).toEqual([initial.leakageQuality])
  const { driver, medium, volumeM3, leakageQuality } = initial
  const rhoC2 = medium.densityKgM3 * medium.soundSpeedMps ** 2
  const s2 = driver.sdM2 ** 2
  const cms = driver.vasM3 / (rhoC2 * s2)
  const ws = 2 * Math.PI * driver.fsHz
  const mass = 1 / (ws ** 2 * cms)
  const bl2 = ws * mass * driver.reOhms / driver.qes
  const cab = volumeM3 / rhoC2
  const conductance = ws * Math.sqrt(1 + driver.vasM3 / volumeM3) * cab / leakageQuality
  const dY = -conductance * (bounds[0]!.max - bounds[0]!.min) / leakageQuality
  let squares = 0
  let gradient = 0
  for (const { frequency, impedanceOhms: measured } of samples) {
    const w = 2 * Math.PI * frequency
    const y = api.c(conductance, w * cab)
    const zFree = api.c(ws * mass / driver.qms, w * mass - 1 / (w * cms))
    const mech = api.add(api.mul(zFree, y), api.c(s2))
    const predicted = api.add(api.c(driver.reOhms, w * driver.leHenries), api.div(api.mul(api.c(bl2), y), mech))
    const dz = api.div(api.c(bl2 * s2 * dY), api.mul(mech, mech))
    const error = api.sub(predicted, measured)
    const scaleSquared = measured.re ** 2 + measured.im ** 2
    squares += (error.re ** 2 + error.im ** 2) / scaleSquared
    gradient += (error.re * dz.re + error.im * dz.im) / scaleSquared
  }
  const rms = Math.sqrt(squares / (2 * samples.length))
  const pg = Math.abs(gradient / (2 * samples.length))
  const bound = certificate.rmsRelativeErrorBound
  expect(rms).toBeGreaterThanOrEqual(bound.lower)
  expect(rms).toBeLessThanOrEqual(bound.upper)
  expect(pg).toBeGreaterThanOrEqual(certificate.projectedGradientBound.lower)
  expect(pg).toBeLessThanOrEqual(certificate.projectedGradientBound.upper)
  expect(api.verifyEnclosureImpedanceFitCertificate(initial, samples, bounds, certificate, options)).toBe(true)
})

it('keeps the floating-point diagnostics when a dyadic sample norm underflows', () => {
  const initial = circuitFixture
  const samples = [19, 30].map((frequency) => ({ frequency, impedanceOhms: api.c(1e-30) }))
  const bounds = [{ parameter: 'volumeM3' as const, min: 0.04, max: 0.09 }]
  const fit = api.fitEnclosureImpedance(initial, samples, bounds, { normalizedStepTolerance: 0.99 })
  expect(Number.isFinite(fit.rmsRelativeError)).toBe(true)
  expect(fit.certificate).toBeUndefined()
})

it('preserves active-bound diagnostics and pivoted rank if certification runs out of numeric range', () => {
  const port = { areaM2: 0.01, effectiveLengthM: 0.3, quality: 8 }
  const initial = { ...circuitFixture, port, leakageQuality: 11 }
  const samples = enclosureSamples(initial, [18, 35, 45, 61])
  const bounds = [
    { parameter: 'volumeM3' as const, min: 0.04, max: 0.09 },
    { parameter: 'effectiveLengthM' as const, min: 0.2, max: 0.3 },
    { parameter: 'leakageQuality' as const, min: 11, max: 20 },
  ]
  const enclose = vi.spyOn(exactFit, 'evaluateImpedanceFit')
  try {
    enclose.mockImplementationOnce(() => { throw new IntervalRangeError() })
    const fit = api.fitEnclosureImpedance(initial, samples, bounds)
    expect(fit.certificate).toBeUndefined()
    expect(fit.status).toBe('residual-target')
    expect(fit.sensitivityRank).toBe(3)
    expect(fit.activeBounds).toEqual([
      { parameter: 'effectiveLengthM', bound: 'max' },
      { parameter: 'leakageQuality', bound: 'min' },
    ])

    enclose.mockImplementationOnce(() => { throw new IntervalRangeError() })
    const reordered = api.fitEnclosureImpedance(initial, samples, [...bounds].reverse())
    expect(reordered.sensitivityRank).toBe(fit.sensitivityRank)

    enclose.mockImplementationOnce(() => { throw new IntervalRangeError() })
    const sparse = enclosureSamples(circuitFixture, [1e7, 2e7])
    const weak = api.fitEnclosureImpedance(circuitFixture, sparse, [bounds[0]!])
    expect(weak.certificate).toBeUndefined()
    expect(weak.sensitivityRank).toBe(0)
  } finally {
    enclose.mockRestore()
  }
})

it('uses decisive enclosures at a straddled tolerance and rejects inconclusive proofs', () => {
  const { exact } = dyadicIntervals
  const tolerance = 0.125
  const straddles = { lo: exact(0.12).lo, hi: exact(0.13).hi }
  const d = { columns: [[exact(1)]], shifted: [[exact(0.75)]], floor: 0.25,
    active: false, rms: straddles, projected: exact(0.5) }
  const certify = (diagnostics: typeof d) =>
    exactFit.certifyImpedanceFit(diagnostics, 'enclosure', '[]', diagnostics.columns.map(() => 1), tolerance, true, 0.13)
  expect(certify(d).status).toBe('stalled')
  expect(() => certify({ ...d, projected: straddles })).toThrow(IntervalRangeError)
  expect(() => certify({ ...d, shifted: [[exact(0)]] })).toThrow(IntervalRangeError)
  const widePivot = { lo: exact(1).lo, hi: exact(4).hi }
  expect(() => certify({ ...d, columns: [[exact(1)], [exact(1)]],
    shifted: [[exact(2), exact(1)], [exact(1), widePivot]] })).toThrow(IntervalRangeError)
})
