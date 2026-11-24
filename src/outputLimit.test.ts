import { expect, it, vi } from 'vitest'
import * as api from './index.js'
import { dyadicIntervals } from './dyadicInterval.js'
import { enclosedOr, exact, plus, root, zero } from './interval.js'
import { circuitFixture, odeFixture } from './testFixtures.js'

it('reports an amplifier-current bottleneck and subtracts DSP boost from headroom', () => {
  const source = {
    perDriverReferenceVoltage: 2, seriesDriversPerString: 2, parallelStrings: 1,
    dcResistancePerDriver: 3, xmaxMeters: 0, ratedPowerWattsPerDriver: 0,
    points: [
      { frequency: 25, coneExcursionMeters: 0.001, portVelocity: 0, portMach: 0, impedanceOhms: 4, splDb: 80 },
      { frequency: 50, coneExcursionMeters: 0.001, portVelocity: 0, portMach: 0, impedanceOhms: 10, splDb: 90 },
    ],
  }
  const result = api.analyzeOutputLimit(source, {
    maxAmplifierVoltageRms: 15, maxAmplifierCurrentRms: 2,
    driveVoltageRms: 4, filter: { gainDb: 6.020599913279624 },
  })
  expect(result.points[0]).toMatchObject({ maxTerminalVoltageRms: 8,
    maxInputVoltageRms: 4, limitingFactor: 'amplifier-current', headroomDb: 0 })
  expect(result.points[0]!.maxSplDb).toBeCloseTo(86.0206)
  expect(result.points[1]).toMatchObject({ maxTerminalVoltageRms: 15, limitingFactor: 'amplifier-voltage' })
  expect(result.bandInputLimit).toEqual({ value: 4, frequency: 25 })
})

it('reports unavailable headroom for missing limits, pressure, and DSP at a null', () => {
  const at = api.createCircuit(circuitFixture)
  const src = api.operatingSourceFromCircuit(circuitFixture, [at(25)], { xmaxMeters: 0, ratedPowerWattsPerDriver: 0 })
  expect(api.analyzeOutputLimit(src).points[0]!.limitingFactor).toBeNull()
  const quiet = api.analyzeOutputLimit(src, { maxAmplifierVoltageRms: 2, filter: { gainDb: -8000 } })
  expect(quiet.points[0]).toMatchObject({ maxTerminalVoltageRms: 2, maxInputVoltageRms: null, maxSplDb: null })
  const { splDb: _, ...point } = src.points[0]!
  const missing = { ...src, points: [{ ...point, radiatorExcursionPeakM: 0 }] }
  expect(api.analyzeOutputLimit(missing, { maxRadiatorExcursionPeakM: 1, maxAmplifierVoltageRms: 2, driveVoltageRms: 3 }).points[0])
    .toMatchObject({ limitingFactor: 'amplifier-voltage', plannedSplDb: null, maxSplDb: null })
  expect(() => api.analyzeOutputLimit(src, { maxRadiatorExcursionPeakM: 1 })).toThrow(/radiator/)
  expect(() => api.analyzeOutputLimit(src, { maxAmplifierCurrentRms: -1 })).toThrow(/finite limits/)
  expect(() => api.analyzeOutputLimit(src, { maxAmplifierCurrentRms: Number.MAX_VALUE })).toThrow(/numeric range/)
  expect(() => api.analyzeOutputLimit(src, { maxAmplifierVoltageRms: 2, filter: { gainDb: -6400 } })).toThrow(/DSP input limit/)
})

it('keeps single-frequency and filtered SPL finite when the pressure ratio overflows', () => {
  const reference = api.createCircuit(circuitFixture)(40).splDb
  const input = { ...circuitFixture, distanceM: 1e-305 }
  expect(api.createCircuit(input)(40).splDb).toBeCloseTo(reference + 6100, 9)
  const sweep = api.sweepCircuit(input, { minHz: 40, maxHz: 50, filter: { gainDb: 0 } })
  expect(sweep.points[0]!.splDb).toBeCloseTo(reference + 6100, 9)
  expect(() => api.createCircuit({ ...input, distanceM: 1e-310 })(40)).toThrow(/evaluation exceeds finite numerical support/)
})

it('bounds the narrow EQ peak that makes a sampled drive limit 36% too high', () => {
  const at = api.createCircuit(circuitFixture)
  const source = api.operatingSourceFromCircuit(circuitFixture, [at(30), at(80)], {
    xmaxMeters: 0, ratedPowerWattsPerDriver: 0,
  })
  const center = 51
  const boost = 1.36
  const ceiling = 20
  const options = {
    maxAmplifierVoltageRms: ceiling,
    filter: { digital: { sampleRateHz: 48000, stages: [
      { kind: 'peaking' as const, frequencyHz: center, q: 60, gainDb: 20 * Math.log10(boost) },
    ] } },
  }
  // The cookbook peaking stage reaches its specified voltage gain at center
  // and has no higher gain elsewhere. The ideal input ceiling is V / boost.
  const reference = ceiling / boost
  const sampled = api.analyzeOutputLimit(source, options)
  expect(sampled.bandInputLimit!.value / reference).toBeCloseTo(1.36, 3)
  const bounded = api.analyzeBandOutputLimit(circuitFixture, { minHz: 30, maxHz: 80, ...options })
  expect(bounded.status).toBe('resolved')
  expect(bounded.safeInputVoltageRms).toBeLessThanOrEqual(reference)
  expect(bounded.upperInputVoltageRms).toBeGreaterThanOrEqual(reference - 1e-8)
  expect(bounded.errorBoundDb).toBeLessThanOrEqual(0.1)
  const request = { minHz: 30, maxHz: 80, ...options }
  const certificate = bounded.certificate!
  expect(api.verifyBandOutputCertificate(circuitFixture, request, certificate)).toBe(true)
  expect(api.verifyBandOutputCertificate(circuitFixture, request, {
    ...certificate, spans: certificate.spans.slice(1),
  })).toBe(false)
  expect(api.verifyBandOutputCertificate(circuitFixture, request, {
    ...certificate, safeInputVoltageRms: reference * 1.01,
  })).toBe(false)
  expect(api.verifyBandOutputCertificate(circuitFixture, {
    ...request, maxAmplifierVoltageRms: 19,
  }, certificate)).toBe(false)
  expect(api.verifyBandOutputCertificate(circuitFixture, request, {
    ...certificate, safeInputVoltageRms: certificate.upperInputVoltageRms,
  })).toBe(false)
  expect(api.verifyBandOutputCertificate(circuitFixture, request, {
    ...certificate, spans: certificate.spans.slice(0, -1),
  })).toBe(false)
  expect(api.verifyBandOutputCertificate(circuitFixture, request, {
    ...certificate, upperInputVoltageRms: certificate.safeInputVoltageRms,
  })).toBe(false)
  expect(api.verifyBandOutputCertificate(circuitFixture, request, {
    ...certificate, errorBoundDb: 1e-9,
  })).toBe(false)
  expect(api.verifyBandOutputCertificate(circuitFixture, { ...request, minHz: 0 }, certificate)).toBe(false)
  expect(api.verifyBandOutputCertificate(circuitFixture, request, null!)).toBe(false)
})

const band = { minHz: 15, maxHz: 300 }
const sealed = { ...circuitFixture, driver: { ...circuitFixture.driver, leHenries: 0.0012 } }
const vented = { ...sealed, leakageQuality: 17, absorptionQuality: 12,
  quantity: 4, seriesDrivers: 2, port: { areaM2: 0.012, effectiveLengthM: 0.34, quality: 8 } }
const radiator = { movingMassKg: 0.09, complianceMPerN: 0.001,
  mechanicalResistanceNsPerM: 1.2, sdM2: 0.04, quantity: 2 }
const passive = { ...sealed, leakageQuality: 10, passiveRadiator: radiator }
const { quantity: _quantity, ...singleRadiator } = radiator

function referenceUsage(input: api.CircuitInput, options: api.BandOutputLimitOptions, frequency: number,
  duct?: { mass: number; reactance: number; peak: number }) {
  // Solve for the current after forming the loaded mechanical impedance.
  // This uses the admittance form of the network, without the solver's
  // cleared denominator or interval operations.
  const { driver: d, volumeM3: volume, medium: { densityKgM3: rho, soundSpeedMps: c } } = input
  const w = 2 * Math.PI * frequency
  const ws = 2 * Math.PI * d.fsHz
  const k = rho * c ** 2 * d.sdM2 ** 2 / d.vasM3
  const m = k / ws ** 2
  const rm = ws * m / d.qms
  const bl = Math.sqrt(ws * m * d.reOhms / d.qes)
  const cab = volume / (rho * c ** 2)
  const count = input.quantity ?? 1
  const series = input.seriesDrivers ?? 1
  const parallel = count / series
  let characteristic = 1 / (ws * Math.sqrt(1 + count * d.vasM3 / volume) * cab)
  let branchR = 0, branchX = 0, branchScale = 0
  const pr = input.passiveRadiator
  if (input.port) {
    const portMass = duct?.mass ?? rho * input.port.effectiveLengthM! / input.port.areaM2!
    characteristic = Math.sqrt(portMass / cab)
    branchR = characteristic / input.port.quality
    branchX = duct?.reactance ?? w * portMass
    branchScale = 1
  } else if (pr) {
    branchScale = (pr.quantity ?? 1) * pr.sdM2 ** 2
    characteristic = Math.sqrt(pr.movingMassKg / (cab * branchScale))
    branchR = pr.mechanicalResistanceNsPerM
    branchX = w * pr.movingMassKg - 1 / (w * pr.complianceMPerN)
  }
  const branchNorm = branchScale === 0 ? 1 : branchR ** 2 + branchX ** 2
  const yr = (1 / input.leakageQuality + 1 / input.absorptionQuality) / characteristic +
    branchScale * branchR / branchNorm
  const yi = w * cab - branchScale * branchX / branchNorm
  const y2 = yr ** 2 + yi ** 2
  const load = count * d.sdM2 ** 2
  const zr = rm + load * yr / y2
  const zi = w * m - k / w - load * yi / y2
  const z2 = zr ** 2 + zi ** 2
  const terminalZ = Math.hypot(d.reOhms + bl ** 2 * zr / z2, w * d.leHenries - bl ** 2 * zi / z2)
  const perDriverI = 1 / (series * terminalZ)
  const speed = bl * perDriverI / Math.sqrt(z2)
  const pressure = count * d.sdM2 * speed / Math.sqrt(y2)
  const portMach = input.port
    ? Math.SQRT2 * pressure * (duct?.peak ?? 1 / input.port.areaM2!) / (Math.sqrt(branchNorm) * c) : 0
  const radiatorTravel = pr ? Math.SQRT2 * pressure * pr.sdM2 / (Math.sqrt(branchNorm) * w) : 0
  return Math.max(
    Math.SQRT2 * speed / w / (options.xmaxMeters ?? Infinity),
    portMach / (options.maxPortMach ?? Infinity),
    radiatorTravel / (options.maxRadiatorExcursionPeakM ?? Infinity),
    perDriverI * Math.sqrt(d.reOhms / (options.ratedPowerWattsPerDriver ?? Infinity)),
    parallel * perDriverI / (options.maxAmplifierCurrentRms ?? Infinity),
    1 / (options.maxAmplifierVoltageRms ?? Infinity),
  )
}

it.each([
  { input: sealed, limits: { maxAmplifierCurrentRms: 1, maxAmplifierVoltageRms: 8 } },
  { input: vented, limits: { xmaxMeters: 0.008 } },
  { input: vented, limits: { maxPortMach: 0.045 } },
  { input: vented, limits: { ratedPowerWattsPerDriver: 140 } },
  { input: vented, limits: { maxAmplifierCurrentRms: 3 } },
  { input: passive, limits: { maxRadiatorExcursionPeakM: 0.008 } },
  { input: { ...passive, passiveRadiator: singleRadiator }, limits: { maxRadiatorExcursionPeakM: 0.008 } },
])('encloses the independently evaluated circuit ceiling for $limits', ({ input, limits }) => {
  const options = { ...band, ...limits }
  let peak = 0
  let peakHz = band.minHz
  for (let i = 0; i <= 12000; i += 1) {
    const frequency = band.minHz + (band.maxHz - band.minHz) * i / 12000
    const usage = referenceUsage(input, options, frequency)
    if (usage > peak) [peak, peakHz] = [usage, frequency]
  }
  const result = api.analyzeBandOutputLimit(input, options)
  expect(result.status).toBe('resolved')
  expect(result.safeInputVoltageRms).toBeLessThanOrEqual(1 / peak)
  expect(result.upperInputVoltageRms!).toBeGreaterThanOrEqual(1 / peak - 1e-5)
  expect(result.errorBoundDb).toBeLessThanOrEqual(0.1)
  if (input === sealed) {
    expect(peakHz).toBeGreaterThan(band.minHz)
    expect(peakHz).toBeLessThan(band.maxHz)
    expect(referenceUsage(input, options, 36)).toBe(1 / limits.maxAmplifierVoltageRms!)
  }
})

it('certifies a mixed analog and raw digital filter up to Nyquist', () => {
  const filter: api.FilterChain = { highpassHz: 20, highpassType: 'BW24',
    lowpassHz: 90, gainDb: -7, delaySeconds: 0.2, digital: { sampleRateHz: 1000,
      stages: [{ kind: 'biquad', b0: 0.5, b1: -0.5, b2: 0, a1: 0, a2: 0 }] } }
  const result = api.analyzeBandOutputLimit(sealed, {
    minHz: 10, maxHz: 500, filter, maxAmplifierVoltageRms: 20,
  })
  let maxGain = 0
  for (let f = 10; f <= 500; f += 0.001) {
    const highpass = 1 / Math.sqrt(1 + (20 / f) ** 8)
    const lowpass = 1 / (1 + (f / 90) ** 4)
    const digitalGain = Math.sin(Math.PI * f / 1000)
    maxGain = Math.max(maxGain, 10 ** (-7 / 20) * highpass * lowpass * digitalGain)
  }
  expect(result.status).toBe('resolved')
  expect(result.safeInputVoltageRms).toBeLessThanOrEqual(20 / maxGain)
  expect(result.upperInputVoltageRms!).toBeGreaterThanOrEqual(20 / maxGain - 1e-7)
  expect(result.errorBoundDb).toBeLessThanOrEqual(0.1)
})

it('bounds the thermal limit through a lossless lumped vent with default wiring', () => {
  const input = { ...circuitFixture, port: { ...vented.port, quality: Infinity } }
  const options = { minHz: 50, maxHz: 52, ratedPowerWattsPerDriver: 140 }
  const result = api.analyzeBandOutputLimit(input, options)
  const sampleCeiling = 1 / referenceUsage(input, options, 52)
  expect(result.status).toBe('resolved')
  expect(result.safeInputVoltageRms).toBeLessThanOrEqual(sampleCeiling)
  expect(result.upperInputVoltageRms!).toBeGreaterThanOrEqual(sampleCeiling - 1e-6)
})

it('rejects endpoint overflow and an inaccurate square root enclosure', () => {
  expect(enclosedOr(() => plus(exact(Number.MAX_VALUE), zero), null)).toBeNull()
  const sqrt = vi.spyOn(Math, 'sqrt').mockReturnValue(3)
  try {
    expect(enclosedOr(() => root(exact(4)), null)).toBeNull()
    sqrt.mockReturnValue(1)
    expect(enclosedOr(() => root(exact(4)), null)).toBeNull()
  } finally {
    sqrt.mockRestore()
  }
})

it('encloses signed dyadic arithmetic and rejects out-of-range intermediates', () => {
  const math = dyadicIntervals
  const unit = math.one.lo
  expect(math.exact(Number.MIN_VALUE)).toEqual({ lo: 0n, hi: 1n })
  expect(math.exact(-Number.MIN_VALUE)).toEqual({ lo: -1n, hi: 0n })
  expect(enclosedOr(() => math.exact(Infinity), null)).toBeNull()
  expect(enclosedOr(() => math.quotient(math.one, math.zero), null)).toBeNull()
  expect(enclosedOr(() => math.quotient(math.one, { lo: -unit, hi: unit }), null)).toBeNull()
  expect(math.quotient(math.exact(2), math.exact(-1))).toEqual(math.exact(-2))
  expect(math.root(math.zero)).toEqual(math.zero)
  expect(math.root(math.exact(4))).toEqual(math.exact(2))
  expect(math.root(math.exact(2)).hi - math.root(math.exact(2)).lo).toBe(1n)
  const exp = math.exp(math.exact(0.5))
  expect(exp.lo).toBeLessThan(exp.hi)
  const scaledExp = math.exp(math.exact(2))
  expect(scaledExp.lo).toBeGreaterThan(7n * unit)
  expect(scaledExp.hi).toBeLessThan(8n * unit)
  expect(enclosedOr(() => math.exp(math.exact(1025)), null)).toBeNull()
  const [sine, cosine] = math.firstQuadrant({ lo: 0n, hi: math.pi.hi })
  expect(sine).toEqual({ lo: 0n, hi: unit })
  expect(cosine).toEqual({ lo: 0n, hi: unit })
})

it('fails closed at the band certificate boundary', () => {
  const request = { ...band, maxAmplifierVoltageRms: 20 }
  const report = api.analyzeBandOutputLimit(sealed, { ...request, maxAmplifierVoltageRms: 1e100 })
  expect(report).toMatchObject({ status: 'unresolved', reason: 'certificate-rejected', safeInputVoltageRms: null })
  const accepted = api.analyzeBandOutputLimit(sealed, request).certificate!
  const silent = { ...request, filter: { digital: { sampleRateHz: 1000,
    stages: [{ kind: 'biquad' as const, b0: 0, b1: 0, b2: 0, a1: 0, a2: 0 }] } } }
  const key = (input: api.CircuitInput, options: api.BandOutputLimitOptions) =>
    JSON.stringify([input, options], (_, value) => {
      if (value === Infinity) return '+Infinity'
      if (value && typeof value === 'object' && !Array.isArray(value))
        return Object.fromEntries(Object.keys(value).sort().map((field) => [field, value[field]]))
      return value
    })
  expect(api.verifyBandOutputCertificate(sealed, silent, {
    ...accepted, request: key(sealed, silent),
  })).toBe(false)
  const distributed = { ...vented, port: { quality: 8, ductPath: {
    count: 1, inletCorrectionMeters: 0, outletCorrectionMeters: 0,
    sections: [{ lengthMeters: 0.3, inletAreaSquareMeters: 0.01,
      outletAreaSquareMeters: 0.01, profile: 'straight' as const }],
  } } }
  const withMach = { ...request, maxPortMach: 0.08 }
  expect(api.verifyBandOutputCertificate(distributed, withMach, {
    ...accepted, request: key(distributed, withMach),
  })).toBe(false)
})

it('reports which spans still need refinement and keeps any safe bound', () => {
  const settings = { ...band, maxAmplifierVoltageRms: 20, maxSplits: 1,
    filter: { highpassHz: 30, lowpassHz: 60 } }
  const result = api.analyzeBandOutputLimit(sealed, settings)
  expect(result).toMatchObject({ status: 'unresolved', reason: 'subdivision-budget', splits: 1 })
  expect(result.unresolvedIntervals).toEqual([{ minHz: 15, maxHz: 157.5 }])
  expect(result.safeInputVoltageRms).toBeLessThan(result.upperInputVoltageRms!)
  expect(result.errorBoundDb).toBeGreaterThan(0.1)
  // A loose enclosure can include a zero denominator even when a sampled
  // witness gives a finite upper voltage.
  expect(api.analyzeBandOutputLimit(sealed, { ...band, xmaxMeters: 0.01, maxSplits: 0 }))
    .toMatchObject({ status: 'unresolved', safeInputVoltageRms: null,
      upperInputVoltageRms: expect.any(Number), unresolvedIntervals: [band] })
})

it('checks partial voltage bounds independently when refinement stops', () => {
  const settings = { minHz: 15, maxHz: 120, toleranceDb: 1e-8, maxAmplifierVoltageRms: 20,
    filter: { highpassHz: 30, lowpassHz: 60 } }
  // The product of these two LR4 gains peaks at the geometric mean.
  const ceiling = 20 * (1 + (30 / 60) ** 2) ** 2
  for (const maxSplits of [0, 2]) {
    const result = api.analyzeBandOutputLimit(sealed, { ...settings, maxSplits })
    expect(result).toMatchObject({ status: 'unresolved', reason: 'subdivision-budget', splits: maxSplits })
    expect(result.safeInputVoltageRms!).toBeLessThanOrEqual(ceiling)
    expect(result.upperInputVoltageRms!).toBeGreaterThanOrEqual(ceiling)
    expect(result.errorBoundDb!).toBeGreaterThanOrEqual(20 * Math.log10(ceiling / result.safeInputVoltageRms!))
  }

  // At this voltage rating the fixed dyadic grid cannot establish a positive
  // lower bound on utilization, even though binary64 proposes both bounds.
  const limits = { maxAmplifierVoltageRms: 1e100, toleranceDb: 1e-20, maxSplits: 0 }
  for (const [maxHz, reason] of [[2, 'subdivision-budget'], [1 + Number.EPSILON, 'frequency-resolution']] as const) {
    expect(api.analyzeBandOutputLimit(sealed, { minHz: 1, maxHz, ...limits }))
      .toMatchObject({ status: 'unresolved', reason, safeInputVoltageRms: null,
        upperInputVoltageRms: null, errorBoundDb: null })
  }
})

it('replays a band certificate for conical and exponential sections with both mouth corrections', () => {
  const input = { ...vented, port: { quality: 8, ductPath: {
    count: 2, inletCorrectionMeters: 0.012, outletCorrectionMeters: 0.008,
    junctionInertanceLengthsMeters: [-0.003],
    inertanceFactor: 1.08, complianceFactor: 0.97,
    sections: [
      { lengthMeters: 0.3, inletAreaSquareMeters: 0.005, outletAreaSquareMeters: 0.009,
        profile: 'conical' as const },
      { lengthMeters: 0.2, inletAreaSquareMeters: 0.009, outletAreaSquareMeters: 0.015,
        profile: 'exponential' as const },
    ],
  } } }
  const options = { minHz: 45, maxHz: 46, maxPortMach: 0.008 }
  const result = api.analyzeBandOutputLimit(input, options)
  expect(result.status).toBe('resolved')
  expect(api.verifyBandOutputCertificate(input, options, result.certificate!)).toBe(true)
})

it('encloses a lossless uniform duct including its first impedance pole', () => {
  const duct = { ...vented, port: { quality: Infinity, ductPath: {
    count: 1, inletCorrectionMeters: 0, outletCorrectionMeters: 0,
    sections: [{ lengthMeters: 0.3, inletAreaSquareMeters: 0.01,
      outletAreaSquareMeters: 0.01, profile: 'straight' as const }],
  } } }
  const options = { minHz: 250, maxHz: 310, maxPortMach: 0.004, xmaxMeters: 0.008 }
  const result = api.analyzeBandOutputLimit(duct, options)
  const { densityKgM3: rho, soundSpeedMps: c } = duct.medium
  let maxUsage = 0
  for (let i = 0; i <= 6000; i += 1) {
    const frequency = options.minHz + i * 0.01
    const phase = 2 * Math.PI * frequency * 0.3 / c
    maxUsage = Math.max(maxUsage, referenceUsage(duct, options, frequency, {
      mass: rho * 0.3 / 0.01,
      reactance: rho * c / 0.01 * Math.tan(phase),
      peak: 1 / (0.01 * Math.abs(Math.cos(phase))),
    }))
  }
  expect(result.status).toBe('resolved')
  expect(result.safeInputVoltageRms).toBeLessThanOrEqual(1 / maxUsage)
  expect(result.upperInputVoltageRms!).toBeGreaterThanOrEqual(1 / maxUsage - 1e-6)
  expect(result.errorBoundDb).toBeLessThanOrEqual(0.1)
  expect(api.verifyBandOutputCertificate(duct, options, result.certificate!)).toBe(true)
  expect(api.analyzeBandOutputLimit(duct, { ...options, maxSplits: 0 }))
    .toMatchObject({ status: 'unresolved', reason: 'subdivision-budget' })
  expect(api.analyzeBandOutputLimit(duct, { ...band, maxAmplifierVoltageRms: 20 }).status).toBe('resolved')
  expect(api.analyzeBandOutputLimit(duct, { minHz: 250, maxHz: 310, maxAmplifierCurrentRms: 1 }).status)
    .toBe('resolved')
})

it('encloses the interior airspeed of a multi-section tapered duct over a band', () => {
  const throat = 0.005
  const mouth = 0.04
  const path: api.DuctPath = {
    count: 2, inletCorrectionMeters: 0.012, outletCorrectionMeters: 0.008,
    junctionInertanceLengthsMeters: [-0.003],
    inertanceFactor: 1.08, complianceFactor: 0.97,
    sections: [
      { lengthMeters: 0.6, inletAreaSquareMeters: throat, outletAreaSquareMeters: throat, profile: 'straight' },
      { lengthMeters: 0.3, inletAreaSquareMeters: throat, outletAreaSquareMeters: mouth, profile: 'exponential' },
    ],
  }
  const input = { ...vented, medium: { soundSpeedMps: 343, densityKgM3: 1.2 },
    port: { quality: 8, ductPath: path } }
  const options = { minHz: 275, maxHz: 320, maxPortMach: 0.008 }
  const mass = odeFixture(path, 0.0001, 256).reactance / (2 * Math.PI * 0.0001 * path.count)
  let maxUsage = 0
  let endpointUsage = 0
  let peakHz = options.minHz
  const sample = (hz: number, steps: number) => {
    const response = odeFixture(path, hz, steps)
    const reactance = response.reactance / path.count
    const usage = referenceUsage(input, options, hz, { mass, reactance, peak: response.peak })
    if (usage > maxUsage) [maxUsage, peakHz] = [usage, hz]
    const peak = Math.max(1 / throat, Math.abs(response.ratio) / mouth) / path.count
    endpointUsage = Math.max(endpointUsage, referenceUsage(input, options, hz, { mass, reactance, peak }))
  }
  for (let i = 0; i <= 450; i += 1) sample(options.minHz + i / 10, 256)
  const fineStart = Math.max(options.minHz, peakHz - 0.1)
  const fineEnd = Math.min(options.maxHz, peakHz + 0.1)
  for (let i = 0; i <= 40; i += 1) sample(fineStart + (fineEnd - fineStart) * i / 40, 4096)
  expect(maxUsage).toBeGreaterThan(endpointUsage * 1.02)
  const result = api.analyzeBandOutputLimit(input, options)
  expect(result.status).toBe('resolved')
  expect(result.safeInputVoltageRms).toBeLessThanOrEqual(1 / maxUsage)
  expect(result.upperInputVoltageRms!).toBeGreaterThanOrEqual(1 / maxUsage - 1e-4)
  expect(result.errorBoundDb).toBeLessThanOrEqual(0.1)
  expect(api.verifyBandOutputCertificate(input, options, result.certificate!)).toBe(true)
  const endpointCeiling = 1 / endpointUsage
  expect(api.verifyBandOutputCertificate(input, options, {
    ...result.certificate!, safeInputVoltageRms: endpointCeiling, upperInputVoltageRms: endpointCeiling,
  })).toBe(false)
}, 15_000)

it('identifies unsupported ranges and inactive limits', () => {
  expect(api.analyzeBandOutputLimit(sealed, { ...band, maxPortMach: 0.1 }).status).toBe('unbounded')
  expect(api.analyzeBandOutputLimit(sealed, { ...band, xmaxMeters: 0.01, maxPortMach: 0.1 }).status).toBe('resolved')
  expect(api.analyzeBandOutputLimit(sealed, { ...band, xmaxMeters: 0.01,
    filter: { digital: { sampleRateHz: 1000,
      stages: [{ kind: 'biquad', b0: 0, b1: 0, b2: 0, a1: 0, a2: 0 }] } },
  }).status).toBe('unbounded')
  expect(api.analyzeBandOutputLimit(sealed, {
    ...band, maxAmplifierVoltageRms: 10, filter: { gainDb: 1e8 },
  })).toMatchObject({ status: 'unresolved', reason: 'numeric-range' })
  expect(api.analyzeBandOutputLimit(sealed, { ...band, maxAmplifierVoltageRms: Number.MIN_VALUE }))
    .toMatchObject({ status: 'unresolved', reason: 'numeric-range' })
  expect(api.analyzeBandOutputLimit(sealed, {
    minHz: 1, maxHz: 1 + Number.EPSILON, maxAmplifierVoltageRms: 10, toleranceDb: 1e-20,
  })).toMatchObject({ status: 'unresolved', reason: 'frequency-resolution' })
})

it('validates the band, enabled limits, and filter settings', () => {
  const voltage = { ...band, maxAmplifierVoltageRms: 20 }
  for (const update of [
    { minHz: 0 }, { maxHz: Infinity }, { maxHz: 10 }, { toleranceDb: 0 },
    { maxSplits: 0.5 }, { maxSplits: -1 }, { maxSplits: 8193 },
  ]) expect(() => api.analyzeBandOutputLimit(sealed, { ...voltage, ...update })).toThrow(/Band requires/)
  expect(() => api.analyzeBandOutputLimit(sealed, { ...voltage, maxRadiatorExcursionPeakM: 1 })).toThrow(/passive radiator/)
  expect(() => api.analyzeBandOutputLimit(sealed, { ...voltage, xmaxMeters: NaN })).toThrow(/limits/)
  expect(() => api.analyzeBandOutputLimit(sealed, { ...voltage, ratedPowerWattsPerDriver: -1 })).toThrow(/limits/)
  expect(() => api.analyzeBandOutputLimit(sealed, { ...voltage, maxAmplifierCurrentRms: 0 })).toThrow(/limits/)
  for (const filter of [
    { highpassType: 'bad' as 'BW24' }, { gainDb: Infinity }, { delaySeconds: -1 }, { delaySeconds: NaN },
    { highpassHz: Infinity }, { lowpassHz: 0 },
  ]) expect(() => api.analyzeBandOutputLimit(sealed, { ...voltage, filter })).toThrow(/filter settings/)
  for (const sampleRateHz of [Infinity, 0, 400])
    expect(() => api.analyzeBandOutputLimit(sealed, {
      ...voltage, filter: { digital: { sampleRateHz, stages: [] } },
    })).toThrow(/Nyquist/)
  expect(() => api.analyzeBandOutputLimit(sealed, {
    ...voltage, minHz: Number.MIN_VALUE, maxHz: 2 * Number.MIN_VALUE,
    filter: { digital: { sampleRateHz: 3 * Number.MIN_VALUE, stages: [] } },
  })).toThrow(/Nyquist/)
})
