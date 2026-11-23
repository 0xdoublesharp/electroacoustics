import fc from 'fast-check'
import { expect, inject, it } from 'vitest'
import * as api from './index'
import { circuitFixture } from './testFixtures'

declare module 'vitest' {
  interface ProvidedContext {
    fuzz: Pick<fc.Parameters<unknown>, 'numRuns' | 'seed' | 'path' | 'endOnFailure'>
  }
}

function invariant<T>(
  name: string,
  inputs: fc.Arbitrary<T>,
  check: (input: T) => void,
) {
  it(name, () => fc.assert(fc.property(inputs, check), inject('fuzz')))
}

function expectNear(actual: number, expected: number, label: string) {
  expect(Math.abs(actual - expected), label).toBeLessThanOrEqual(
    1e-12 + 1e-9 * Math.abs(expected),
  )
}

function decimal(min: number, max: number, divisor: number) {
  return fc.integer({ min, max }).map((value) => value / divisor)
}

const quality = fc.oneof(fc.constant(Infinity), decimal(10, 500, 10))
const duct = fc
  .record({
    profile: fc.constantFrom('conical' as const, 'exponential' as const),
    lengthMeters: decimal(10, 90, 100),
    inletAreaSquareMeters: decimal(20, 500, 10_000),
    areaRatio: decimal(25, 400, 100),
    count: fc.integer({ min: 1, max: 6 }),
    inletCorrectionMeters: decimal(0, 4, 1000),
    outletCorrectionMeters: decimal(0, 4, 1000),
  })
  .map(
    ({ count, inletCorrectionMeters, outletCorrectionMeters, areaRatio, ...section }): api.DuctPath => ({
      count,
      inletCorrectionMeters,
      outletCorrectionMeters,
      sections: [
        {
          ...section,
          outletAreaSquareMeters: section.inletAreaSquareMeters * areaRatio,
        },
      ],
    }),
  )

const cabinet = fc.record({
  driver: fc.record({
    fsHz: fc.integer({ min: 15, max: 80 }),
    vasM3: decimal(10, 250, 1000),
    qes: decimal(20, 120, 100),
    qms: decimal(10, 150, 10),
    reOhms: decimal(20, 130, 10),
    leHenries: decimal(0, 500, 100_000),
    sdM2: decimal(50, 1500, 10_000),
  }),
  volumeM3: decimal(10, 300, 1000),
  voltageRms: decimal(10, 800, 10),
  medium: fc.record({
    densityKgM3: decimal(95, 130, 100),
    soundSpeedMps: fc.integer({ min: 315, max: 365 }),
  }),
  leakageQuality: quality,
  absorptionQuality: quality,
})

invariant(
  'circuit power is passive and rewiring at equal per-driver voltage preserves drive',
  fc.record({
    cabinet,
    duct,
    portModel: fc.constantFrom('sealed', 'lumped', 'distributed'),
    portQuality: quality,
    series: fc.integer({ min: 2, max: 4 }),
    strings: fc.integer({ min: 1, max: 4 }),
    frequency: decimal(50, 2500, 10),
  }),
  ({ cabinet, duct, portModel, portQuality, series, strings, frequency }) => {
    const section = duct.sections[0]!
    const ports = {
      sealed: {},
      lumped: {
        port: {
          quality: portQuality,
          areaM2: section.inletAreaSquareMeters * duct.count,
          effectiveLengthM: section.lengthMeters,
        },
      },
      distributed: { port: { quality: portQuality, ductPath: duct } },
    }
    const quantity = series * strings
    const input = { ...cabinet, ...ports[portModel], quantity }
    const parallel = api.createCircuit(input)(frequency)
    const wired = api.createCircuit({
      ...input,
      seriesDrivers: series,
      voltageRms: input.voltageRms * series,
    })(frequency)

    const dcResistance = input.driver.reOhms / quantity
    expect(parallel.impedanceOhms.re).toBeGreaterThanOrEqual(dcResistance - 1e-10)
    expect(parallel.coilLossWatts).toBeGreaterThan(0)
    expect(parallel.realInputPowerWatts).toBeGreaterThanOrEqual(
      parallel.coilLossWatts * (1 - 1e-9),
    )
    expect(parallel.realInputPowerWatts).toBeLessThanOrEqual(
      input.voltageRms * api.magnitude(parallel.currentAmps) * (1 + 1e-9),
    )
    expectNear(wired.impedanceOhms.re, parallel.impedanceOhms.re * series ** 2, 'resistance')
    expectNear(wired.impedanceOhms.im, parallel.impedanceOhms.im * series ** 2, 'reactance')
    expectNear(wired.realInputPowerWatts, parallel.realInputPowerWatts, 'real power')
    expectNear(wired.coilLossWatts, parallel.coilLossWatts, 'copper loss')
    expectNear(wired.pressurePa.re, parallel.pressurePa.re, 'in-phase pressure')
    expectNear(wired.pressurePa.im, parallel.pressurePa.im, 'quadrature pressure')
    expectNear(wired.portMach, parallel.portMach, 'port Mach')
  },
)

invariant(
  'fractional subdivision preserves taper inertance and complex transfer',
  fc.record({
    duct,
    fraction: decimal(10, 90, 100),
    phase: decimal(5, 90, 100),
  }),
  ({ duct, fraction, phase }) => {
    const section = duct.sections[0]!
    const inlet = section.inletAreaSquareMeters
    const outlet = section.outletAreaSquareMeters
    // An exponential taper interpolates log area, and a cone interpolates radius.
    const middle = section.profile === 'exponential'
      ? inlet * (outlet / inlet) ** fraction
      : ((1 - fraction) * Math.sqrt(inlet) + fraction * Math.sqrt(outlet)) ** 2
    const split = {
      ...duct,
      sections: [
        {
          ...section,
          lengthMeters: section.lengthMeters * fraction,
          outletAreaSquareMeters: middle,
        },
        {
          ...section,
          lengthMeters: section.lengthMeters * (1 - fraction),
          inletAreaSquareMeters: middle,
        },
      ],
    }
    const speed = 343
    const frequency = (phase * speed) / (2 * Math.PI * section.lengthMeters)
    const whole = api.ductPathImpedance(duct, frequency, speed, 1.2, 12)
    const divided = api.ductPathImpedance(split, frequency, speed, 1.2, 12)
    expectNear(api.ductPathEquivalentLength(split), api.ductPathEquivalentLength(duct), 'inertance length')
    expect(divided.impedance.re).toBe(12)
    expectNear(divided.impedance.im, whole.impedance.im, 'duct reactance')
    expectNear(divided.mouthFlowRatio.re, whole.mouthFlowRatio.re, 'mouth flow ratio')
  },
)

invariant(
  'straight-duct tuning cancels cavity admittance below the first pole',
  fc.record({
    length: decimal(8, 100, 100),
    area: decimal(20, 500, 10_000),
    volume: decimal(10, 300, 1000),
    count: fc.integer({ min: 1, max: 8 }),
    speed: fc.integer({ min: 315, max: 365 }),
  }),
  ({ length, area, volume, count, speed }) => {
    const path: api.DuctPath = {
      count,
      inletCorrectionMeters: 0,
      outletCorrectionMeters: 0,
      sections: [{
        profile: 'straight',
        lengthMeters: length,
        inletAreaSquareMeters: area,
        outletAreaSquareMeters: area,
      }],
    }
    const tuning = api.ductPathTuning(path, volume, speed)
    const phase = (2 * Math.PI * tuning * length) / speed
    expect(phase).toBeGreaterThan(0)
    expect(phase).toBeLessThan(Math.PI / 2)
    // Open-tube reactance is rho*c*tan(kL)/(N*A), and cavity admittance is omega*V/(rho*c²).
    expectNear((phase * volume * Math.tan(phase)) / (length * count * area), 1, 'admittance cancellation')
    expect(api.ductPathTuning(path, 2 * volume, speed)).toBeLessThan(tuning)
  },
)

invariant(
  'filter-chain voltage magnitude follows the stage responses and gain',
  fc.record({
    frequency: fc.integer({ min: 10, max: 1000 }),
    highpassHz: fc.integer({ min: 10, max: 1000 }),
    lowpassHz: fc.integer({ min: 10, max: 1000 }),
    highpassType: fc.constantFrom('LR24' as const, 'BW24' as const),
    gainDb: decimal(-300, 300, 10),
    delaySeconds: decimal(0, 200, 1000),
  }),
  ({ frequency, ...filter }) => {
    const highpassRatio = filter.highpassHz / frequency
    const highpassGain = filter.highpassType === 'BW24'
      ? 1 / Math.sqrt(1 + highpassRatio ** 8)
      : 1 / (1 + highpassRatio ** 4)
    const lowpassGain = 1 / (1 + (frequency / filter.lowpassHz) ** 4)
    const transfer = api.composeFilters(frequency, filter)
    expectNear(
      api.magnitude(transfer) / (highpassGain * lowpassGain),
      10 ** (filter.gainDb / 20),
      'filter voltage gain',
    )
    expectNear(
      api.lr24AttenuationDb(frequency, filter.lowpassHz, 'lowpass'),
      20 * Math.log10(lowpassGain),
      'low-pass attenuation',
    )
  },
)

invariant(
  'adaptive sampling retains its in-band landmarks and every evaluated point within budget',
  fc.record({
    minHz: fc.integer({ min: 1, max: 100 }),
    span: fc.integer({ min: 10, max: 1000 }),
    initialPoints: fc.integer({ min: 2, max: 6 }),
    maxPoints: fc.integer({ min: 8, max: 64 }),
    relativeTolerance: decimal(1, 800, 1000),
  }),
  ({ span, ...options }) => {
    const { minHz, maxPoints } = options
    const maxHz = minHz + span
    const landmark = minHz + 0.23 * span
    const reserved = minHz + 0.71 * span
    const evaluated: number[] = []
    const result = api.sampleAdaptive(
      (frequency) => {
        evaluated.push(frequency)
        return 1 / (1 + ((frequency - landmark) / (span * 0.01)) ** 2)
      },
      (value) => [value],
      {
        ...options,
        maxHz,
        landmarksHz: [landmark, maxHz + 1, landmark],
        reservedLandmarksHz: [reserved],
      },
    )
    const frequencies = result.samples.map((point) => point.frequency)
    expect(evaluated.length).toBeLessThanOrEqual(maxPoints)
    expect(result.diagnostics.evaluations).toBe(evaluated.length)
    expect(frequencies).toEqual(evaluated.sort((a, b) => a - b))
    expect(new Set(frequencies).size).toBe(frequencies.length)
    expect(frequencies[0]).toBe(minHz)
    expect(frequencies.at(-1)).toBe(maxHz)
    expect(frequencies).toContain(landmark)
    expect(frequencies).toContain(reserved)
    expect(result.diagnostics.converged).toBe(result.diagnostics.unresolvedIntervals === 0)
  },
)

invariant(
  'a flat sweep gain scales RMS quantities linearly and power quadratically',
  fc.record({ cabinet, gainDb: decimal(-180, 180, 10) }),
  ({ cabinet, gainDb }) => {
    const evaluate = api.createCircuit(cabinet)
    const gain = 10 ** (gainDb / 20)
    const { points } = api.sweepCircuit(cabinet, {
      minHz: 10,
      maxHz: 220,
      initialPoints: 5,
      maxPoints: 24,
      filter: { gainDb },
    })
    for (const point of points) {
      const raw = evaluate(point.frequency)
      expect(point.impedanceOhms).toEqual(raw.impedanceOhms)
      expectNear(point.splDb - raw.splDb, gainDb, 'SPL change')
      expectNear(point.coneExcursionPeakM, raw.coneExcursionPeakM * gain, 'peak excursion')
      expectNear(point.currentAmps.re, raw.currentAmps.re * gain, 'in-phase current')
      expectNear(point.realInputPowerWatts, raw.realInputPowerWatts * gain ** 2, 'real power')
    }
  },
)

const operatingSample = fc.record({
  coneExcursionMeters: decimal(1, 400, 100_000),
  portMach: decimal(1, 500, 10_000),
  impedanceOhms: decimal(20, 400, 10),
})

invariant(
  'the reported amplifier voltage obeys every sampled constraint and binds at the reported frequency',
  fc.record({
    perDriverReferenceVoltage: decimal(10, 130, 10),
    seriesDriversPerString: fc.integer({ min: 1, max: 5 }),
    parallelStrings: fc.integer({ min: 1, max: 5 }),
    dcResistancePerDriver: decimal(20, 120, 10),
    xmaxMeters: decimal(1, 15, 1000),
    ratedPowerWattsPerDriver: fc.integer({ min: 10, max: 1000 }),
    maxPortMach: decimal(1, 20, 100),
    gainDb: decimal(-180, 180, 10),
    rows: fc.array(operatingSample, { minLength: 1, maxLength: 8 }),
  }),
  ({ rows, maxPortMach, gainDb, ...ratings }) => {
    const points = rows.map((row, index) => ({
      ...row,
      frequency: 10 + index * 20,
      portVelocity: row.portMach * 343,
    }))
    const result = api.analyzeFilteredVoltageLimit(
      { ...ratings, points },
      { maxPortMach, filter: { gainDb } },
    )
    const filteredVoltage = result.safeAmplifierVoltage * 10 ** (gainDb / 20)
    const reference = ratings.perDriverReferenceVoltage * ratings.seriesDriversPerString
    for (const point of points) {
      const scale = filteredVoltage / reference
      const perDriverCurrent =
        filteredVoltage / (point.impedanceOhms * ratings.parallelStrings)
      const ratios = {
        excursion: (point.coneExcursionMeters * scale) / ratings.xmaxMeters,
        'port-mach': (point.portMach * scale) / maxPortMach,
        'thermal-proxy':
          (perDriverCurrent ** 2 * ratings.dcResistancePerDriver) /
          ratings.ratedPowerWattsPerDriver,
      }
      expect(Math.max(...Object.values(ratios))).toBeLessThanOrEqual(1 + 1e-9)
      if (point.frequency === result.limitingFrequency)
        expectNear(ratios[result.limitingFactor], 1, 'binding constraint')
    }
    expect(points.map((point) => point.frequency)).toContain(result.limitingFrequency)
  },
)

invariant(
  'sensitivity uses a common grid and encloses all sampled SPL values',
  fc.record({
    cabinet,
    scales: fc.array(decimal(5, 20, 10), { minLength: 1, maxLength: 4 }),
    minHz: fc.integer({ min: 5, max: 80 }),
    span: fc.integer({ min: 20, max: 200 }),
  }),
  ({ cabinet, scales, minHz, span }) => {
    const volumes = scales.map((scale) => cabinet.volumeM3 * scale)
    const maxHz = minHz + span
    const result = api.analyzeSensitivity(
      cabinet,
      [{ parameter: 'volumeM3', values: volumes }],
      { minHz, maxHz, points: 7 },
    )
    const frequencies = result.baseline.points.map((point) => point.frequency)
    expect(frequencies[0]).toBe(minHz)
    expect(frequencies.at(-1)).toBe(maxHz)
    expect(result.scenarios).toHaveLength(volumes.length)
    for (const [i, scenario] of result.scenarios.entries()) {
      const volume = volumes[i]!
      expect(scenario.points.map((point) => point.frequency)).toEqual(frequencies)
      expectNear(
        scenario.metrics.referenceResonanceHz,
        cabinet.driver.fsHz * Math.sqrt(1 + cabinet.driver.vasM3 / volume),
        'sealed resonance',
      )
    }
    for (const [i, envelope] of result.envelope.entries()) {
      const levels = [result.baseline, ...result.scenarios].map((row) => row.points[i]!.splDb)
      expect(envelope).toEqual({
        frequency: frequencies[i],
        minSplDb: Math.min(...levels),
        maxSplDb: Math.max(...levels),
      })
    }
  },
)

invariant(
  'frequency entry points reject nonpositive and nonfinite inputs before evaluation',
  fc.oneof(
    fc.constantFrom(0, -0, NaN, Infinity, -Infinity),
    fc.double({ min: -Number.MAX_VALUE, max: -Number.MIN_VALUE, noNaN: true }),
  ),
  (frequency) => {
    expect(() => api.createCircuit(circuitFixture)(frequency)).toThrow(RangeError)
    expect(() => api.composeFilters(frequency)).toThrow(RangeError)
    let evaluations = 0
    expect(() =>
      api.sampleAdaptive(
        (value) => {
          evaluations++
          return value
        },
        (value) => [value],
        { minHz: frequency, maxHz: 200 },
      ),
    ).toThrow(RangeError)
    expect(evaluations).toBe(0)
  },
)
