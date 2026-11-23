import { describe, expect, it } from 'vitest'
import { analyzeFilteredVoltageLimit, analyzeOperatingDrive } from './operating'
import { lr24AttenuationDb } from './filters'

const source = {
  perDriverReferenceVoltage: 2,
  seriesDriversPerString: 1,
  parallelStrings: 1,
  dcResistancePerDriver: 5,
  xmaxMeters: 0.008,
  ratedPowerWattsPerDriver: 800,
  points: [
    {
      frequency: 14,
      coneExcursionMeters: 0.034,
      portVelocity: 17,
      portMach: 0.05,
      impedanceOhms: 10,
      splDb: 90,
    },
    {
      frequency: 28,
      coneExcursionMeters: 0.002,
      portVelocity: 2,
      portMach: 0.006,
      impedanceOhms: 20,
      splDb: 94,
    },
    {
      frequency: 100,
      coneExcursionMeters: 0.0001,
      portVelocity: 0.1,
      portMach: 0.0003,
      impedanceOhms: 40,
      splDb: 92,
    },
  ],
}

describe('operating analysis', () => {
  it.each([
    [1, 6],
    [2, 3],
    [3, 2],
    [6, 1],
  ])(
    'keeps per-driver excursion and copper heat invariant across %s-series/%s-parallel wiring',
    (series, parallel) => {
      const array = {
        ...source,
        seriesDriversPerString: series,
        parallelStrings: parallel,
        points: source.points.map((point) => ({
          ...point,
          impedanceOhms: (point.impedanceOhms * series) / parallel,
        })),
      }
      const before = {
        ...array,
        points: array.points.map((point) => ({ ...point })),
      }
      const result = analyzeOperatingDrive(array, 800, 8, () => 0)
      expect(result.perDriverVoltage).toBe(80)
      expect(result.amplifierVoltage).toBe(80 * series)
      expect(result.nominalTotalWatts).toBe(800 * 6)
      expect(result.excursion.value).toBeCloseTo((0.034 * 80) / 2, 12)
      expect(result.coilLossWattsPerDriver.value).toBeCloseTo(
        (80 / 10) ** 2 * 5,
        12,
      )
      expect(result.coilLossWattsPerDriver.frequency).toBe(14)
      expect(array).toEqual(before)
    },
  )

  it('selects port Mach when excursion and thermal ratings are unavailable', () => {
    const result = analyzeFilteredVoltageLimit(
      {
        ...source,
        xmaxMeters: 0,
        ratedPowerWattsPerDriver: 0,
        points: source.points.map(({ splDb: _splDb, ...point }) => point),
      },
      { maxPortMach: 0.1 },
    )
    expect(result.limitingFactor).toBe('port-mach')
    expect(result.safeAmplifierVoltage).toBeCloseTo((2 * 0.1) / 0.05, 12)
    expect(result.limitingFrequency).toBe(14)
    expect(result.safeSplDbAtLimitingFrequency).toBeNull()
    expect(result.candidates.excursion).toBeNull()
    expect(result.candidates['thermal-proxy']).toBeNull()
  })

  it.each(['zero response', 'zero filter gain'])(
    'does not invent a finite voltage limit for %s',
    (condition) => {
      const silent = {
        ...source,
        ratedPowerWattsPerDriver: 0,
        points:
          condition === 'zero response'
            ? source.points.map((point) => ({
                ...point,
                coneExcursionMeters: 0,
                portMach: 0,
              }))
            : source.points,
      }
      expect(() =>
        analyzeFilteredVoltageLimit(silent, {
          maxPortMach: 0.1,
          ...(condition === 'zero filter gain'
            ? { filter: { gainDb: -10000 } }
            : {}),
        }),
      ).toThrow(/do not produce a finite voltage limit/i)
    },
  )

  it('returns unknown rating ratios instead of manufacturing limits from absent ratings', () => {
    const result = analyzeOperatingDrive(
      { ...source, xmaxMeters: 0, ratedPowerWattsPerDriver: 0 },
      800,
      8,
      () => 0,
    )
    expect(result.excursionRatio).toBeNull()
    expect(result.nominalRatingRatio).toBeNull()
    expect(result.excursion.value).toBeCloseTo(1.36)
  })

  it('rejects total array power overflow even when per-driver drive remains finite', () => {
    expect(() =>
      analyzeOperatingDrive(
        { ...source, seriesDriversPerString: 2, parallelStrings: 2 },
        1e308,
        1e-308,
        () => 0,
      ),
    ).toThrow(/numeric range/i)
  })

  it('derives the source amplifier reference when the option is omitted', () => {
    const explicit = analyzeFilteredVoltageLimit(source, {
      referenceAmplifierVoltage: 2,
      maxPortMach: 0.1,
      filter: { highpassHz: 28, delaySeconds: 0.02 },
    })
    const derived = analyzeFilteredVoltageLimit(source, {
      maxPortMach: 0.1,
      filter: { highpassHz: 28, delaySeconds: 0.02 },
    })
    expect(derived).toEqual(explicit)
  })

  it('preserves the web operating scenario calculations', () => {
    const result = analyzeOperatingDrive(source, 800, 8, (frequency) =>
      lr24AttenuationDb(frequency, 28, 'highpass'),
    )
    expect(result.perDriverVoltage).toBe(80)
    expect(result.excursion.value).toBeCloseTo(0.08, 10)
    expect(result.excursion.frequency).toBe(14)
    expect(result.coilLossWattsPerDriver.value).toBeCloseTo(20)
    expect(result.coilLossWattsPerDriver.frequency).toBe(28)
  })

  it('finds a sub-tuning excursion limit across every filtered sample', () => {
    const unfiltered = analyzeFilteredVoltageLimit(source, {
      referenceAmplifierVoltage: 2,
      maxPortMach: 0.1,
    })
    const filtered = analyzeFilteredVoltageLimit(source, {
      referenceAmplifierVoltage: 2,
      maxPortMach: 0.1,
      filter: { highpassHz: 28 },
    })
    expect(unfiltered.limitingFactor).toBe('excursion')
    expect(unfiltered.limitingFrequency).toBe(14)
    expect(unfiltered.safeAmplifierVoltage).toBeCloseTo((2 * 0.008) / 0.034)
    expect(filtered.limitingFactor).toBe('excursion')
    expect(filtered.limitingFrequency).toBe(14)
    expect(filtered.safeAmplifierVoltage).toBeCloseTo(8)
    expect(filtered.safeAmplifierVoltage).toBeGreaterThan(
      unfiltered.safeAmplifierVoltage,
    )
    expect(filtered.evaluatedFrequencyRange).toEqual({ minHz: 14, maxHz: 100 })
  })

  it('uses array current and I squared Re for the thermal proxy', () => {
    const thermal = analyzeFilteredVoltageLimit(
      {
        ...source,
        xmaxMeters: 1,
        ratedPowerWattsPerDriver: 20,
        seriesDriversPerString: 3,
        parallelStrings: 2,
        points: source.points.map((point) => ({ ...point, impedanceOhms: 15 })),
      },
      { referenceAmplifierVoltage: 6, maxPortMach: 1 },
    )
    // Per-driver current = 6 V / 15 ohm / 2 strings = 0.2 A.
    expect(thermal.atReference.maxCoilLossWattsPerDriver.value).toBeCloseTo(0.2)
    expect(thermal.safeAmplifierVoltage).toBeCloseTo(60)
    expect(thermal.limitingFactor).toBe('thermal-proxy')
    expect(thermal.metadata.thermalBasis).toBe('steady-state-i2r-proxy')
    expect(thermal.metadata.nominalWattsAreCoilHeat).toBe(false)
  })

  it('reports SPL at the safe voltage when samples include it', () => {
    const result = analyzeFilteredVoltageLimit(source, {
      referenceAmplifierVoltage: 2,
      maxPortMach: 0.1,
    })
    expect(result.safeSplDbAtLimitingFrequency).toBeCloseTo(
      90 + 20 * Math.log10(result.safeAmplifierVoltage / 2),
    )
  })

  it('rejects empty, unordered, nonfinite, and incomplete constraint data', () => {
    expect(() =>
      analyzeFilteredVoltageLimit(
        { ...source, points: [] },
        { referenceAmplifierVoltage: 2 },
      ),
    ).toThrow()
    expect(() =>
      analyzeFilteredVoltageLimit(
        { ...source, points: [source.points[1]!, source.points[0]!] },
        { referenceAmplifierVoltage: 2 },
      ),
    ).toThrow()
    expect(() =>
      analyzeFilteredVoltageLimit(
        { ...source, points: [{ ...source.points[0]!, portMach: NaN }] },
        { referenceAmplifierVoltage: 2 },
      ),
    ).toThrow()
    expect(() =>
      analyzeFilteredVoltageLimit(
        { ...source, xmaxMeters: 0, ratedPowerWattsPerDriver: 0 },
        { referenceAmplifierVoltage: 2 },
      ),
    ).toThrow(/constraint/i)
    expect(() =>
      analyzeFilteredVoltageLimit(source, {
        referenceAmplifierVoltage: Infinity,
      }),
    ).toThrow()
    expect(() =>
      analyzeFilteredVoltageLimit(source, { referenceAmplifierVoltage: 3 }),
    ).toThrow(/reference/i)
    expect(() =>
      analyzeFilteredVoltageLimit(source, {
        referenceAmplifierVoltage: 2,
        filter: { gainDb: 6200 },
      }),
    ).toThrow(/numeric range/i)
  })
})
