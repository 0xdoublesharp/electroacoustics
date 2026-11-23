import { describe, expect, it } from 'vitest'
import * as api from './index'
import { circuitFixture } from './testFixtures'

describe('explicit sensitivity scenarios', () => {
  it('exports scenario analysis with no inferred probability distribution', () => {
    expect(api.analyzeSensitivity).toBeTypeOf('function')
  })
  it('matches the closed-form sealed resonance shift and ranks measured metric changes', () => {
    const result = api.analyzeSensitivity(
      circuitFixture,
      [
        { parameter: 'volumeM3', values: [0.035, 0.14] },
        { parameter: 'driver.fsHz', values: [25] },
      ],
      { minHz: 10, maxHz: 150, points: 121 },
    )
    expect(result.metadata.interpretation).toBe(
      'one-at-a-time scenarios; not confidence intervals',
    )
    expect(result.scenarios[0]!.metrics.referenceResonanceHz).toBeCloseTo(
      25 * Math.sqrt(1 + 0.08 / 0.035),
      10,
    )
    expect(result.scenarios[1]!.metrics.referenceResonanceHz).toBeCloseTo(
      25 * Math.sqrt(1 + 0.08 / 0.14),
      10,
    )
    expect(result.scenarios[2]!.maxAbsSplDeltaDb).toBe(0)
    expect(result.ranking[0]!.parameter).toBe('volumeM3')
    for (const [i, envelope] of result.envelope.entries()) {
      const levels = [
        result.baseline.points[i]!.splDb,
        ...result.scenarios.map((s) => s.points[i]!.splDb),
      ]
      expect(envelope.minSplDb).toBe(Math.min(...levels))
      expect(envelope.maxSplDb).toBe(Math.max(...levels))
    }
    expect(
      result.scenarios.every(
        (s) =>
          s.points.map((p) => p.frequency).join() ===
          result.baseline.points.map((p) => p.frequency).join(),
      ),
    ).toBe(true)
  })
  it('varies physical vent length without silently retuning the other parameters', () => {
    const vented = {
      ...circuitFixture,
      port: { areaM2: 0.01, effectiveLengthM: 0.4, quality: 7 },
    }
    const original = JSON.stringify(vented)
    const result = api.analyzeSensitivity(
      vented,
      [{ parameter: 'port.effectiveLengthM', values: [0.8] }],
      { minHz: 10, maxHz: 150 },
    )
    expect(result.scenarios[0]!.metrics.referenceResonanceHz).toBeCloseTo(
      result.baseline.metrics.referenceResonanceHz / Math.SQRT2,
      10,
    )
    expect(JSON.stringify(vented)).toBe(original)
  })
  it('scales distributed physical lengths while preserving end corrections and input ownership', () => {
    const path: api.DuctPath = {
      count: 1,
      inletCorrectionMeters: 0.02,
      outletCorrectionMeters: 0.03,
      sections: [
        {
          lengthMeters: 0.4,
          inletAreaSquareMeters: 0.01,
          outletAreaSquareMeters: 0.01,
          profile: 'straight',
        },
      ],
    }
    const input = { ...circuitFixture, port: { ductPath: path, quality: 7 } }
    const original = {
      ...input,
      driver: { ...input.driver },
      port: {
        ...input.port,
        ductPath: {
          ...path,
          sections: path.sections.map((section) => ({ ...section })),
        },
      },
    }
    const options = { minHz: 10, maxHz: 100, points: 31 }
    const result = api.analyzeSensitivity(
      input,
      [{ parameter: 'port.lengthScale', values: [2] }],
      options,
    )
    const expectedInput = {
      ...input,
      port: {
        ...input.port,
        ductPath: {
          ...path,
          sections: [{ ...path.sections[0]!, lengthMeters: 0.8 }],
        },
      },
    }
    expect(result.scenarios[0]!.metrics.referenceResonanceHz).toBeCloseTo(
      api.referenceResonanceHz(expectedInput),
      10,
    )
    const evaluate = api.createCircuit(expectedInput)
    for (const point of result.scenarios[0]!.points)
      expect(point).toEqual(evaluate(point.frequency))
    expect(input).toEqual(original)
    expect(
      api.analyzeSensitivity(
        input,
        [{ parameter: 'port.lengthScale', values: [2] }],
        options,
      ),
    ).toEqual(result)
    for (const parameter of ['port.areaM2', 'port.effectiveLengthM'] as const)
      expect(() =>
        api.analyzeSensitivity(input, [{ parameter, values: [0.02] }], options),
      ).toThrow(/ignored/)
    const loss = api.analyzeSensitivity(
      input,
      [{ parameter: 'port.quality', values: [3] }],
      options,
    )
    expect(loss.scenarios[0]!.maxAbsSplDeltaDb).toBeGreaterThan(0)
  })
  it('rejects invalid values, unsupported port changes and unbounded workloads', () => {
    expect(() =>
      api.analyzeSensitivity(
        circuitFixture,
        [{ parameter: 'volumeM3', values: [-1] }],
        { minHz: 10, maxHz: 100 },
      ),
    ).toThrow()
    expect(() =>
      api.analyzeSensitivity(
        circuitFixture,
        [{ parameter: 'port.areaM2', values: [0.02] }],
        { minHz: 10, maxHz: 100 },
      ),
    ).toThrow(/port/i)
    expect(() =>
      api.analyzeSensitivity(
        circuitFixture,
        [{ parameter: 'volumeM3', values: [NaN] }],
        { minHz: 10, maxHz: 100 },
      ),
    ).toThrow()
    expect(() =>
      api.analyzeSensitivity(
        circuitFixture,
        [{ parameter: 'volumeM3', values: Array(65).fill(0.1) }],
        { minHz: 10, maxHz: 100 },
      ),
    ).toThrow(/scenario/i)
    expect(() =>
      api.analyzeSensitivity(circuitFixture, [], { minHz: 100, maxHz: 10 }),
    ).toThrow()
  })
})
