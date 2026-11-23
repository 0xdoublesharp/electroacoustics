import { describe, expect, it } from 'vitest'
import * as api from './index'
import { circuitFixture } from './testFixtures'

describe('circuit sweeps', () => {
  it('rejects filtered power overflow even when phasors and sampling metrics stay finite', () => {
    expect(() =>
      api.sweepCircuit(circuitFixture, {
        minHz: 20,
        maxHz: 80,
        filter: { gainDb: 3100 },
      }),
    ).toThrow(/numeric|finite/i)
  })

  it('exports a configurable adaptive sweep', () => {
    expect(api.sweepCircuit).toBeTypeOf('function')
  })
  it('includes exact resonance and frequency bounds and approaches a dense reference', () => {
    const input = {
      ...circuitFixture,
      driver: { ...circuitFixture.driver, qes: 5, qms: 50 },
    }
    const fc = 25 * Math.sqrt(1 + 0.08 / 0.07)
    const sweep = api.sweepCircuit(input, {
      minHz: 10,
      maxHz: 200,
      relativeTolerance: 0.002,
      maxPoints: 2048,
    })
    expect(sweep.points[0]!.frequency).toBe(10)
    expect(sweep.points.at(-1)!.frequency).toBe(200)
    expect(sweep.points.some((p) => p.frequency === fc)).toBe(true)
    const evaluate = api.createCircuit(input)
    const dense = Array.from({ length: 10001 }, (_, i) =>
      evaluate(10 * 20 ** (i / 10000)),
    )
    expect(Math.max(...sweep.points.map((p) => p.splDb))).toBeCloseTo(
      Math.max(...dense.map((p) => p.splDb)),
      2,
    )
    expect(sweep.sampling.converged).toBe(true)
    expect(sweep.points.length).toBeLessThan(2048)
  })
  it('applies complex filters consistently to pressure, flow, excursion, current and power', () => {
    const raw = api.createCircuit(circuitFixture)(40)
    const filtered = api
      .sweepCircuit(circuitFixture, {
        minHz: 20,
        maxHz: 80,
        filter: { lowpassHz: 40 },
      })
      .points.find((p) => p.frequency === 40)!
    expect(filtered.splDb - raw.splDb).toBeCloseTo(-6.020599913, 8)
    expect(filtered.pressurePa.re).toBeCloseTo(-0.5 * raw.pressurePa.re, 10)
    expect(filtered.pressurePa.im).toBeCloseTo(-0.5 * raw.pressurePa.im, 10)
    expect(filtered.coneExcursionPeakM).toBeCloseTo(
      0.5 * raw.coneExcursionPeakM,
      10,
    )
    expect(filtered.currentAmps.re).toBeCloseTo(-0.5 * raw.currentAmps.re, 10)
    expect(filtered.coilLossWatts).toBeCloseTo(0.25 * raw.coilLossWatts, 10)
    expect(filtered.realInputPowerWatts).toBeCloseTo(
      0.25 * raw.realInputPowerWatts,
      10,
    )
    expect(filtered.impedanceOhms).toEqual(raw.impedanceOhms)
  })
})
