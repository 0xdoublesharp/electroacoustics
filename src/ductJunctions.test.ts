import { describe, expect, it } from 'vitest'
import {
  ductPathEquivalentLength,
  ductPathImpedance,
  ductPathPeakVelocityRatio,
  ductPathTuning,
  ductPathTuningResidual,
  type DuctPath,
} from './ductAcoustics'

const base = (): DuctPath => ({
  sections: [
    {
      lengthMeters: 0.5,
      inletAreaSquareMeters: 0.01,
      outletAreaSquareMeters: 0.01,
      profile: 'straight',
    },
  ],
  count: 2,
  inletCorrectionMeters: 0.03,
  outletCorrectionMeters: 0.05,
})

describe('signed junction inertances and reactive boundary-layer factors', () => {
  it('leaves an external-style path without the new fields byte-identical', () => {
    const plain = base()
    const empty = {
      ...base(),
      junctionInertanceLengthsMeters: [],
      inertanceFactor: 1,
      complianceFactor: 1,
    }
    for (const f of [5, 30, 120]) {
      expect(ductPathImpedance(empty, f, 343, 1.2, 3)).toEqual(
        ductPathImpedance(plain, f, 343, 1.2, 3),
      )
      expect(ductPathPeakVelocityRatio(empty, f, 343, 1.2)).toBe(
        ductPathPeakVelocityRatio(plain, f, 343, 1.2),
      )
    }
    expect(ductPathTuning(empty, 0.1, 343)).toBe(
      ductPathTuning(plain, 0.1, 343),
    )
    expect(ductPathEquivalentLength(empty)).toBe(
      ductPathEquivalentLength(plain),
    )
  })

  it('adds signed throat-referenced junction inertance to the lumped mass', () => {
    const junctions = {
      ...base(),
      junctionInertanceLengthsMeters: [0.04, -0.02],
    }
    const inlet = { ...base(), inletCorrectionMeters: 0.05 }
    expect(ductPathEquivalentLength(junctions)).toBeCloseTo(
      ductPathEquivalentLength(inlet),
      14,
    )
    for (const f of [10, 40])
      expect(
        ductPathImpedance(junctions, f, 343, 1.2).impedance.im,
      ).toBeCloseTo(ductPathImpedance(inlet, f, 343, 1.2).impedance.im, 8)
    expect(ductPathTuning(junctions, 0.1, 343)).toBeCloseTo(
      ductPathTuning(inlet, 0.1, 343),
      9,
    )
    // A negative (mitre) junction raises tuning.
    const mitre = { ...base(), junctionInertanceLengthsMeters: [-0.02] }
    expect(ductPathTuning(mitre, 0.1, 343)).toBeGreaterThan(
      ductPathTuning(base(), 0.1, 343),
    )
  })

  it('rejects junctions that make the total effective inertance non-positive', () => {
    expect(() =>
      ductPathTuning(
        { ...base(), junctionInertanceLengthsMeters: [-0.6] },
        0.1,
        343,
      ),
    ).toThrow(RangeError)
    expect(() =>
      ductPathEquivalentLength({
        ...base(),
        junctionInertanceLengthsMeters: [Number.NaN],
      }),
    ).toThrow(RangeError)
    for (const factor of [0, -1, Number.POSITIVE_INFINITY])
      expect(() =>
        ductPathEquivalentLength({ ...base(), inertanceFactor: factor }),
      ).toThrow(RangeError)
  })

  it('scales the sections by the reactive density and compliance factors', () => {
    const fi = 1.03,
      fc = 1.01
    const lossy = { ...base(), inertanceFactor: fi, complianceFactor: fc }
    // Low-frequency mass: only the section inertance scales, ends do not.
    const lumped =
      base().inletCorrectionMeters + base().outletCorrectionMeters + 0.5 * fi
    expect(ductPathEquivalentLength(lossy)).toBeCloseTo(lumped, 14)
    const mass =
      ductPathImpedance(lossy, 0.01, 343, 1.2).impedance.im /
      (2 * Math.PI * 0.01)
    expect(mass / ((1.2 * lumped) / (0.01 * 2))).toBeCloseTo(1, 6)
    // Wave speed falls by sqrt(fi*fc): the first straight-pipe pole moves.
    const pole = (p: DuctPath) => {
      let lo = 100,
        hi = 250
      const den = (f: number) =>
        ductPathImpedance(
          { ...p, inletCorrectionMeters: 0, outletCorrectionMeters: 0 },
          f,
          343,
          1.2,
        ).mouthFlowRatio.re
      // quarter-wave mouth flow ratio 1/cos changes sign through the pole
      for (let i = 0; i < 80; i++) {
        const mid = (lo + hi) / 2
        if (den(mid) > 0) lo = mid
        else hi = mid
      }
      return (lo + hi) / 2
    }
    expect(pole(lossy)).toBeCloseTo(343 / 4 / 0.5 / Math.sqrt(fi * fc), 3)
    expect(ductPathTuning(lossy, 0.1, 343)).toBeLessThan(
      ductPathTuning(base(), 0.1, 343),
    )
  })

  it.each([
    ['inertanceFactor', 'complianceFactor'],
    ['complianceFactor', 'inertanceFactor'],
  ] as const)('uses unity for an omitted %s', (omitted, supplied) => {
    const duct = { ...base(), [supplied]: 1.1 }
    expect(ductPathImpedance(duct, 100, 343, 1.2)).toEqual(
      ductPathImpedance({ ...duct, [omitted]: 1 }, 100, 343, 1.2),
    )
  })
})

describe('tuning residual', () => {
  it('changes sign at the solved tuning and is linear in volume', () => {
    const path = { ...base(), junctionInertanceLengthsMeters: [-0.01] }
    const f = ductPathTuning(path, 0.12, 343)
    expect(ductPathTuningResidual(path, 0.12, f * 0.999, 343)).toBeLessThan(0)
    expect(ductPathTuningResidual(path, 0.12, f * 1.001, 343)).toBeGreaterThan(
      0,
    )
    const g0 = ductPathTuningResidual(path, 0, 30, 343)
    const g1 = ductPathTuningResidual(path, 1, 30, 343)
    const volume = -g0 / (g1 - g0)
    expect(ductPathTuning(path, volume, 343)).toBeCloseTo(30, 9)
    expect(() => ductPathTuningResidual(path, -1, 30, 343)).toThrow(RangeError)
  })
})
