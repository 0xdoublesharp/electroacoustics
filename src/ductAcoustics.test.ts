import { describe, expect, it } from 'vitest'
import {
  ductPathEquivalentLength,
  ductPathImpedance,
  ductPathPeakVelocityRatio,
  ductPathTuning,
  type DuctPath,
} from './ductAcoustics'
const path = (
  profile: 'straight' | 'conical' | 'exponential' = 'straight',
  outlet = 0.005,
): DuctPath => ({
  sections: [
    {
      lengthMeters: 0.4,
      inletAreaSquareMeters: 0.005,
      outletAreaSquareMeters: outlet,
      profile,
    },
  ],
  count: 1,
  inletCorrectionMeters: 0,
  outletCorrectionMeters: 0,
})
describe('distributed duct acoustics', () => {
  it('matches the analytic open straight pipe tangent and mouth transfer', () => {
    const f = 120,
      kL = (2 * Math.PI * f * 0.4) / 343
    const result = ductPathImpedance(path(), f, 343, 1.2, 20)
    expect(result.impedance.re).toBe(20)
    expect(result.impedance.im).toBeCloseTo(
      ((1.2 * 343) / 0.005) * Math.tan(kL),
      7,
    )
    expect(result.mouthFlowRatio.re).toBeCloseTo(1 / Math.cos(kL), 12)
  })
  it('uses the analytical inertance integral for both tapers and end corrections', () => {
    const cone = {
      ...path('conical', 0.02),
      inletCorrectionMeters: 0.03,
      outletCorrectionMeters: 0.04,
    }
    expect(ductPathEquivalentLength(cone)).toBeCloseTo(0.24, 12)
    expect(ductPathEquivalentLength(path('exponential', 0.02))).toBeCloseTo(
      (0.4 * 0.75) / Math.log(4),
      12,
    )
    for (const p of [cone, path('exponential', 0.02)]) {
      const mass =
        ductPathImpedance(p, 0.001, 343, 1.2).impedance.im /
        (2 * Math.PI * 0.001)
      expect(mass).toBeCloseTo((1.2 * ductPathEquivalentLength(p)) / 0.005, 6)
    }
  })
  it('degenerates to a cylinder for equal areas', () => {
    for (const profile of ['conical', 'exponential'] as const)
      expect(ductPathImpedance(path(profile), 60, 343, 1.2)).toEqual(
        ductPathImpedance(path(), 60, 343, 1.2),
      )
  })
  it('is invariant to exact taper subdivision', () => {
    for (const profile of ['conical', 'exponential'] as const) {
      const p = path(profile, 0.02)
      const mid = profile === 'conical' ? 0.01125 : 0.01
      const split = {
        ...p,
        sections: [
          { ...p.sections[0]!, lengthMeters: 0.2, outletAreaSquareMeters: mid },
          { ...p.sections[0]!, lengthMeters: 0.2, inletAreaSquareMeters: mid },
        ],
      }
      for (const f of [1, 80, 220]) {
        expect(ductPathImpedance(split, f, 343, 1.2).impedance.im).toBeCloseTo(
          ductPathImpedance(p, f, 343, 1.2).impedance.im,
          6,
        )
      }
    }
  })
  it('scales impedance for parallel ducts while resistance is total branch resistance', () => {
    const single = ductPathImpedance(path(), 60, 343, 1.2)
    const parallel = ductPathImpedance(
      { ...path(), count: 2 },
      60,
      343,
      1.2,
      50,
    )
    expect(parallel.impedance.im).toBe(single.impedance.im / 2)
    expect(parallel.impedance.re).toBe(50)
    expect(parallel.mouthFlowRatio).toEqual(single.mouthFlowRatio)
  })
  it('finds the lowest cavity cancellation before the straight pipe pole', () => {
    const f = ductPathTuning(path(), 0.07, 343)
    const x = ductPathImpedance(path(), f, 343, 1.2).impedance.im
    expect((2 * Math.PI * f * 0.07) / (1.2 * 343 ** 2) - 1 / x).toBeCloseTo(
      0,
      12,
    )
    expect(f).toBeLessThan(
      (343 / (2 * Math.PI)) * Math.sqrt(0.005 / (0.07 * 0.4)),
    )
    expect(
      ductPathTuning(
        {
          ...path(),
          sections: [{ ...path().sections[0]!, lengthMeters: 0.8 }],
        },
        0.07,
        343,
      ),
    ).toBeLessThan(f)
  })
  it('rejects malformed geometry and nonpassive losses', () => {
    for (const p of [
      { ...path(), count: 0 },
      { ...path(), sections: [] },
      { ...path(), inletCorrectionMeters: -1 },
      path('straight', 0.02),
      { ...path(), sections: [{ ...path().sections[0]!, lengthMeters: NaN }] },
    ])
      expect(() => ductPathEquivalentLength(p)).toThrow()
    expect(() => ductPathImpedance(path(), 30, 343, 1.2, -1)).toThrow()
  })
})

// Independent integration of pressure/volume-flow conservation, without
// transfer matrices or the transformed Webster equation used by production.
function odeFixture(p: DuctPath, frequency: number) {
  const s = p.sections[0]!
  const omega = 2 * Math.PI * frequency
  const areaAt = (x: number) =>
    s.profile === 'exponential'
      ? s.inletAreaSquareMeters *
        (s.outletAreaSquareMeters / s.inletAreaSquareMeters) **
          (x / s.lengthMeters)
      : (Math.sqrt(s.inletAreaSquareMeters) +
          ((Math.sqrt(s.outletAreaSquareMeters) -
            Math.sqrt(s.inletAreaSquareMeters)) *
            x) /
            s.lengthMeters) **
        2
  const derivative = (x: number, pressure: number, flow: number) => [
    (-omega * 1.2 * flow) / areaAt(x),
    (omega * areaAt(x) * pressure) / (1.2 * 343 ** 2),
  ]
  const h = -s.lengthMeters / 4000
  let pressure = 0,
    flow = 1
  for (let i = 0; i < 4000; i++) {
    const x = s.lengthMeters + i * h
    const a = derivative(x, pressure, flow)
    const b = derivative(
      x + h / 2,
      pressure + (h * a[0]!) / 2,
      flow + (h * a[1]!) / 2,
    )
    const c = derivative(
      x + h / 2,
      pressure + (h * b[0]!) / 2,
      flow + (h * b[1]!) / 2,
    )
    const d = derivative(x + h, pressure + h * c[0]!, flow + h * c[1]!)
    pressure += (h / 6) * (a[0]! + 2 * b[0]! + 2 * c[0]! + d[0]!)
    flow += (h / 6) * (a[1]! + 2 * b[1]! + 2 * c[1]! + d[1]!)
  }
  return { reactance: pressure / flow, ratio: 1 / flow }
}
it('agrees with independent pressure/flow ODE fixtures above and below taper cutoff', () => {
  for (const profile of ['conical', 'exponential'] as const) {
    for (const outlet of [0.001, 0.02]) {
      for (const frequency of [1, 90, 220]) {
        const p = path(profile, outlet)
        const fixture = odeFixture(p, frequency)
        const result = ductPathImpedance(p, frequency, 343, 1.2)
        expect(result.impedance.im / fixture.reactance).toBeCloseTo(1, 9)
        expect(result.mouthFlowRatio.re).toBeCloseTo(fixture.ratio, 9)
      }
    }
  }
})

describe('internal duct velocity maxima', () => {
  it('finds an interior antinode hidden by large mouth and throat endpoints', () => {
    const p: DuctPath = {
      ...path(),
      sections: [
        {
          lengthMeters: 0.6,
          inletAreaSquareMeters: 0.005,
          outletAreaSquareMeters: 0.005,
          profile: 'straight',
        },
        {
          lengthMeters: 0.3,
          inletAreaSquareMeters: 0.005,
          outletAreaSquareMeters: 0.04,
          profile: 'conical',
        },
      ],
    }
    const f = 343 / (2 * 0.6)
    const endpoint = Math.max(
      1 / 0.005,
      Math.abs(ductPathImpedance(p, f, 343, 1.2).mouthFlowRatio.re) / 0.04,
    )
    expect(ductPathPeakVelocityRatio(p, f, 343, 1.2)).toBeGreaterThan(
      endpoint * 1.05,
    )
  })
  it('converges under section subdivision and counts parallel ducts', () => {
    const p = path('exponential', 0.02)
    const split: DuctPath = {
      ...p,
      sections: Array.from({ length: 16 }, (_, i) => ({
        lengthMeters: 0.4 / 16,
        inletAreaSquareMeters: 0.005 * 4 ** (i / 16),
        outletAreaSquareMeters: 0.005 * 4 ** ((i + 1) / 16),
        profile: 'exponential',
      })),
    }
    for (const f of [20, 220, 800]) {
      const peak = ductPathPeakVelocityRatio(p, f, 343, 1.2)
      expect(ductPathPeakVelocityRatio(split, f, 343, 1.2) / peak).toBeCloseTo(
        1,
        6,
      )
      expect(ductPathPeakVelocityRatio({ ...p, count: 2 }, f, 343, 1.2)).toBe(
        peak / 2,
      )
    }
  })
})

it('keeps exact straight poles finite and passive, and finds tuning outside the plotted range', () => {
  const p = path()
  for (const frequency of [343 / 1.6, 343 / 1.6 - 1e-8, 343 / 1.6 + 1e-8]) {
    const result = ductPathImpedance(p, frequency, 343, 1.2, 4)
    expect(result.impedance.re).toBe(4)
    expect(Number.isFinite(result.impedance.im)).toBe(true)
    expect(
      Number.isFinite(ductPathPeakVelocityRatio(p, frequency, 343, 1.2)),
    ).toBe(true)
  }
  const short = { ...p, sections: [{ ...p.sections[0]!, lengthMeters: 0.01 }] }
  const tuning = ductPathTuning(short, 0.001, 343)
  expect(tuning).toBeGreaterThan(220)
  const reactance = ductPathImpedance(short, tuning, 343, 1).impedance.im
  expect(((2 * Math.PI * tuning * 0.001) / 343 ** 2) * reactance).toBeCloseTo(
    1,
    10,
  )
})

it('rejects unsupported finite magnitudes without allocating unbounded samples or returning NaN', () => {
  for (const p of [
    { ...path(), sections: [{ ...path().sections[0]!, lengthMeters: 1e300 }] },
    path('exponential', 1e300),
    {
      ...path(),
      sections: [
        {
          ...path().sections[0]!,
          inletAreaSquareMeters: 1e-300,
          outletAreaSquareMeters: 1e-300,
        },
      ],
    },
  ]) {
    expect(() => ductPathPeakVelocityRatio(p, 30, 343, 1.2)).toThrow(RangeError)
    expect(() => ductPathTuning(p, 0.07, 343)).toThrow(RangeError)
    expect(() => ductPathEquivalentLength(p)).toThrow(RangeError)
  }
  expect(() => ductPathPeakVelocityRatio(path(), 1e300, 343, 1.2)).toThrow(
    RangeError,
  )
  expect(() => ductPathImpedance(path(), 30, 1e-300, 1.2)).toThrow(RangeError)
  expect(() => ductPathTuning(path(), 1e-300, 343)).toThrow(RangeError)
})

it('uses the finite pressure and flow limit at an exact exponential cutoff', () => {
  const duct = path('exponential', 0.02)
  const length = duct.sections[0]!.lengthMeters
  const frequency = (Math.LN2 / length) / (2 * Math.PI)
  const omega = 2 * Math.PI * frequency
  const result = ductPathImpedance(duct, frequency, 1, 1)
  // At cutoff the reduced Webster solution is linear in axial distance.
  const mouthFlowRatio = 2 / (1 + Math.LN2)
  expect(result.mouthFlowRatio.re).toBeCloseTo(mouthFlowRatio, 12)
  expect(result.impedance.im).toBeCloseTo(
    ((omega * length) / 0.01) * mouthFlowRatio,
    12,
  )
})

it('rejects an excessive end correction and an overflowing cascade', () => {
  expect(() =>
    ductPathEquivalentLength({ ...path(), outletCorrectionMeters: 1001 }),
  ).toThrow(/end correction exceeds supported/)

  // Alternating quarter-wave sections multiply their area ratios into the
  // transfer matrix even though every individual section is in range.
  const sections = Array.from({ length: 64 }, (_, index) => {
    const area = index % 2 === 0 ? 1e-10 : 1e4
    return {
      profile: 'straight' as const,
      lengthMeters: 1,
      inletAreaSquareMeters: area,
      outletAreaSquareMeters: area,
    }
  })
  expect(() =>
    ductPathImpedance({ ...path(), sections }, 1, 4, 1),
  ).toThrow(/geometry exceeds finite numerical support/)
})

it('bounds tuning searches and velocity sampling by their numerical limits', () => {
  const straight = path().sections[0]!
  const short = { ...path(), sections: [{ ...straight, lengthMeters: 1e-6 }] }
  expect(() => ductPathTuning(short, 1e-12, 1e6)).toThrow(/1 MHz search range/)

  const slowPhase = {
    ...path(),
    inertanceFactor: 0.001,
    complianceFactor: 0.001,
    sections: [{ ...straight, lengthMeters: 100 }],
  }
  expect(() => ductPathTuning(slowPhase, 1e-12, 1e6)).toThrow(/4096 bounded/)

  const long = { ...path(), sections: [{ ...straight, lengthMeters: 100 }] }
  expect(() => ductPathPeakVelocityRatio(long, 1000, 343, 1)).toThrow(
    /requires too many samples/,
  )
  const many = { ...path(), sections: Array.from({ length: 32 }, () => straight) }
  expect(() => ductPathPeakVelocityRatio(many, 10000, 343, 1)).toThrow(
    /requires too many samples/,
  )
})

it('uses the effective section wave speed to bracket tuning', () => {
  const duct = {
    ...path(),
    inertanceFactor: 0.001,
    complianceFactor: 0.001,
    sections: [{ ...path().sections[0]!, lengthMeters: 1 }],
  }
  const speed = 343
  const volume = 1e-8
  const tuning = ductPathTuning(duct, volume, speed)
  const quarterWave = speed / (4 * Math.sqrt(0.001 * 0.001))
  expect(tuning).toBeGreaterThan(quarterWave * 0.95)
  expect(tuning).toBeLessThan(quarterWave)
  const reactance = ductPathImpedance(duct, tuning, speed, 1).impedance.im
  expect((2 * Math.PI * tuning * volume * reactance) / speed ** 2).toBeCloseTo(1, 10)
})

it('checks the last fractional tuning step up to 1 MHz', () => {
  const section = { ...path().sections[0]!, lengthMeters: 0.001 }
  const duct = { ...path(), sections: [section] }
  const speed = 10000
  const expected = 999900
  // For an open cylinder, omega*V*tan(omega*L/c)/(c*A) = 1 at tuning.
  const omega = 2 * Math.PI * expected
  const volume =
    (speed * section.inletAreaSquareMeters) /
    (omega * Math.tan((omega * section.lengthMeters) / speed))
  expect(ductPathTuning(duct, volume, speed)).toBeCloseTo(expected, 6)
})
