import { odeFixture } from './testFixtures.js'
import { describe, expect, it } from 'vitest'
import {
  boundDuctPathPeakVelocityRatio,
  boundDuctPathTuning,
  ductPathEquivalentLength,
  ductPathImpedance,
  ductPathPeakVelocityRatio,
  ductPathTuning,
  verifyDuctPeakVelocityCertificate,
  verifyDuctTuningCertificate,
  type DuctBound,
  type DuctBoundOptions,
  type DuctPath,
} from './ductAcoustics'
import { ductLogRatio } from './ductBounds.js'
import { dyadicIntervals } from './dyadicInterval.js'
import { enclosedOr } from './interval.js'

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

it.each(['conical', 'exponential'] as const)('encloses the first physical tuning of a %s duct', (profile) => {
  const p = path(profile, 0.02)
  const volume = 0.07
  const result = boundDuctPathTuning(p, volume, 343)
  expect(result.status).toBe('resolved')
  if (result.status !== 'resolved') throw new Error(result.reason)
  expect(result).toMatchObject({ certificate: { version: 1, lower: result.lower, upper: result.upper } })
  expect(verifyDuctTuningCertificate(p, volume, 343, jsonRoundTrip(result.certificate))).toBe(true)
  const residual = (frequency: number) =>
    2 * Math.PI * frequency * volume * odeFixture(p, frequency).reactance / (1.2 * 343 ** 2) - 1
  expect(residual(result.lower)).toBeLessThan(0)
  expect(residual(result.upper)).toBeGreaterThan(0)
  expect((result.upper - result.lower) / result.lower).toBeLessThanOrEqual(1e-5)
})

describe('internal duct velocity maxima', () => {
  it('finds an interior antinode hidden by large mouth and throat endpoints', () => {
    const p = antinodePath()
    const f = 343 / (2 * 0.6)
    const endpoint = Math.max(
      1 / 0.005,
      Math.abs(ductPathImpedance(p, f, 343, 1.2).mouthFlowRatio.re) / 0.04,
    )
    expect(ductPathPeakVelocityRatio(p, f, 343, 1.2)).toBeGreaterThan(
      endpoint * 1.05,
    )
    const bounded = boundDuctPathPeakVelocityRatio(p, f, 343, 1.2)
    expect(bounded.status).toBe('resolved')
    if (bounded.status !== 'resolved') throw new Error(bounded.reason)
    expect(bounded).toMatchObject({ certificate: { version: 1, lower: bounded.lower, upper: bounded.upper } })
    expect(verifyDuctPeakVelocityCertificate(p, f, 343, 1.2, jsonRoundTrip(bounded.certificate))).toBe(true)
    expect(bounded.lower).toBeGreaterThan(endpoint * 1.05)
    // The upstream uniform section spans half a wave, so its exact maximum
    // follows from the pressure and flow at the junction. Integrate the taper
    // independently, then use that junction state for the uniform section.
    const taper = odeFixture({ ...p, sections: [p.sections[1]!] }, f)
    const characteristic = 1.2 * 343 / 0.005
    const upstreamPeak = Math.hypot(1, taper.reactance / characteristic) / 0.005
    const reference = Math.max(upstreamPeak, taper.peak)
    expect(bounded.lower).toBeLessThanOrEqual(reference + 1e-8)
    expect(bounded.upper).toBeGreaterThanOrEqual(reference - 1e-8)
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
  expect(boundDuctPathTuning(short, 1e-12, 1e6)).toMatchObject({ status: 'unresolved', reason: 'bracket' })
  expect(() => boundDuctPathTuning(short, -1, 343)).toThrow(/cavity parameters/)

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

it('reports unsupported spatial ranges, poles, exhausted budgets, and invalid bounds', () => {
  const straight = path()
  const conical = path('conical', 0.02)
  expect(() => boundDuctPathTuning(straight, 0.06, 343, { maxSplits: -1 })).toThrow(/budget/)
  expect(() => boundDuctPathPeakVelocityRatio(straight, 20, 343, 1.2, { relativeTolerance: 0.1 })).toThrow(/tolerance/)
  expect(boundDuctPathTuning(straight, 0.06, 343, { relativeTolerance: 1e-20 }))
    .toMatchObject({ status: 'unresolved', reason: 'bracket' })
  expect(boundDuctPathTuning(straight, 1e-12, 343))
    .toMatchObject({ status: 'unresolved', reason: 'pole' })
  expect(boundDuctPathTuning(conical, 0.06, 343, { maxSplits: 0 }))
    .toMatchObject({ status: 'unresolved', reason: 'subdivision-budget' })
  expect(boundDuctPathPeakVelocityRatio(conical, 150, 343, 1.2, { maxSplits: 0 }))
    .toMatchObject({ status: 'unresolved', reason: 'subdivision-budget' })
  const halfMeter = { ...straight, sections: [{ ...straight.sections[0]!, lengthMeters: 0.5 }] }
  expect(boundDuctPathPeakVelocityRatio(halfMeter, 171.5, 343, 1.2))
    .toMatchObject({ status: 'unresolved', reason: 'pole' })
  expect(boundDuctPathPeakVelocityRatio(straight, 1e6, 343, 1.2))
    .toMatchObject({ status: 'unresolved', reason: 'numeric-range' })
  const almostConstant = { ...straight, sections: [{ ...straight.sections[0]!, lengthMeters: 1e-9 }] }
  expect(boundDuctPathPeakVelocityRatio(almostConstant, 1e-6, 343, 1.2,
    { relativeTolerance: 1e-18, maxSplits: 0 })).toMatchObject({ status: 'unresolved', reason: 'subdivision-budget' })
  const withCorrections = { ...conical, junctionInertanceLengthsMeters: [0.01, -0.001] }
  expect(boundDuctPathTuning(withCorrections, 0.06, 343).status).toBe('resolved')
  expect(enclosedOr(() => ductLogRatio({ lo: dyadicIntervals.one.lo, hi: dyadicIntervals.exact(5).hi }), null))
    .toBeNull()
})

function antinodePath(): DuctPath {
  return {
    ...path(),
    sections: [
      { ...path().sections[0]!, lengthMeters: 0.6 },
      { ...path('conical', 0.04).sections[0]!, lengthMeters: 0.3 },
    ],
  }
}

function jsonRoundTrip<T>(value: T): T {
  return JSON.parse(JSON.stringify(value))
}

function certificateOf<C>(result: DuctBound<C>): C {
  if (result.status !== 'resolved') throw new Error(result.reason)
  return result.certificate
}

function requestWith(request: string, argument: number, value: unknown): string {
  const parameters: unknown[] = JSON.parse(request)
  parameters[argument] = value
  return JSON.stringify(parameters)
}

describe('duct certificates', () => {
  const speed = 343
  const volume = 0.06
  const density = 1.2
  const frequency = speed / 1.2
  const corrected: DuctPath = {
    ...antinodePath(),
    count: 2,
    inletCorrectionMeters: 0.015,
    outletCorrectionMeters: 0.025,
    junctionInertanceLengthsMeters: [-0.001, 0.005],
    inertanceFactor: 1.02,
    complianceFactor: 1.01,
  }

  it.each([path(), antinodePath(), corrected])('replays a tuning bound after JSON serialization %#', (p) => {
    const options = { relativeTolerance: 0.0001, maxSplits: 128 }
    const certificate = jsonRoundTrip(certificateOf(boundDuctPathTuning(p, volume, speed, options)))
    // Construct the same geometry with a different field order.
    const { sections, ...geometry } = p
    const reordered = { sections: sections.map(({ profile, ...section }) => ({ profile, ...section })), ...geometry }
    expect(verifyDuctTuningCertificate(reordered, volume, speed, certificate,
      { maxSplits: 128, relativeTolerance: 0.0001 })).toBe(true)
  })

  it.each([path(), path('conical', 0.02), path('exponential', 0.02)])(
    'replays the velocity envelope of a single section %#', (p) => {
      const hz = 150
      const result = boundDuctPathPeakVelocityRatio(p, hz, speed, density)
      const certificate = jsonRoundTrip(certificateOf(result))
      expect(verifyDuctPeakVelocityCertificate(p, hz, speed, density, certificate,
        { maxSplits: 4096, relativeTolerance: 0.001 })).toBe(true)
      expect(certificate.witness.sectionIndex).toBe(0)
    },
  )

  it('replays a corrected interior antinode using throat-to-mouth section order', () => {
    const certificate = jsonRoundTrip(certificateOf(boundDuctPathPeakVelocityRatio(corrected, frequency, speed, density)))
    expect(certificate.witness.sectionIndex).toBe(0)
    expect(certificate.witness.fraction).toBeGreaterThan(0)
    expect(certificate.witness.fraction).toBeLessThan(1)
    expect(verifyDuctPeakVelocityCertificate(corrected, frequency, speed, density, certificate)).toBe(true)
    expect(verifyDuctPeakVelocityCertificate(corrected, frequency, speed, density,
      { ...certificate, witness: { ...certificate.witness, sectionIndex: 1 } })).toBe(false)
    expect(verifyDuctPeakVelocityCertificate(corrected, frequency, speed, density,
      { ...certificate, sectionSpans: [...certificate.sectionSpans].reverse() })).toBe(false)
  })

  it('rejects forged tuning brackets and incomplete earlier-root exclusions', () => {
    const p = path('conical', 0.02)
    const certificate = certificateOf(boundDuctPathTuning(p, volume, speed))
    const { lower, upper, earlierSpans, request } = certificate
    const [first, second, ...rest] = earlierSpans
    const last = earlierSpans.at(-1)!
    const beforeRoot = lower + (upper - lower) / 8
    const afterRoot = upper - (upper - lower) / 8
    const tampered = [
      { version: 2 },
      { request: 'another request' },
      { relativeTolerance: 0.05 },
      { lower: 0 },
      { upper: lower },
      { upper: Infinity },
      { upper: upper * 1.01 },
      { upper: beforeRoot },
      { lower: afterRoot },
      { earlierSpans: null },
      { earlierSpans: [] },
      { earlierSpans: [null, ...earlierSpans.slice(1)] },
      { earlierSpans: [{ ...first, minHz: first!.maxHz / 2 }, second, ...rest] },
      { earlierSpans: [first, { ...second, minHz: (second!.minHz + second!.maxHz) / 2 }, ...rest] },
      { earlierSpans: [{ minHz: 0, maxHz: 0 }, second, ...rest] },
      { earlierSpans: [{ minHz: 0, maxHz: upper }] },
      { earlierSpans: earlierSpans.slice(0, -1) },
      { earlierSpans: [...earlierSpans.slice(0, -1), { ...last, maxHz: (last.minHz + lower) / 2 }] },
      { earlierSpans: [{ minHz: 0, maxHz: lower }] },
    ]
    for (const change of tampered)
      expect(verifyDuctTuningCertificate(p, volume, speed, { ...certificate, ...change } as typeof certificate),
        JSON.stringify(change)).toBe(false)
    expect(verifyDuctTuningCertificate(p, volume, speed,
      { ...certificate, request: requestWith(request, 4, 0) }, { maxSplits: 0 })).toBe(false)
    expect(verifyDuctTuningCertificate(p, volume * 2, speed, certificate)).toBe(false)
    expect(verifyDuctTuningCertificate(p, volume, speed + 1, certificate)).toBe(false)
    expect(verifyDuctTuningCertificate({ ...p, count: 2 }, volume, speed, certificate)).toBe(false)
    expect(verifyDuctTuningCertificate(p, volume, speed, certificate, { maxSplits: 4095 })).toBe(false)
    for (const malformed of [null, {}, 'certificate', { version: 1, request }])
      expect(verifyDuctTuningCertificate(p, volume, speed, malformed as typeof certificate)).toBe(false)
  })

  it('rejects a tuning bracket crossing a duct pole even with the correct request', () => {
    const p = path()
    const certificate = certificateOf(boundDuctPathTuning(p, volume, speed))
    const smallVolume = 1e-12
    const pole = speed / (4 * p.sections[0]!.lengthMeters)
    const estimate = ductPathTuning(p, smallVolume, speed)
    const lower = estimate * (1 - 4.5e-6)
    const upper = estimate * (1 + 4.5e-6)
    expect(upper).toBeGreaterThan(pole)
    expect(verifyDuctTuningCertificate(p, smallVolume, speed, {
      ...certificate, request: requestWith(certificate.request, 1, smallVolume),
      lower, upper, earlierSpans: [{ minHz: 0, maxHz: lower }],
    })).toBe(false)
  })

  it('rejects forged velocity bounds, point witnesses, and spatial partitions', () => {
    const p = antinodePath()
    const certificate = certificateOf(boundDuctPathPeakVelocityRatio(p, frequency, speed, density))
    const { lower, upper, witness, sectionSpans, request } = certificate
    const [spans, other] = sectionSpans
    const [first, second, ...rest] = spans!
    const withSpans = (replacement: unknown) => [replacement, other]
    const tampered = [
      { version: 2 },
      { request: 'another request' },
      { relativeTolerance: 0.05 },
      { lower: -1 },
      { upper: lower * 0.999 },
      { upper: Infinity },
      { upper: upper * 1.01 },
      { lower: upper },
      { upper: lower },
      { witness: null },
      { witness: { ...witness, sectionIndex: -1 } },
      { witness: { ...witness, sectionIndex: 0.5 } },
      { witness: { ...witness, sectionIndex: 2 } },
      { witness: { ...witness, fraction: 1.01 } },
      { witness: { ...witness, fraction: -0.01 } },
      { witness: { ...witness, fraction: NaN } },
      { witness: { ...witness, fraction: 0 } },
      { sectionSpans: null },
      { sectionSpans: [spans] },
      { sectionSpans: withSpans(null) },
      { sectionSpans: withSpans([]) },
      { sectionSpans: withSpans([null]) },
      { sectionSpans: withSpans([{ ...first, minFraction: first!.maxFraction / 2 }, second, ...rest]) },
      { sectionSpans: withSpans([first, { ...second, minFraction: (second!.minFraction + second!.maxFraction) / 2 }, ...rest]) },
      { sectionSpans: withSpans([{ minFraction: 0, maxFraction: 0 }, second, ...rest]) },
      { sectionSpans: withSpans([{ minFraction: 0, maxFraction: 2 }]) },
      { sectionSpans: withSpans([{ minFraction: 0, maxFraction: 1 }]) },
      { sectionSpans: withSpans(spans!.slice(0, -1)) },
    ]
    for (const change of tampered)
      expect(verifyDuctPeakVelocityCertificate(p, frequency, speed, density,
        { ...certificate, ...change } as typeof certificate), JSON.stringify(change)).toBe(false)
    expect(verifyDuctPeakVelocityCertificate(p, frequency, speed, density,
      { ...certificate, request: requestWith(request, 5, 0) }, { maxSplits: 0 })).toBe(false)
    expect(verifyDuctPeakVelocityCertificate(p, frequency - 1, speed, density, certificate)).toBe(false)
    expect(verifyDuctPeakVelocityCertificate(p, frequency, speed + 1, density, certificate)).toBe(false)
    expect(verifyDuctPeakVelocityCertificate(p, frequency, speed, density * 2, certificate)).toBe(false)
    expect(verifyDuctPeakVelocityCertificate(p, frequency, speed, density, certificate, { maxSplits: 4095 })).toBe(false)
    for (const malformed of [null, {}, 'certificate', { version: 1, request }])
      expect(verifyDuctPeakVelocityCertificate(p, frequency, speed, density, malformed as typeof certificate)).toBe(false)
  })

  it('rejects velocity certificates at a pole even with the correct request', () => {
    const p = { ...path(), sections: [{ ...path().sections[0]!, lengthMeters: 0.5 }] }
    const certificate = certificateOf(boundDuctPathPeakVelocityRatio(p, 100, speed, density))
    const pole = speed / 2
    expect(verifyDuctPeakVelocityCertificate(p, pole, speed, density, {
      ...certificate, request: requestWith(certificate.request, 1, pole),
    })).toBe(false)
  })

  it('returns an unresolved result when the request changes before self-verification', () => {
    function changingOptions(): DuctBoundOptions {
      let maxSplits = 4096
      return {
        get maxSplits() {
          return maxSplits--
        },
      }
    }
    const p = path()
    expect(boundDuctPathTuning(p, volume, speed, changingOptions()))
      .toMatchObject({ status: 'unresolved', reason: 'certificate-rejected' })
    expect(boundDuctPathPeakVelocityRatio(p, frequency, speed, density, changingOptions()))
      .toMatchObject({ status: 'unresolved', reason: 'certificate-rejected' })
  })

  it('fails closed for unsupported requests and bound options', () => {
    const p = path()
    const tuning = certificateOf(boundDuctPathTuning(p, volume, speed))
    const velocity = certificateOf(boundDuctPathPeakVelocityRatio(p, frequency, speed, density))
    const arrayLike = { 0: p.sections[0], length: 1 } as unknown as DuctPath['sections']
    for (const malformedPath of [
      null as unknown as DuctPath, { ...p, count: 0 }, { ...p, sections: arrayLike },
      { ...p, junctionInertanceLengthsMeters: new Array<number>(1) },
    ]) {
      expect(verifyDuctTuningCertificate(malformedPath, volume, speed, tuning)).toBe(false)
      expect(verifyDuctPeakVelocityCertificate(malformedPath, frequency, speed, density, velocity)).toBe(false)
    }
    expect(verifyDuctTuningCertificate(p, -1, speed, tuning)).toBe(false)
    expect(verifyDuctTuningCertificate(p, volume, 0, tuning)).toBe(false)
    expect(verifyDuctPeakVelocityCertificate(p, 0, speed, density, velocity)).toBe(false)
    expect(verifyDuctPeakVelocityCertificate(p, frequency, 0, density, velocity)).toBe(false)
    expect(verifyDuctPeakVelocityCertificate(p, frequency, speed, 0, velocity)).toBe(false)
    for (const options of [
      null, 1, [], { relativeTolerance: NaN }, { relativeTolerance: 0 }, { relativeTolerance: 0.1 },
      { maxSplits: 0.5 }, { maxSplits: -1 }, { maxSplits: 8193 },
    ]) {
      expect(verifyDuctTuningCertificate(p, volume, speed, tuning, options as DuctBoundOptions)).toBe(false)
      expect(verifyDuctPeakVelocityCertificate(p, frequency, speed, density, velocity, options as DuctBoundOptions)).toBe(false)
    }
  })
})
