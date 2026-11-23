import { describe, expect, it } from 'vitest'
import * as api from './index'

import { circuitFixture as fixture } from './testFixtures'

it('accounts for every dissipated watt in a parallel-driver cabinet with lumped or distributed ports', () => {
  const quantity = 4
  const rho = fixture.medium.densityKgM3
  const speed = fixture.medium.soundSpeedMps
  const cms =
    fixture.driver.vasM3 / (rho * speed ** 2 * fixture.driver.sdM2 ** 2)
  const mms = 1 / ((2 * Math.PI * fixture.driver.fsHz) ** 2 * cms)
  const mechanicalResistance =
    (2 * Math.PI * fixture.driver.fsHz * mms) / fixture.driver.qms
  const path: api.DuctPath = {
    count: 2,
    inletCorrectionMeters: 0,
    outletCorrectionMeters: 0,
    sections: [
      {
        profile: 'conical',
        lengthMeters: 0.5,
        inletAreaSquareMeters: 0.01,
        outletAreaSquareMeters: 0.02,
      },
    ],
  }
  // Integral of dx/S(x) for this conical area expansion gives L/sqrt(2).
  const equivalentLength = 0.5 / Math.sqrt(2)
  const area = 0.02
  const portMass = (rho * equivalentLength) / area
  const cavityCompliance = fixture.volumeM3 / (rho * speed ** 2)
  const portResistance = Math.sqrt(portMass / cavityCompliance) / 7
  for (const distributed of [false, true]) {
    const circuit = api.createCircuit({
      ...fixture,
      quantity,
      port: distributed
        ? { quality: 7, ductPath: path }
        : { quality: 7, areaM2: area, effectiveLengthM: equivalentLength },
    })
    for (const frequency of [8, 35, 100, 200]) {
      const point = circuit(frequency)
      const coneVelocityRms =
        Math.hypot(
          point.coneVolumeVelocityM3s.re,
          point.coneVolumeVelocityM3s.im,
        ) /
        (quantity * fixture.driver.sdM2)
      const mouthFlowRms = Math.hypot(
        point.mouthVolumeVelocityM3s.re,
        point.mouthVolumeVelocityM3s.im,
      )
      const mouthToThroat = distributed
        ? Math.abs(
            api.ductPathImpedance(path, frequency, speed, rho).mouthFlowRatio
              .re,
          )
        : 1
      const throatFlowRms = mouthFlowRms / mouthToThroat
      const dissipated =
        point.coilLossWatts +
        quantity * mechanicalResistance * coneVelocityRms ** 2 +
        portResistance * throatFlowRms ** 2
      expect(point.realInputPowerWatts).toBeCloseTo(dissipated, 11)
    }
  }
})

it('conserves total volume flow and peak particle speed when an equal-area duct is split into parallel ducts', () => {
  const circuits = [1, 4, 9].map((count) =>
    api.createCircuit({
      ...fixture,
      port: {
        quality: 7,
        ductPath: {
          count,
          inletCorrectionMeters: 0,
          outletCorrectionMeters: 0,
          sections: [
            {
              profile: 'straight',
              lengthMeters: 0.5,
              inletAreaSquareMeters: 0.02 / count,
              outletAreaSquareMeters: 0.02 / count,
            },
          ],
        },
      },
    }),
  )
  for (const frequency of [8, 35, 100]) {
    const reference = circuits[0]!(frequency)
    for (const circuit of circuits) {
      const point = circuit(frequency)
      expect(point.mouthVolumeVelocityM3s.re).toBeCloseTo(
        reference.mouthVolumeVelocityM3s.re,
        12,
      )
      expect(point.mouthVolumeVelocityM3s.im).toBeCloseTo(
        reference.mouthVolumeVelocityM3s.im,
        12,
      )
      // With a pressure-release mouth and kL < pi/2, its flow antinode is
      // the largest along this uniform tube: peak u = sqrt(2) * RMS U / A_total.
      const mouthRms = Math.hypot(
        point.mouthVolumeVelocityM3s.re,
        point.mouthVolumeVelocityM3s.im,
      )
      expect(point.portVelocityPeakMps).toBeCloseTo(
        (Math.SQRT2 * mouthRms) / 0.02,
        10,
      )
      expect(point.portMach).toBeCloseTo(
        point.portVelocityPeakMps / fixture.medium.soundSpeedMps,
        12,
      )
    }
  }
})

describe('SI electroacoustic circuit', () => {
  it('exports an application-independent solver', () => {
    expect(api.createCircuit).toBeTypeOf('function')
  })
  it('matches the sealed mechanical closed form at resonance', () => {
    const fc = 25 * Math.sqrt(1 + 0.08 / 0.07)
    const rho = 1.2041,
      speed = 343,
      sd = 0.05
    const cms = 0.08 / (rho * speed ** 2 * sd ** 2)
    const mass = 1 / ((2 * Math.PI * 25) ** 2 * cms)
    const rm = (2 * Math.PI * 25 * mass) / 8
    const bl2 = (2 * Math.PI * 25 * mass * 6) / 0.45
    const velocity = (2.83 * Math.sqrt(bl2)) / (6 * rm + bl2)
    const point = api.createCircuit(fixture)(fc)
    expect(point.impedanceOhms.re).toBeCloseTo(6 + bl2 / rm, 8)
    expect(point.impedanceOhms.im).toBeCloseTo(0, 8)
    expect(point.coneExcursionPeakM).toBeCloseTo(
      (Math.SQRT2 * velocity) / (2 * Math.PI * fc),
      10,
    )
    expect(point.pressurePa.im).toBeCloseTo(rho * fc * sd * velocity, 10)
    expect(point.portVelocityPeakMps).toBe(0)
    expect(point.realInputPowerWatts).toBeCloseTo(
      2.83 ** 2 / (6 + bl2 / rm),
      10,
    )
    expect(point.coilLossWatts).toBeCloseTo(
      (2.83 / (6 + bl2 / rm)) ** 2 * 6,
      10,
    )
  })
  it('obeys voltage and distance scaling and half/full-space normalization', () => {
    const base = api.createCircuit(fixture)(60)
    const doubled = api.createCircuit({ ...fixture, voltageRms: 5.66 })(60)
    expect(doubled.splDb - base.splDb).toBeCloseTo(20 * Math.log10(2), 10)
    expect(doubled.coneExcursionPeakM).toBeCloseTo(
      base.coneExcursionPeakM * 2,
      12,
    )
    expect(doubled.realInputPowerWatts).toBeCloseTo(
      base.realInputPowerWatts * 4,
      12,
    )
    const far = api.createCircuit({ ...fixture, distanceM: 2 })(60)
    const full = api.createCircuit({
      ...fixture,
      radiationSolidAngle: 4 * Math.PI,
    })(60)
    expect(far.splDb).toBeCloseTo(full.splDb, 10)
    expect(base.splDb - far.splDb).toBeCloseTo(20 * Math.log10(2), 10)
  })
  it('maps identical series and parallel arrays to the same physical drive', () => {
    const parallel = api.createCircuit({ ...fixture, quantity: 2 })(40)
    const series = api.createCircuit({
      ...fixture,
      quantity: 2,
      seriesDrivers: 2,
      voltageRms: 5.66,
    })(40)
    expect(series.splDb).toBeCloseTo(parallel.splDb, 10)
    expect(series.impedanceOhms.re).toBeCloseTo(
      parallel.impedanceOhms.re * 4,
      10,
    )
    expect(series.realInputPowerWatts).toBeCloseTo(
      parallel.realInputPowerWatts,
      10,
    )
  })
  it('is passive and partitions input power into copper and mechanical/acoustic losses', () => {
    const circuit = api.createCircuit({
      ...fixture,
      leakageQuality: 15,
      absorptionQuality: 30,
      port: { areaM2: 0.01, effectiveLengthM: 0.5, quality: 7 },
    })
    for (const f of [8, 15, 25, 40, 80, 200]) {
      const p = circuit(f)
      expect(p.impedanceOhms.re).toBeGreaterThanOrEqual(6)
      expect(p.realInputPowerWatts).toBeGreaterThan(p.coilLossWatts)
      expect(p.realInputPowerWatts).toBeLessThanOrEqual(
        Math.hypot(p.currentAmps.re, p.currentAmps.im) * fixture.voltageRms,
      )
      expect(p.portVelocityPeakMps).toBeGreaterThan(0)
    }
  })
  it('rejects invalid public inputs and owns a snapshot of nested inputs', () => {
    for (const volumeM3 of [0, -1, NaN, Infinity])
      expect(() => api.createCircuit({ ...fixture, volumeM3 })).toThrow()
    for (const quantity of [0, 1.5, Infinity])
      expect(() => api.createCircuit({ ...fixture, quantity })).toThrow()
    expect(() =>
      api.createCircuit({ ...fixture, quantity: 3, seriesDrivers: 2 }),
    ).toThrow()
    expect(() =>
      api.createCircuit({
        ...fixture,
        driver: { ...fixture.driver, qes: NaN },
      }),
    ).toThrow()
    expect(() => api.createCircuit({ ...fixture, leakageQuality: 0 })).toThrow()
    expect(() =>
      api.createCircuit({
        ...fixture,
        port: { areaM2: 0, effectiveLengthM: 1, quality: 7 },
      }),
    ).toThrow()
    const input = { ...fixture, driver: { ...fixture.driver } }
    const circuit = api.createCircuit(input)
    const before = circuit(25)
    input.driver.fsHz = 99
    input.volumeM3 = 2
    expect(circuit(25)).toEqual(before)
    for (const f of [0, -1, Infinity, NaN]) expect(() => circuit(f)).toThrow()
  })

  it.each([{ areaM2: 0.01 }, { effectiveLengthM: 0.4 }])(
    'requires both area and effective length for a lumped port with %j',
    (port) => {
      expect(() =>
        api.createCircuit({ ...fixture, port: { ...port, quality: 7 } }),
      ).toThrow(/port requires positive area, effective length/i)
    },
  )

  it('rejects finite inputs that overflow derived parameters or phasors', () => {
    expect(() =>
      api.createCircuit({
        ...fixture,
        medium: { ...fixture.medium, soundSpeedMps: Number.MAX_VALUE },
      }),
    ).toThrow(/parameters exceed finite numerical support/)
    expect(() => api.createCircuit(fixture)(Number.MAX_VALUE)).toThrow(
      /evaluation exceeds finite numerical support/,
    )
  })

  it('owns a snapshot of signed duct junction corrections', () => {
    const ductPath: api.DuctPath = {
      count: 1,
      inletCorrectionMeters: 0,
      outletCorrectionMeters: 0,
      junctionInertanceLengthsMeters: [0.03, -0.01],
      sections: [
        {
          profile: 'straight',
          lengthMeters: 0.4,
          inletAreaSquareMeters: 0.01,
          outletAreaSquareMeters: 0.01,
        },
      ],
    }
    const input = { ...fixture, port: { quality: 7, ductPath } }
    const circuit = api.createCircuit(input)
    const before = circuit(40)
    ductPath.junctionInertanceLengthsMeters![0] = 0.1
    expect(circuit(40)).toEqual(before)
    expect(api.createCircuit(input)(40).portMach).not.toBe(before.portMach)
  })
})

it('accepts a duct path without ignored lumped placeholders and approaches the lumped limit', () => {
  const ductPath = {
    count: 1,
    inletCorrectionMeters: 0,
    outletCorrectionMeters: 0,
    sections: [
      {
        profile: 'straight' as const,
        lengthMeters: 0.002,
        inletAreaSquareMeters: 0.005,
        outletAreaSquareMeters: 0.005,
      },
    ],
  }
  const distributed = api.createCircuit({
    ...fixture,
    port: { quality: 7, ductPath },
  })
  const lumped = api.createCircuit({
    ...fixture,
    port: { quality: 7, areaM2: 0.005, effectiveLengthM: 0.002 },
  })
  for (const f of [5, 8, 12]) {
    const a = distributed(f),
      b = lumped(f)
    expect(Math.abs(a.splDb - b.splDb)).toBeLessThan(0.001)
    expect(a.portVelocityPeakMps / b.portVelocityPeakMps).toBeCloseTo(1, 4)
    expect(
      Math.hypot(a.impedanceOhms.re, a.impedanceOhms.im) /
        Math.hypot(b.impedanceOhms.re, b.impedanceOhms.im),
    ).toBeCloseTo(1, 4)
  }
  const before = distributed(40)
  ductPath.sections[0]!.lengthMeters = 5
  expect(distributed(40)).toEqual(before)
})

it('evaluates the exact lossless cavity cancellation without an infinite intermediate load', () => {
  const input = {
    driver: {
      fsHz: 1,
      vasM3: 1,
      qes: 1,
      qms: 1,
      reOhms: 1,
      leHenries: 0,
      sdM2: 1,
    },
    volumeM3: 1,
    voltageRms: 1,
    medium: { densityKgM3: 1, soundSpeedMps: 1 },
    leakageQuality: Infinity,
    absorptionQuality: Infinity,
    port: { areaM2: 1, effectiveLengthM: 1, quality: Infinity },
  }
  const result = api.createCircuit(input)(1 / (2 * Math.PI))
  expect(result.coneExcursionPeakM).toBe(0)
  expect(result.impedanceOhms.re).toBe(1)
  expect(result.impedanceOhms.im).toBe(0)
  // At tuning, pressure balances motor force: p_box = Bl*V/(Re*Sd).
  // Here Mms=1/(2pi)^2, Bl=sqrt(2pi*Mms), omega*portMass=1.
  expect(result.mouthVolumeVelocityM3s.im).toBeCloseTo(
    1 / Math.sqrt(2 * Math.PI),
    12,
  )
})

it("radiates box leakage like Small's lossy vented response", () => {
  // Small (1973): U0 = UD + UP + UL; QL = 7, QA = QP = infinity.
  const rho = 1.2041,
    speed = 343.2
  const driver = {
    fsHz: 25,
    vasM3: 0.1,
    qes: 0.45,
    qms: 3.6,
    reOhms: 6,
    leHenries: 0,
    sdM2: 0.05,
  }
  const volume = 0.1,
    tuning = 30,
    area = 0.01,
    leakage = 7
  const circuit = api.createCircuit({
    driver,
    volumeM3: volume,
    voltageRms: 2.83,
    medium: { densityKgM3: rho, soundSpeedMps: speed },
    leakageQuality: leakage,
    absorptionQuality: Infinity,
    port: {
      areaM2: area,
      effectiveLengthM:
        (speed ** 2 * area) / ((2 * Math.PI * tuning) ** 2 * volume),
      quality: Infinity,
    },
  })
  const qt = (driver.qes * driver.qms) / (driver.qes + driver.qms)
  const alpha = driver.vasM3 / volume,
    h = tuning / driver.fsHz,
    root = Math.sqrt(h)
  const a1 = 1 / (qt * root) + root / leakage
  const a2 = (alpha + 1) / h + h + 1 / (leakage * qt)
  const a3 = root / qt + 1 / (leakage * root)
  const eta0 =
    (4 * Math.PI ** 2 * driver.fsHz ** 3 * driver.vasM3) /
    (speed ** 3 * driver.qes)
  const reference =
    20 *
    Math.log10(
      Math.sqrt(
        ((eta0 * 2.83 ** 2) / driver.reOhms) * ((rho * speed) / (2 * Math.PI)),
      ) / 20e-6,
    )
  for (const frequency of [10, 20, 30]) {
    const w = frequency / Math.sqrt(tuning * driver.fsHz)
    const response =
      w ** 4 / Math.hypot(w ** 4 - a2 * w * w + 1, -a1 * w ** 3 + a3 * w)
    expect(circuit(frequency).splDb).toBeCloseTo(
      reference + 20 * Math.log10(response),
      3,
    )
  }
})
