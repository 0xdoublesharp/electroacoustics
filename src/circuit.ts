import {
  add,
  c,
  div,
  magnitude,
  mul,
  reciprocal,
  type Complex,
} from './complex.js'
import {
  ductPathEquivalentLength,
  ductPathImpedance,
  ductPathPeakVelocityRatio,
  type DuctPath,
} from './ductAcoustics.js'
import { passiveRadiatorTuningHz, radiatorParameters, type PassiveRadiator } from './passiveRadiator.js'
import { driverMotor } from './driverMotor.js'

export interface ThieleSmallDriver {
  fsHz: number
  vasM3: number
  qes: number
  qms: number
  reOhms: number
  leHenries: number
  sdM2: number
}
export interface CircuitInput {
  driver: ThieleSmallDriver
  /** Acoustic compliance volume, including any caller-selected fill multiplier. */
  volumeM3: number
  /** RMS voltage at the amplifier terminals. */
  voltageRms: number
  quantity?: number
  /** Identical drivers per series string. Must divide quantity. Default parallel. */
  seriesDrivers?: number
  medium: { densityKgM3: number; soundSpeedMps: number }
  /** Positive finite Q or Infinity to remove the loss branch. */
  leakageQuality: number
  absorptionQuality: number
  /** Omit for sealed. A duct path supersedes lumped area and effective length. */
  port?: {
    areaM2?: number
    effectiveLengthM?: number
    quality: number
    ductPath?: DuctPath
  }
  /** Identical passive radiators in the cavity. Mutually exclusive with a port. */
  passiveRadiator?: PassiveRadiator
  distanceM?: number
  /** Defaults to 2 pi half-space; 4 pi represents a free-field monopole. */
  radiationSolidAngle?: number
}
export interface CircuitPoint {
  frequency: number
  /** Complex electrical impedance and current at amplifier terminals. */
  impedanceOhms: Complex
  currentAmps: Complex
  /** Outward front cone and mouth flows in RMS m³/s. Pressure also includes leakage flow. */
  coneVolumeVelocityM3s: Complex
  mouthVolumeVelocityM3s: Complex
  radiatorVolumeVelocityM3s?: Complex
  radiatorExcursionPeakM?: number
  /** Source pressure at the reference distance, without propagation delay. RMS Pa. */
  pressurePa: Complex
  splDb: number
  coneExcursionPeakM: number
  portVelocityPeakMps: number
  portMach: number
  /** Total real electrical input power for the complete array. */
  realInputPowerWatts: number
  /** Total copper I²Re loss across all drivers in the array. */
  coilLossWatts: number
}
const positive = (n: number) => Number.isFinite(n) && n > 0
const quality = (n: number) => positive(n) || n === Infinity

/** Low-frequency, linear, identical-driver shared-cavity circuit.
 * Snapshot ownership prevents later caller mutations changing a sweep.
 * Density and sound speed describe the T/S reference medium as well as the box.
 * No thermal compression, panel radiation, diffraction or propagation is fitted.
 */
export function createCircuit(
  source: CircuitInput,
): (frequencyHz: number) => CircuitPoint {
  const input: CircuitInput = {
    ...source,
    driver: { ...source.driver },
    medium: { ...source.medium },
    ...(source.port
      ? {
          port: {
            ...source.port,
            ...(source.port.ductPath
              ? {
                  ductPath: {
                    ...source.port.ductPath,
                    sections: source.port.ductPath.sections.map((section) => ({
                      ...section,
                    })),
                    ...(source.port.ductPath.junctionInertanceLengthsMeters
                      ? {
                          junctionInertanceLengthsMeters: [
                            ...source.port.ductPath
                              .junctionInertanceLengthsMeters,
                          ],
                        }
                      : {}),
                  },
                }
              : {}),
          },
        }
      : {}),
  }
  const { driver, volumeM3, voltageRms, medium } = input
  const quantity = input.quantity ?? 1
  const series = input.seriesDrivers ?? 1
  const parallel = quantity / series
  const distance = input.distanceM ?? 1
  const solidAngle = input.radiationSolidAngle ?? 2 * Math.PI
  if (
    ![
      driver.fsHz,
      driver.vasM3,
      driver.qes,
      driver.qms,
      driver.reOhms,
      driver.sdM2,
      volumeM3,
      voltageRms,
      medium.densityKgM3,
      medium.soundSpeedMps,
      distance,
      solidAngle,
    ].every(positive) ||
    !Number.isFinite(driver.leHenries) ||
    driver.leHenries < 0 ||
    !Number.isSafeInteger(quantity) ||
    quantity < 1 ||
    !Number.isSafeInteger(series) ||
    series < 1 ||
    !Number.isInteger(parallel) ||
    !quality(input.leakageQuality) ||
    !quality(input.absorptionQuality)
  ) {
    throw new RangeError(
      'Circuit requires finite positive SI parameters, nonnegative inductance, valid wiring and positive loss Q (or Infinity)',
    )
  }
  const port = input.port
  const radiator = input.passiveRadiator ? { ...input.passiveRadiator } : undefined
  if (port && radiator) throw new RangeError('Choose a vent or passive radiators')
  const radiatorModel = radiator ? radiatorParameters(radiator) : undefined
  if (
    port &&
    (!quality(port.quality) ||
      (!port.ductPath &&
        (!positive(port.areaM2 ?? NaN) ||
          !positive(port.effectiveLengthM ?? NaN))))
  )
    throw new RangeError(
      'Port requires positive area, effective length and loss Q (or Infinity)',
    )
  const rho = medium.densityKgM3,
    speed = medium.soundSpeedMps
  const { cms, mms, rms, blSquared } = driverMotor(driver, medium)
  const bl = Math.sqrt(blSquared)
  const cab = volumeM3 / (rho * speed ** 2)
  const path = port?.ductPath
  const length = path
    ? ductPathEquivalentLength(path)
    : (port?.effectiveLengthM ?? 0)
  const area = path
    ? path.sections[0]!.inletAreaSquareMeters * path.count
    : (port?.areaM2 ?? 0)
  const mass = port ? (rho * length) / area : 0
  const omega0 = port
    ? 1 / Math.sqrt(mass * cab)
    : radiator ? 2 * Math.PI * passiveRadiatorTuningHz(radiator, volumeM3, medium) : 2 *
      Math.PI *
      driver.fsHz *
      Math.sqrt(1 + (driver.vasM3 * quantity) / volumeM3)
  const characteristic = port ? Math.sqrt(mass / cab) : radiator && radiatorModel
    ? Math.sqrt(radiator.movingMassKg / radiatorModel.areaTerm / cab) : 1 / (omega0 * cab)
  const portResistance = port ? (omega0 * mass) / port.quality : 0
  const leakAdmittance = 1 / (input.leakageQuality * characteristic)
  const lossAdmittance =
    leakAdmittance + 1 / (input.absorptionQuality * characteristic)
  if (![cms, mms, rms, blSquared, cab, omega0, characteristic].every(positive))
    throw new RangeError('Circuit parameters exceed finite numerical support')

  return (frequency: number): CircuitPoint => {
    if (!positive(frequency))
      throw new RangeError('Frequency must be finite and positive')
    const omega = 2 * Math.PI * frequency
    const duct = path
      ? ductPathImpedance(path, frequency, speed, rho, portResistance)
      : undefined
    const yPort = port
      ? reciprocal(duct?.impedance ?? c(portResistance, omega * mass))
      : c(0)
    const baseAdmittance = add(add(c(0, omega * cab), yPort), c(lossAdmittance))
    // Clear the radiator impedance too, so a lossless free radiator resonance
    // does not form an infinite intermediate admittance.
    const radiatorImpedance = radiator && radiatorModel
      ? c(radiator.mechanicalResistanceNsPerM, omega * radiator.movingMassKg - radiatorModel.stiffness / omega)
      : c(1)
    const yTotal = radiatorModel
      ? add(mul(baseAdmittance, radiatorImpedance), c(radiatorModel.areaTerm))
      : baseAdmittance
    // Multiply the mechanical equation through by cavity admittance. At
    // exact lossless tuning yTotal=0: cone motion vanishes but mouth flow and
    // current remain finite. Forming 1/yTotal first would lose that limit.
    const mechanicalNumerator = add(
      mul(c(rms, omega * mms - 1 / (omega * cms)), yTotal),
      mul(c(quantity * driver.sdM2 ** 2), radiatorImpedance),
    )
    const zElectrical = c(driver.reOhms, omega * driver.leHenries)
    const denominator = add(
      mul(zElectrical, mechanicalNumerator),
      mul(c(blSquared), yTotal),
    )
    const drive = (voltageRms * bl) / series
    const velocity = div(mul(c(drive), yTotal), denominator)
    const current = div(
      mul(c((voltageRms * parallel) / series), mechanicalNumerator),
      denominator,
    )
    const impedance = div(c(voltageRms), current)
    const coneFlow = mul(velocity, c(driver.sdM2 * quantity))
    const throatFlow = div(
      mul(c(drive * driver.sdM2 * quantity), yPort),
      denominator,
    )
    const mouthFlow = mul(
      duct ? mul(throatFlow, duct.mouthFlowRatio) : throatFlow,
      c(-1),
    )
    // Leaks vent to the room and radiate (Small 1973: U0 = UD + UP + UL);
    // absorption stays inside the cavity.
    const leakFlow = div(
      mul(c(-drive * driver.sdM2 * quantity * leakAdmittance), radiatorImpedance),
      denominator,
    )
    const radiatorFlow = radiatorModel ? div(c(-drive * driver.sdM2 * quantity * radiatorModel.areaTerm), denominator) : c(0)
    const radiatorTravel = radiator && radiatorModel
      ? (Math.SQRT2 * magnitude(radiatorFlow)) / (omega * radiator.sdM2 * radiatorModel.quantity) : 0
    const pressure = mul(
      add(add(add(coneFlow, mouthFlow), leakFlow), radiatorFlow),
      c(0, (rho * omega) / (solidAngle * distance)),
    )
    const portVelocity = !port
      ? 0
      : Math.SQRT2 *
        magnitude(throatFlow) *
        (path
          ? ductPathPeakVelocityRatio(path, frequency, speed, rho)
          : 1 / area)
    const result = {
      frequency,
      impedanceOhms: impedance,
      currentAmps: current,
      coneVolumeVelocityM3s: coneFlow,
      mouthVolumeVelocityM3s: mouthFlow,
      ...(radiator ? { radiatorVolumeVelocityM3s: radiatorFlow, radiatorExcursionPeakM: radiatorTravel } : {}),
      pressurePa: pressure,
      splDb: 20 * Math.log10(Math.max(magnitude(pressure), 1e-12) / 20e-6),
      coneExcursionPeakM: (Math.SQRT2 * magnitude(velocity)) / omega,
      portVelocityPeakMps: portVelocity,
      portMach: portVelocity / speed,
      realInputPowerWatts: voltageRms * current.re,
      coilLossWatts:
        (magnitude(current) / parallel) ** 2 * driver.reOhms * quantity,
    }
    if (
      ![
        ...Object.values(impedance),
        ...Object.values(current),
        ...Object.values(coneFlow),
        ...Object.values(mouthFlow),
        ...Object.values(radiatorFlow), radiatorTravel,
        ...Object.values(pressure),
        result.splDb,
        result.coneExcursionPeakM,
        portVelocity,
        result.portMach,
        result.realInputPowerWatts,
        result.coilLossWatts,
      ].every(Number.isFinite)
    )
      throw new RangeError(
        'Circuit evaluation exceeds finite numerical support',
      )
    return result
  }
}
