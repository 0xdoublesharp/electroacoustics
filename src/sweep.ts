import { pressureSplDb } from './pressure.js'
import {
  createCircuit,
  type CircuitInput,
  type CircuitPoint,
} from './circuit.js'
import { magnitude, mul } from './complex.js'
import { ductPathTuning } from './ductAcoustics.js'
import { composeFilters, type FilterChain } from './filters.js'
import { sampleAdaptive, type SamplingOptions } from './sampling.js'
import { passiveRadiatorResonanceHz, passiveRadiatorTuningHz } from './passiveRadiator.js'

export interface SweepOptions extends SamplingOptions {
  filter?: FilterChain
}

/** Lossless reference resonance used to seed numerical sampling, not a measured peak. */
export function referenceResonanceHz(input: CircuitInput): number {
  // Also ensures a lumped port has a positive area and effective length.
  createCircuit(input)
  if (input.port?.ductPath)
    return ductPathTuning(
      input.port.ductPath,
      input.volumeM3,
      input.medium.soundSpeedMps,
    )
  if (input.passiveRadiator)
    return passiveRadiatorTuningHz(input.passiveRadiator, input.volumeM3, input.medium)
  return input.port
    ? (input.medium.soundSpeedMps / (2 * Math.PI)) *
        Math.sqrt(
          input.port.areaM2! / (input.volumeM3 * input.port.effectiveLengthM!),
        )
    : input.driver.fsHz *
        Math.sqrt(
          1 + (input.driver.vasM3 * (input.quantity ?? 1)) / input.volumeM3,
        )
}

/** Apply amplifier voltage transfer to every dependent phasor and magnitude.
 * Impedance is independent of drive in this linear model. Powers scale by |H|².
 */
function filteredPoint(
  point: CircuitPoint,
  filter: FilterChain | undefined,
): CircuitPoint {
  if (!filter) return point
  const transfer = composeFilters(point.frequency, filter)
  const gain = magnitude(transfer)
  const pressure = mul(point.pressurePa, transfer)
  const result = {
    ...point,
    pressurePa: pressure,
    currentAmps: mul(point.currentAmps, transfer),
    coneVolumeVelocityM3s: mul(point.coneVolumeVelocityM3s, transfer),
    mouthVolumeVelocityM3s: mul(point.mouthVolumeVelocityM3s, transfer),
    ...(point.radiatorVolumeVelocityM3s === undefined ? {} : {
      radiatorVolumeVelocityM3s: mul(point.radiatorVolumeVelocityM3s, transfer),
      radiatorExcursionPeakM: point.radiatorExcursionPeakM! * gain,
    }),
    splDb: pressureSplDb(pressure),
    coneExcursionPeakM: point.coneExcursionPeakM * gain,
    portVelocityPeakMps: point.portVelocityPeakMps * gain,
    portMach: point.portMach * gain,
    realInputPowerWatts: point.realInputPowerWatts * gain ** 2,
    coilLossWatts: point.coilLossWatts * gain ** 2,
  }
  if (
    ![
      ...Object.values(result.pressurePa),
      ...Object.values(result.currentAmps),
      ...Object.values(result.coneVolumeVelocityM3s),
      ...Object.values(result.mouthVolumeVelocityM3s),
      ...Object.values(result.radiatorVolumeVelocityM3s ?? {}),
      result.radiatorExcursionPeakM ?? 0,
      result.splDb,
      result.coneExcursionPeakM,
      result.portVelocityPeakMps,
      result.portMach,
      result.realInputPowerWatts,
      result.coilLossWatts,
    ].every(Number.isFinite)
  )
    throw new RangeError(
      'Filtered circuit evaluation exceeds finite numerical support.',
    )
  return result
}

export function sweepCircuit(input: CircuitInput, options: SweepOptions) {
  const circuit = createCircuit(input)
  const resonanceHz = referenceResonanceHz(input)
  const landmarks = [
    input.driver.fsHz,
    resonanceHz,
    ...(options.landmarksHz ?? []),
  ]
  if (input.passiveRadiator) landmarks.push(passiveRadiatorResonanceHz(input.passiveRadiator))
  if (options.filter?.highpassHz !== undefined)
    landmarks.push(options.filter.highpassHz)
  if (options.filter?.lowpassHz !== undefined)
    landmarks.push(options.filter.lowpassHz)
  for (const stage of options.filter?.digital?.stages ?? []) {
    if (stage.kind !== 'biquad') landmarks.push(stage.frequencyHz)
  }
  const sampled = sampleAdaptive(
    (frequency) => filteredPoint(circuit(frequency), options.filter),
    (p) => [
      p.pressurePa.re,
      p.pressurePa.im,
      magnitude(p.impedanceOhms),
      p.coneExcursionPeakM,
      p.portVelocityPeakMps,
      p.radiatorExcursionPeakM ?? 0,
    ],
    { ...options, landmarksHz: landmarks },
  )
  return {
    points: sampled.samples.map((sample) => sample.value),
    sampling: sampled.diagnostics,
    referenceResonanceHz: resonanceHz,
    model: {
      validation: 'equation' as const,
      amplitudeConvention:
        'RMS phasors; peak excursion and port speed' as const,
      propagationDelayIncluded: false as const,
    },
  }
}
