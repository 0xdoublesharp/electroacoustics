import {
  createCircuit,
  type CircuitInput,
  type CircuitPoint,
} from './circuit.js'
import { referenceResonanceHz } from './sweep.js'

export type SensitivityParameter =
  | 'volumeM3'
  | 'driver.fsHz'
  | 'driver.vasM3'
  | 'driver.qes'
  | 'driver.qms'
  | 'driver.reOhms'
  | 'driver.leHenries'
  | 'driver.sdM2'
  | 'leakageQuality'
  | 'absorptionQuality'
  | 'port.areaM2'
  | 'port.effectiveLengthM'
  | 'port.quality'
  | 'port.lengthScale'
export interface SensitivityVariation {
  parameter: SensitivityParameter
  values: readonly number[]
}
export interface SensitivityOptions {
  minHz: number
  maxHz: number
  points?: number
}
const parameters: readonly string[] = [
  'volumeM3',
  'driver.fsHz',
  'driver.vasM3',
  'driver.qes',
  'driver.qms',
  'driver.reOhms',
  'driver.leHenries',
  'driver.sdM2',
  'leakageQuality',
  'absorptionQuality',
  'port.areaM2',
  'port.effectiveLengthM',
  'port.quality',
  'port.lengthScale',
]

function withParameter(
  input: CircuitInput,
  parameter: SensitivityParameter,
  value: number,
): CircuitInput {
  if (
    !parameters.includes(parameter) ||
    !Number.isFinite(value) ||
    (parameter === 'driver.leHenries' ? value < 0 : value <= 0)
  )
    throw new RangeError('Scenario parameter or value is invalid')
  const copy = { ...input, driver: { ...input.driver } }
  if (parameter.startsWith('driver.')) {
    copy.driver[parameter.slice(7) as keyof CircuitInput['driver']] = value
  } else if (parameter.startsWith('port.')) {
    if (!input.port)
      throw new RangeError('Port scenario requires a vented circuit')
    copy.port = { ...input.port }
    if (parameter === 'port.lengthScale') {
      if (copy.port.effectiveLengthM !== undefined)
        copy.port.effectiveLengthM *= value
      if (input.port.ductPath)
        copy.port.ductPath = {
          ...input.port.ductPath,
          sections: input.port.ductPath.sections.map((section) => ({
            ...section,
            lengthMeters: section.lengthMeters * value,
          })),
        }
    } else {
      if (input.port.ductPath && parameter !== 'port.quality')
        throw new RangeError(
          'Distributed port scenarios use port.lengthScale; lumped area/length would be ignored',
        )
      copy.port[
        parameter.slice(5) as 'areaM2' | 'effectiveLengthM' | 'quality'
      ] = value
    }
  } else {
    copy[parameter as 'volumeM3' | 'leakageQuality' | 'absorptionQuality'] =
      value
  }
  return copy
}
function summarize(points: CircuitPoint[], input: CircuitInput) {
  return {
    referenceResonanceHz: referenceResonanceHz(input),
    peakSplDb: Math.max(...points.map((p) => p.splDb)),
    maxExcursionPeakM: Math.max(...points.map((p) => p.coneExcursionPeakM)),
    maxPortMach: Math.max(...points.map((p) => p.portMach)),
  }
}

/** One-at-a-time physical input scenarios. No enclosure re-solving or automatic
 * retuning occurs. The envelope covers these sampled scenarios, not combinations,
 * probabilities, measurement error or a bound on continuous-frequency extrema.
 */
export function analyzeSensitivity(
  input: CircuitInput,
  variations: readonly SensitivityVariation[],
  options: SensitivityOptions,
) {
  const count = options.points ?? 241
  if (
    !Number.isFinite(options.minHz) ||
    options.minHz <= 0 ||
    !Number.isFinite(options.maxHz) ||
    options.maxHz <= options.minHz ||
    !Number.isSafeInteger(count) ||
    count < 3 ||
    count > 1024
  )
    throw new RangeError(
      'Sensitivity requires positive increasing bounds and 3 to 1024 grid points',
    )
  const total = variations.reduce((sum, v) => sum + v.values.length, 0)
  if (variations.length > 64 || total > 64)
    throw new RangeError('Sensitivity supports at most 64 scenarios')
  const baselineCircuit = createCircuit(input)
  const cases = variations.flatMap((variation) =>
    variation.values.map((value) => {
      const scenario = withParameter(input, variation.parameter, value)
      return {
        parameter: variation.parameter,
        value,
        input: scenario,
        evaluate: createCircuit(scenario),
      }
    }),
  )
  const frequencies = Array.from({ length: count }, (_, i) =>
    Math.exp(
      Math.log(options.minHz) +
        (i / (count - 1)) * (Math.log(options.maxHz) - Math.log(options.minHz)),
    ),
  )
  frequencies[0] = options.minHz
  frequencies[count - 1] = options.maxHz
  for (const source of [input, ...cases.map((c) => c.input)]) {
    const resonance = referenceResonanceHz(source)
    if (resonance > options.minHz && resonance < options.maxHz)
      frequencies.push(resonance)
  }
  const grid = [...new Set(frequencies)].sort((a, b) => a - b)
  const points = grid.map(baselineCircuit)
  const baseline = { points, metrics: summarize(points, input) }
  const scenarios = cases.map((scenario, index) => {
    const points = grid.map(scenario.evaluate)
    const metrics = summarize(points, scenario.input)
    return {
      id: `scenario-${index + 1}`,
      parameter: scenario.parameter,
      value: scenario.value,
      points,
      metrics,
      resonanceDeltaHz:
        metrics.referenceResonanceHz - baseline.metrics.referenceResonanceHz,
      maxAbsSplDeltaDb: Math.max(
        ...points.map((p, i) => Math.abs(p.splDb - baseline.points[i]!.splDb)),
      ),
    }
  })
  const ranking = variations
    .map((v) => ({
      parameter: v.parameter,
      maxAbsSplDeltaDb: Math.max(
        0,
        ...scenarios
          .filter((s) => s.parameter === v.parameter)
          .map((s) => s.maxAbsSplDeltaDb),
      ),
    }))
    .filter(
      (entry, i, list) =>
        list.findIndex((other) => other.parameter === entry.parameter) === i,
    )
    .sort((a, b) => b.maxAbsSplDeltaDb - a.maxAbsSplDeltaDb)
  return {
    baseline,
    scenarios,
    ranking,
    envelope: grid.map((frequency, index) => {
      const levels = [
        baseline.points[index]!.splDb,
        ...scenarios.map((s) => s.points[index]!.splDb),
      ]
      return {
        frequency,
        minSplDb: Math.min(...levels),
        maxSplDb: Math.max(...levels),
      }
    }),
    metadata: {
      validation: 'equation' as const,
      interpretation:
        'one-at-a-time scenarios; not confidence intervals' as const,
      grid: 'common logarithmic grid plus lossless resonance landmarks' as const,
      minHz: options.minHz,
      maxHz: options.maxHz,
      evaluations: grid.length * (scenarios.length + 1),
    },
  }
}
