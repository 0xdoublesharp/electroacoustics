import { composeFilters, type FilterChain } from './filters.js'
import { magnitude } from './complex.js'
import type { CircuitInput, CircuitPoint } from './circuit.js'

export interface OperatingPoint {
  frequency: number
  coneExcursionMeters: number
  portVelocity: number
  portMach: number
  impedanceOhms: number
  splDb?: number
  radiatorExcursionPeakM?: number
}

export interface OperatingSource {
  perDriverReferenceVoltage: number
  seriesDriversPerString: number
  parallelStrings: number
  dcResistancePerDriver: number
  xmaxMeters: number
  ratedPowerWattsPerDriver: number
  points: OperatingPoint[]
}

export interface OperatingMaximum {
  value: number
  frequency: number
}

export interface OperatingScenario {
  wattsPerDriver: number
  nominalOhmsPerDriver: number
  nominalTotalWatts: number
  perDriverVoltage: number
  amplifierVoltage: number
  minHz: number
  maxHz: number
  excursion: OperatingMaximum
  excursionRatio: number | null
  portVelocity: OperatingMaximum
  portMach: OperatingMaximum
  coilLossWattsPerDriver: OperatingMaximum
  nominalRatingRatio: number | null
}

export interface VoltageLimitOptions {
  /** Optional consistency check. The source wiring determines this by default. */
  referenceAmplifierVoltage?: number
  maxPortMach?: number
  filter?: Readonly<FilterChain>
}

export type VoltageLimitingFactor = 'excursion' | 'port-mach' | 'thermal-proxy'

export type OutputLimitingFactor = VoltageLimitingFactor | 'amplifier-voltage' | 'amplifier-current' | 'radiator-excursion'

export interface OutputLimitOptions {
  filter?: Readonly<FilterChain>
  maxPortMach?: number
  maxAmplifierVoltageRms?: number
  maxAmplifierCurrentRms?: number
  maxRadiatorExcursionPeakM?: number
  /** Planned amplifier RMS voltage at unity DSP gain. */
  driveVoltageRms?: number
}

export interface FilteredVoltageLimit {
  safeAmplifierVoltage: number
  limitingFactor: VoltageLimitingFactor
  limitingFrequency: number
  /** Filtered SPL at the limiting frequency, not the maximum SPL in a band. */
  safeSplDbAtLimitingFrequency: number | null
  evaluatedFrequencyRange: { minHz: number; maxHz: number }
  candidates: Record<VoltageLimitingFactor, OperatingMaximum | null>
  atReference: {
    maxExcursionMeters: OperatingMaximum
    maxPortMach: OperatingMaximum
    maxCoilLossWattsPerDriver: OperatingMaximum
  }
  metadata: {
    model: 'small-signal-scaling'
    thermalBasis: 'steady-state-i2r-proxy'
    nominalWattsAreCoilHeat: false
  }
}

const positive = (value: number) => Number.isFinite(value) && value > 0
const nonnegative = (value: number) => Number.isFinite(value) && value >= 0
const positiveNormal = (value: number) =>
  Number.isFinite(value) && value >= 2 ** -1022

function linearVoltageLimit(
  rating: number,
  response: number,
  reference: number,
  gain: number,
): number {
  const numerator = reference * rating
  const unfiltered = numerator / response
  if (positiveNormal(numerator) && positiveNormal(unfiltered))
    return unfiltered / gain
  return Math.exp(
    Math.log(reference) + Math.log(rating) - Math.log(response) - Math.log(gain),
  )
}

function thermalVoltageLimit(
  rating: number,
  resistance: number,
  impedance: number,
  parallel: number,
  gain: number,
): number {
  const currentLimit = Math.sqrt(rating) / Math.sqrt(resistance)
  const voltageAtUnityGain = currentLimit * impedance
  const voltage = voltageAtUnityGain / gain
  if (
    positiveNormal(currentLimit) &&
    positiveNormal(voltageAtUnityGain) &&
    positiveNormal(voltage)
  )
    return voltage * parallel
  return Math.exp(
    (Math.log(rating) - Math.log(resistance)) / 2 +
      Math.log(impedance) + Math.log(parallel) - Math.log(gain),
  )
}

function visitSpeakerLimits(
  source: OperatingSource, point: OperatingPoint, reference: number, gain: number,
  maxPortMach: number | undefined, consider: (factor: VoltageLimitingFactor, voltage: number) => void,
): void {
  if (positive(source.xmaxMeters) && point.coneExcursionMeters > 0)
    consider('excursion', linearVoltageLimit(source.xmaxMeters, point.coneExcursionMeters, reference, gain))
  if (maxPortMach !== undefined && point.portMach > 0)
    consider('port-mach', linearVoltageLimit(maxPortMach, point.portMach, reference, gain))
  if (positive(source.ratedPowerWattsPerDriver))
    consider('thermal-proxy', thermalVoltageLimit(source.ratedPowerWattsPerDriver,
      source.dcResistancePerDriver, point.impedanceOhms, source.parallelStrings, gain))
}

function validateSource(source: OperatingSource): void {
  if (
    !positive(source.perDriverReferenceVoltage) ||
    !positive(source.dcResistancePerDriver) ||
    !positive(source.seriesDriversPerString) ||
    !positive(source.parallelStrings) ||
    !Number.isInteger(source.seriesDriversPerString) ||
    !Number.isInteger(source.parallelStrings) ||
    source.points.length === 0
  )
    throw new RangeError(
      'Operating checks require positive wiring and simulation data.',
    )
  source.points.forEach((point, index) => {
    if (
      !positive(point.frequency) ||
      !positive(point.impedanceOhms) ||
      !nonnegative(point.coneExcursionMeters) ||
      !nonnegative(point.portVelocity) ||
      !nonnegative(point.portMach) ||
      (point.splDb !== undefined && !Number.isFinite(point.splDb)) ||
      (index > 0 && point.frequency <= source.points[index - 1]!.frequency)
    )
      throw new RangeError('Operating simulation samples are invalid.')
  })
}

function maximum(): OperatingMaximum {
  return { value: -Infinity, frequency: 0 }
}

function collect(
  max: OperatingMaximum,
  value: number,
  frequency: number,
): void {
  if (!Number.isFinite(value))
    throw new RangeError('Operating drive exceeds the supported numeric range.')
  if (value > max.value) Object.assign(max, { value, frequency })
}

/** Small-signal sinusoidal estimates, not a temperature or limiter model. */
export function analyzeOperatingDrive(
  source: OperatingSource,
  wattsPerDriver: number,
  nominalOhmsPerDriver: number,
  attenuationDb: (frequency: number) => number,
): OperatingScenario {
  validateSource(source)
  if (!positive(wattsPerDriver) || !positive(nominalOhmsPerDriver))
    throw new RangeError(
      'Operating drive and nominal impedance must be positive.',
    )
  const wattsOhms = wattsPerDriver * nominalOhmsPerDriver
  const perDriverVoltage = positiveNormal(wattsOhms)
    ? Math.sqrt(wattsOhms)
    : Math.sqrt(wattsPerDriver) * Math.sqrt(nominalOhmsPerDriver)
  const amplifierVoltage = perDriverVoltage * source.seriesDriversPerString
  const scale = perDriverVoltage / source.perDriverReferenceVoltage
  const nominalTotalWatts =
    wattsPerDriver * source.seriesDriversPerString * source.parallelStrings
  if (
    ![perDriverVoltage, amplifierVoltage, scale, nominalTotalWatts].every(
      Number.isFinite,
    )
  )
    throw new RangeError('Operating drive exceeds the supported numeric range.')
  const excursion = maximum()
  const portVelocity = maximum()
  const portMach = maximum()
  const coilLossWattsPerDriver = maximum()
  for (const point of source.points) {
    const db = attenuationDb(point.frequency)
    if (!Number.isFinite(db))
      throw new RangeError('Operating filter gain is invalid.')
    const gain = 10 ** (db / 20)
    collect(
      excursion,
      point.coneExcursionMeters * scale * gain,
      point.frequency,
    )
    collect(portVelocity, point.portVelocity * scale * gain, point.frequency)
    collect(portMach, point.portMach * scale * gain, point.frequency)
    const current =
      (amplifierVoltage * gain) / point.impedanceOhms / source.parallelStrings
    collect(
      coilLossWattsPerDriver,
      current * current * source.dcResistancePerDriver,
      point.frequency,
    )
  }
  return {
    wattsPerDriver,
    nominalOhmsPerDriver,
    nominalTotalWatts,
    perDriverVoltage,
    amplifierVoltage,
    minHz: source.points[0]!.frequency,
    maxHz: source.points.at(-1)!.frequency,
    excursion,
    excursionRatio: positive(source.xmaxMeters)
      ? excursion.value / source.xmaxMeters
      : null,
    portVelocity,
    portMach,
    coilLossWattsPerDriver,
    nominalRatingRatio: positive(source.ratedPowerWattsPerDriver)
      ? wattsPerDriver / source.ratedPowerWattsPerDriver
      : null,
  }
}

export function analyzeFilteredVoltageLimit(
  source: OperatingSource,
  options: Readonly<VoltageLimitOptions>,
): FilteredVoltageLimit {
  validateSource(source)
  const sourceAmplifierReference =
    source.perDriverReferenceVoltage * source.seriesDriversPerString
  const referenceAmplifierVoltage =
    options.referenceAmplifierVoltage ?? sourceAmplifierReference
  if (
    !positive(sourceAmplifierReference) ||
    !positive(referenceAmplifierVoltage)
  )
    throw new RangeError(
      'Reference amplifier voltage must be positive and finite.',
    )
  if (
    Math.abs(referenceAmplifierVoltage - sourceAmplifierReference) >
    Number.EPSILON *
      Math.max(referenceAmplifierVoltage, sourceAmplifierReference) *
      4
  )
    throw new RangeError(
      'Reference amplifier voltage must match the source per-driver reference voltage and series wiring.',
    )
  const maxPortMach = options.maxPortMach
  if (maxPortMach !== undefined && !positive(maxPortMach))
    throw new RangeError('Maximum port Mach must be positive and finite.')
  if (
    !positive(source.xmaxMeters) &&
    !positive(source.ratedPowerWattsPerDriver) &&
    maxPortMach === undefined
  )
    throw new RangeError(
      'At least one finite operating constraint is required.',
    )

  const referenceExcursion = maximum()
  const referencePortMach = maximum()
  const referenceCoilLoss = maximum()
  const candidates: FilteredVoltageLimit['candidates'] = {
    excursion: null,
    'port-mach': null,
    'thermal-proxy': null,
  }
  const consider = (
    factor: VoltageLimitingFactor,
    voltage: number,
    point: OperatingPoint,
  ) => {
    if (!positive(voltage))
      throw new RangeError(
        'Operating constraints exceed the supported numeric range.',
      )
    const current = candidates[factor]
    if (!current || voltage < current.value) {
      candidates[factor] = { value: voltage, frequency: point.frequency }
    }
  }

  for (const point of source.points) {
    const transfer = composeFilters(point.frequency, options.filter)
    const gain = Math.hypot(transfer.re, transfer.im)
    const excursion = point.coneExcursionMeters * gain
    const mach = point.portMach * gain
    const current =
      (referenceAmplifierVoltage * gain) /
      point.impedanceOhms /
      source.parallelStrings
    const coilLoss = current * current * source.dcResistancePerDriver
    collect(referenceExcursion, excursion, point.frequency)
    collect(referencePortMach, mach, point.frequency)
    collect(referenceCoilLoss, coilLoss, point.frequency)
    if (gain === 0) continue
    // Bound I²R directly so rounding the reference power to zero cannot remove
    // an active thermal constraint.
    visitSpeakerLimits(source, point, referenceAmplifierVoltage, gain, maxPortMach,
      (factor, voltage) => consider(factor, voltage, point))
  }
  const selected = Object.entries(candidates)
    .filter(
      (entry): entry is [VoltageLimitingFactor, OperatingMaximum] =>
        entry[1] !== null,
    )
    .sort((a, b) => a[1].value - b[1].value)[0]
  const limitingPoint = selected
    ? source.points.find((point) => point.frequency === selected[1].frequency)
    : undefined
  if (!selected || !limitingPoint)
    throw new RangeError(
      'Operating constraints do not produce a finite voltage limit.',
    )
  const limitingTransfer = composeFilters(
    limitingPoint.frequency,
    options.filter,
  )
  const limitingGain = Math.hypot(limitingTransfer.re, limitingTransfer.im)
  return {
    safeAmplifierVoltage: selected[1].value,
    limitingFactor: selected[0],
    limitingFrequency: selected[1].frequency,
    safeSplDbAtLimitingFrequency:
      limitingPoint.splDb === undefined
        ? null
        : limitingPoint.splDb +
          20 *
            (Math.log10(selected[1].value) + Math.log10(limitingGain) -
              Math.log10(referenceAmplifierVoltage)),
    evaluatedFrequencyRange: {
      minHz: source.points[0]!.frequency,
      maxHz: source.points.at(-1)!.frequency,
    },
    candidates,
    atReference: {
      maxExcursionMeters: referenceExcursion,
      maxPortMach: referencePortMach,
      maxCoilLossWattsPerDriver: referenceCoilLoss,
    },
    metadata: {
      model: 'small-signal-scaling',
      thermalBasis: 'steady-state-i2r-proxy',
      nominalWattsAreCoilHeat: false,
    },
  }
}

/** Adapt unfiltered, reference-voltage circuit points for the operating analyzers. */
export function operatingSourceFromCircuit(
  input: CircuitInput,
  points: readonly CircuitPoint[],
  limits: Pick<OperatingSource, 'xmaxMeters' | 'ratedPowerWattsPerDriver'>,
): OperatingSource {
  const series = input.seriesDrivers ?? 1
  return {
    ...limits, perDriverReferenceVoltage: input.voltageRms / series,
    seriesDriversPerString: series, parallelStrings: (input.quantity ?? 1) / series,
    dcResistancePerDriver: input.driver.reOhms,
    points: points.map((point) => ({ frequency: point.frequency,
      coneExcursionMeters: point.coneExcursionPeakM, portVelocity: point.portVelocityPeakMps,
      portMach: point.portMach, impedanceOhms: magnitude(point.impedanceOhms), splDb: point.splDb,
      ...(point.radiatorExcursionPeakM === undefined ? {} : { radiatorExcursionPeakM: point.radiatorExcursionPeakM }),
    })),
  }
}

/** Single-tone ceiling and planned-drive margin at each unfiltered source sample. */
export function analyzeOutputLimit(source: OperatingSource, options: Readonly<OutputLimitOptions> = {}) {
  validateSource(source)
  const reference = source.perDriverReferenceVoltage * source.seriesDriversPerString
  const { maxPortMach, maxAmplifierVoltageRms, maxAmplifierCurrentRms, maxRadiatorExcursionPeakM, driveVoltageRms } = options
  if (!positive(reference) || [maxPortMach, maxAmplifierVoltageRms, maxAmplifierCurrentRms,
    maxRadiatorExcursionPeakM, driveVoltageRms].some((value) => value !== undefined && !positive(value)))
    throw new RangeError('Output analysis requires positive, finite limits and voltages')

  let bandInputLimit: OperatingMaximum | null = null
  const points = source.points.map((point) => {
    let maxTerminalVoltageRms = Infinity
    let limitingFactor: OutputLimitingFactor | null = null
    const consider = (factor: OutputLimitingFactor, voltage: number) => {
      if (!positive(voltage)) throw new RangeError('Output limit exceeds the supported numeric range')
      if (voltage < maxTerminalVoltageRms) {
        maxTerminalVoltageRms = voltage
        limitingFactor = factor
      }
    }
    visitSpeakerLimits(source, point, reference, 1, maxPortMach, consider)
    if (maxAmplifierVoltageRms !== undefined) consider('amplifier-voltage', maxAmplifierVoltageRms)
    if (maxAmplifierCurrentRms !== undefined)
      consider('amplifier-current', maxAmplifierCurrentRms * point.impedanceOhms)
    if (maxRadiatorExcursionPeakM !== undefined) {
      const travel = point.radiatorExcursionPeakM
      if (travel === undefined || !nonnegative(travel)) throw new RangeError('Missing or invalid radiator excursion')
      if (travel > 0) consider('radiator-excursion', linearVoltageLimit(maxRadiatorExcursionPeakM, travel, reference, 1))
    }

    const gain = magnitude(composeFilters(point.frequency, options.filter))
    const terminal = limitingFactor === null ? null : maxTerminalVoltageRms
    const inputLimit = terminal === null || gain === 0 ? null : terminal / gain
    if (inputLimit !== null && !positive(inputLimit)) throw new RangeError('DSP input limit exceeds the supported numeric range')
    if (inputLimit !== null && (bandInputLimit === null || inputLimit < bandInputLimit.value))
      bandInputLimit = { value: inputLimit, frequency: point.frequency }
    const maxSplDb = terminal === null || gain === 0 || point.splDb === undefined ? null :
      point.splDb + 20 * (Math.log10(terminal) - Math.log10(reference))
    const driveGainDb = driveVoltageRms === undefined || gain === 0 ? null :
      20 * (Math.log10(driveVoltageRms) + Math.log10(gain) - Math.log10(reference))
    return {
      frequency: point.frequency, limitingFactor: limitingFactor as OutputLimitingFactor | null,
      maxTerminalVoltageRms: terminal, maxInputVoltageRms: inputLimit, maxSplDb,
      plannedSplDb: driveGainDb === null || point.splDb === undefined ? null : point.splDb + driveGainDb,
      headroomDb: inputLimit === null || driveVoltageRms === undefined ? null :
        20 * (Math.log10(inputLimit) - Math.log10(driveVoltageRms)),
    }
  })
  return { points, bandInputLimit: bandInputLimit as OperatingMaximum | null }
}
