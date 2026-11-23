import { composeFilters, type FilterChain } from './filters.js'

export interface OperatingPoint {
  frequency: number
  coneExcursionMeters: number
  portVelocity: number
  portMach: number
  impedanceOhms: number
  splDb?: number
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
  const perDriverVoltage = Math.sqrt(wattsPerDriver * nominalOhmsPerDriver)
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
  if (!positive(referenceAmplifierVoltage))
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
    if (positive(source.xmaxMeters) && point.coneExcursionMeters > 0)
      consider(
        'excursion',
        (referenceAmplifierVoltage * source.xmaxMeters) /
          point.coneExcursionMeters /
          gain,
        point,
      )
    if (maxPortMach !== undefined && point.portMach > 0)
      consider(
        'port-mach',
        (referenceAmplifierVoltage * maxPortMach) / point.portMach / gain,
        point,
      )
    if (positive(source.ratedPowerWattsPerDriver) && coilLoss > 0)
      consider(
        'thermal-proxy',
        referenceAmplifierVoltage *
          Math.sqrt(source.ratedPowerWattsPerDriver / coilLoss),
        point,
      )
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
            Math.log10(
              (selected[1].value * limitingGain) / referenceAmplifierVoltage,
            ),
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
