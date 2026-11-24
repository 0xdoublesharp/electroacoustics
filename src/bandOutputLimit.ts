import { bandCircuit, type DistributedPortIntervals } from './bandCircuit.js'
import { bandFilter } from './bandFilter.js'
import { createCircuit, type CircuitInput } from './circuit.js'
import { distributedPort } from './ductBounds.js'
import { dyadicIntervals, outwardBinary64, type DyadicInterval } from './dyadicInterval.js'
import {
  binary64Intervals, enclosedOr, exact, ln10, minus, one, quotient, times, type IntervalMath,
} from './interval.js'
import type { OutputLimitOptions } from './operating.js'

export interface BandOutputLimitOptions extends Omit<OutputLimitOptions, 'driveVoltageRms'> {
  minHz: number
  maxHz: number
  xmaxMeters?: number
  ratedPowerWattsPerDriver?: number
  /** Maximum certified gap between the safe voltage and the true ceiling. Default 0.1 dB. */
  toleranceDb?: number
  /** Maximum number of interval bisections. Default 2048. */
  maxSplits?: number
}

interface FrequencyInterval {
  minHz: number
  maxHz: number
}

export interface BandOutputLimit {
  status: 'resolved' | 'unresolved' | 'unbounded'
  /** Guaranteed feasible voltage at unity DSP gain, when an enclosure is available. */
  safeInputVoltageRms: number | null
  /** No larger voltage is feasible. */
  upperInputVoltageRms: number | null
  errorBoundDb: number | null
  splits: number
  unresolvedIntervals: FrequencyInterval[]
  reason: 'subdivision-budget' | 'frequency-resolution' | 'numeric-range' | 'certificate-rejected' | null
  certificate?: BandOutputCertificate
}

const positive = (value: number) => Number.isFinite(value) && value > 0

export interface BandOutputCertificate {
  version: 1
  request: string
  spans: readonly FrequencyInterval[]
  witnessHz: number
  safeInputVoltageRms: number
  upperInputVoltageRms: number
  errorBoundDb: number
}

const maxSpans = 8193

function validateRequest(input: CircuitInput, options: Readonly<BandOutputLimitOptions>): void {
  const {
    minHz, maxHz, toleranceDb = 0.1, maxSplits = 2048,
    xmaxMeters = 0, ratedPowerWattsPerDriver = 0,
    maxPortMach, maxAmplifierVoltageRms, maxAmplifierCurrentRms, maxRadiatorExcursionPeakM,
  } = options
  if (!positive(minHz) || !positive(maxHz) || maxHz <= minHz || !positive(toleranceDb) ||
      !Number.isSafeInteger(maxSplits) || maxSplits < 0 || maxSplits >= maxSpans)
    throw new RangeError('Band requires positive increasing frequencies, positive tolerance, and maxSplits from 0 to 8192')
  if (maxRadiatorExcursionPeakM !== undefined && !input.passiveRadiator)
    throw new RangeError('A radiator excursion limit requires a passive radiator')
  if ([xmaxMeters, ratedPowerWattsPerDriver].some((value) => !Number.isFinite(value) || value < 0) ||
      [maxPortMach, maxAmplifierVoltageRms, maxAmplifierCurrentRms, maxRadiatorExcursionPeakM]
        .some((value) => value !== undefined && !positive(value)))
    throw new RangeError('Band output limits must be finite and positive when enabled')
  createCircuit(input)
}

function needsCircuit(input: CircuitInput, options: Readonly<BandOutputLimitOptions>) {
  return (options.xmaxMeters ?? 0) > 0 || (options.ratedPowerWattsPerDriver ?? 0) > 0 ||
    options.maxAmplifierCurrentRms !== undefined || options.maxRadiatorExcursionPeakM !== undefined ||
    (options.maxPortMach !== undefined && input.port !== undefined)
}

function createUsage<T>(
  input: CircuitInput, options: Readonly<BandOutputLimitOptions>, math: IntervalMath<T>,
  filterGain: (frequency: T) => T,
  distributed?: DistributedPortIntervals<T>,
) {
  const { exact, maximum, quotient, root, times, one, zero } = math
  const {
    xmaxMeters = 0, ratedPowerWattsPerDriver = 0,
    maxPortMach, maxAmplifierVoltageRms, maxAmplifierCurrentRms, maxRadiatorExcursionPeakM,
  } = options
  const circuit = needsCircuit(input, options) ? bandCircuit(input, math, maxPortMach !== undefined, distributed) : undefined
  const coilCurrentFactor = ratedPowerWattsPerDriver > 0 ? quotient(
    root(quotient(exact(input.driver.reOhms), exact(ratedPowerWattsPerDriver))),
    exact((input.quantity ?? 1) / (input.seriesDrivers ?? 1)),
  ) : zero
  const amplifierFactor = maxAmplifierVoltageRms === undefined ? zero : quotient(one, exact(maxAmplifierVoltageRms))
  return (frequency: T) => {
    const active = [amplifierFactor]
    if (circuit) {
      const point = circuit(frequency)
      if (xmaxMeters > 0) active.push(quotient(point.excursion, exact(xmaxMeters)))
      if (maxPortMach !== undefined) active.push(quotient(point.portMach, exact(maxPortMach)))
      if (ratedPowerWattsPerDriver > 0) active.push(times(point.current, coilCurrentFactor))
      if (maxAmplifierCurrentRms !== undefined)
        active.push(quotient(point.current, exact(maxAmplifierCurrentRms)))
      if (maxRadiatorExcursionPeakM !== undefined)
        active.push(quotient(point.radiatorExcursion, exact(maxRadiatorExcursionPeakM)))
    }
    return times(filterGain(frequency), maximum(active))
  }
}

function dyadicUsage(input: CircuitInput, options: Readonly<BandOutputLimitOptions>) {
  const math = dyadicIntervals
  const gain = bandFilter(options.filter, options.maxHz, math)
  if (gain === null) return null
  const path = input.port?.ductPath
  const { soundSpeedMps, densityKgM3 } = input.medium
  const distributed = path && needsCircuit(input, options)
    ? distributedPort(path, soundSpeedMps, densityKgM3) : undefined
  return createUsage(input, options, math, gain, distributed)
}

function dyadicSpan({ minHz, maxHz }: FrequencyInterval): DyadicInterval {
  return { lo: dyadicIntervals.exact(minHz).lo, hi: dyadicIntervals.exact(maxHz).hi }
}

function dyadicGap(safe: DyadicInterval, upper: DyadicInterval): DyadicInterval {
  const math = dyadicIntervals
  const excess = math.minus(math.quotient(upper, safe), math.one)
  return math.times(excess, math.quotient(math.exact(20), math.ln10))
}

function requestKey(input: CircuitInput, options: Readonly<BandOutputLimitOptions>): string {
  // Sorting object keys gives a stable binding across JSON round trips. Loss
  // qualities may be infinite, so preserve their explicit value.
  return JSON.stringify([input, options], (_, value: unknown) => {
    if (value === Infinity) return '+Infinity'
    if (typeof value === 'object' && value !== null && !Array.isArray(value)) {
      const record = value as Record<string, unknown>
      return Object.fromEntries(Object.keys(record).sort().map((key) => [key, record[key]]))
    }
    return value
  })
}

function replayCertificate(
  input: CircuitInput, options: Readonly<BandOutputLimitOptions>, certificate: Readonly<BandOutputCertificate>,
): boolean {
  const { minHz, maxHz, toleranceDb = 0.1, maxSplits = 2048 } = options
  const { spans, witnessHz, safeInputVoltageRms: safe, upperInputVoltageRms: upper, errorBoundDb: gap } = certificate
  if (certificate.version !== 1 || certificate.request !== requestKey(input, options) ||
      !Array.isArray(spans) || spans.length === 0 || spans.length > maxSplits + 1 ||
      !Number.isFinite(witnessHz) || witnessHz < minHz || witnessHz > maxHz ||
      !positive(safe) || !positive(upper) || safe > upper || !positive(gap) || gap > toleranceDb)
    return false
  const math = dyadicIntervals
  const usage = dyadicUsage(input, options)
  if (usage === null) return false
  const safeInterval = math.exact(safe)
  let expectedLeft = minHz
  for (const span of spans) {
    if (span.minHz !== expectedLeft || !Number.isFinite(span.maxHz) ||
        span.maxHz <= span.minHz || span.maxHz > maxHz) return false
    const bound = usage(dyadicSpan(span))
    if (math.times(safeInterval, bound).hi > math.one.hi) return false
    expectedLeft = span.maxHz
  }
  if (expectedLeft !== maxHz) return false
  const witness = usage(math.exact(witnessHz))
  const upperInterval = math.exact(upper)
  if (math.times(upperInterval, witness).lo < math.one.lo) return false
  return dyadicGap(safeInterval, upperInterval).hi <= math.exact(gap).lo
}

function confirmPartial(
  input: CircuitInput, options: Readonly<BandOutputLimitOptions>, spans: readonly FrequencyInterval[],
  witnessHz: number, safe: number | null, upper: number | null,
) {
  const math = dyadicIntervals
  const usage = enclosedOr(() => dyadicUsage(input, options), null)
  const safeInputVoltageRms = safe !== null && usage !== null && enclosedOr(() =>
    spans.every((span) => math.times(math.exact(safe), usage(dyadicSpan(span))).hi <= math.one.hi),
  false) ? safe : null
  const upperInputVoltageRms = upper !== null && usage !== null && enclosedOr(() =>
    math.times(math.exact(upper), usage(math.exact(witnessHz))).lo >= math.one.lo, false) ? upper : null
  const errorBoundDb = safeInputVoltageRms !== null && upperInputVoltageRms !== null
    ? enclosedOr(() => outwardBinary64(
      dyadicGap(math.exact(safeInputVoltageRms), math.exact(upperInputVoltageRms)),
    ).hi, null) : null
  return { safeInputVoltageRms, upperInputVoltageRms, errorBoundDb }
}

/** Independently replay an envelope certificate against the original request. */
export function verifyBandOutputCertificate(
  input: CircuitInput, options: Readonly<BandOutputLimitOptions>, certificate: Readonly<BandOutputCertificate>,
): boolean {
  try {
    validateRequest(input, options)
    return enclosedOr(() => replayCertificate(input, options, certificate), false)
  } catch {
    // Malformed external certificates and invalid requests fail closed.
    return false
  }
}

/** Enclose the continuous, small-signal single-tone limit over a closed band. */
export function analyzeBandOutputLimit(
  input: CircuitInput, options: Readonly<BandOutputLimitOptions>,
): BandOutputLimit {
  validateRequest(input, options)
  const { minHz, maxHz, toleranceDb = 0.1, maxSplits = 2048, maxAmplifierVoltageRms } = options
  const band = { minHz, maxHz }
  const circuitNeeded = needsCircuit(input, options)
  const empty = {
    safeInputVoltageRms: null, upperInputVoltageRms: null, errorBoundDb: null, splits: 0,
  }
  const filterGain = enclosedOr(() => bandFilter(options.filter, maxHz, binary64Intervals), undefined)
  if (filterGain === undefined)
    return { ...empty, status: 'unresolved', unresolvedIntervals: [band], reason: 'numeric-range' }
  if (filterGain === null || (!circuitNeeded && maxAmplifierVoltageRms === undefined))
    return { ...empty, status: 'unbounded', unresolvedIntervals: [], reason: null }
  const usage = enclosedOr(() => {
    if (input.port?.ductPath && circuitNeeded) {
      const evaluate = dyadicUsage(input, options)
      return (minHz: number, maxHz: number) => outwardBinary64(evaluate!(dyadicSpan({ minHz, maxHz })))
    }
    const evaluate = createUsage(input, options, binary64Intervals, filterGain)
    return (min: number, max: number) => evaluate({ lo: min, hi: max })
  }, null)
  if (usage === null)
    return { ...empty, status: 'unresolved', unresolvedIntervals: [band], reason: 'numeric-range' }

  const enclose = (minHz: number, maxHz: number) =>
    enclosedOr(() => usage(minHz, maxHz), { lo: 0, hi: Infinity })

  const dbFactor = quotient(exact(20), ln10)
  const bracket = (witness: number, ceiling: number) => {
    const safe = Number.isFinite(ceiling) ? enclosedOr(() => quotient(one, exact(ceiling)).lo, null) : null
    const upper = enclosedOr(() => quotient(one, exact(witness)).hi, null)
    const gap = safe !== null && upper !== null ? enclosedOr(() => {
      // ln(r) ≤ r − 1. This is slightly conservative near the target and
      // keeps the bound independent of the runtime log implementation.
      const excess = minus(quotient(exact(upper), exact(safe)), one)
      return times(excess, dbFactor).hi
    }, null) : null
    return { safe, upper, gap }
  }

  let lower = 0
  let witnessHz = minHz
  const witness = (hz: number, candidate: number) => {
    if (candidate > lower) {
      lower = candidate
      witnessHz = hz
    }
  }
  witness(minHz, enclose(minHz, minHz).lo)
  witness(maxHz, enclose(maxHz, maxHz).lo)
  for (const stage of options.filter?.digital?.stages ?? []) {
    if (stage.kind !== 'biquad' && stage.frequencyHz > minHz && stage.frequencyHz < maxHz)
      witness(stage.frequencyHz, enclose(stage.frequencyHz, stage.frequencyHz).lo)
  }
  const bound = (minHz: number, maxHz: number) => {
    const value = enclose(minHz, maxHz)
    // Every such interval contains a frequency, so its lower bound is also a witness.
    witness(minHz, value.lo)
    return { minHz, maxHz, ceiling: value.hi }
  }
  const pending = [bound(minHz, maxHz)]
  let splits = 0
  for (;;) {
    const worst = pending.reduce((a, b) => a.ceiling >= b.ceiling ? a : b)
    const { safe, upper, gap } = bracket(lower, worst.ceiling)
    if (safe !== null && upper !== null && gap !== null && gap <= toleranceDb) {
      const certificate: BandOutputCertificate = {
        version: 1, request: requestKey(input, options), witnessHz,
        spans: pending.map(({ minHz, maxHz }) => ({ minHz, maxHz })),
        safeInputVoltageRms: safe, upperInputVoltageRms: upper, errorBoundDb: gap,
      }
      if (enclosedOr(() => replayCertificate(input, options, certificate), false))
        return { status: 'resolved', safeInputVoltageRms: safe, upperInputVoltageRms: upper,
          errorBoundDb: gap, splits, unresolvedIntervals: [], reason: null, certificate }
      return { ...empty, status: 'unresolved', splits, unresolvedIntervals: [band], reason: 'certificate-rejected' }
    }
    const midpoint = worst.minHz + (worst.maxHz - worst.minHz) / 2
    const atResolution = midpoint <= worst.minHz || midpoint >= worst.maxHz
    if (splits === maxSplits || atResolution) {
      const unresolvedIntervals = pending.filter((p) => {
        const local = bracket(lower, p.ceiling).gap
        return local === null || local > toleranceDb
      }).map(({ minHz, maxHz }) => ({ minHz, maxHz }))
      return { status: 'unresolved', ...confirmPartial(input, options, pending, witnessHz, safe, upper),
        splits, unresolvedIntervals,
        reason: atResolution ? 'frequency-resolution' : 'subdivision-budget' }
    }
    witness(midpoint, enclose(midpoint, midpoint).lo)
    pending.splice(pending.indexOf(worst), 1, bound(worst.minHz, midpoint), bound(midpoint, worst.maxHz))
    splits += 1
  }
}
