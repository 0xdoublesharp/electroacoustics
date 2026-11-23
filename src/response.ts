import type { CircuitInput, CircuitPoint } from './circuit.js'
import { magnitude } from './complex.js'
import { driverMotor } from './driverMotor.js'

export type ResponsePoint = Pick<CircuitPoint, 'frequency' | 'pressurePa' | 'splDb' | 'impedanceOhms'>
export type ResponseReference = { kind: 'band-peak' } | { kind: 'explicit'; splDb: number }

export interface ResponseSummaryOptions {
  band?: { minHz: number; maxHz: number }
  reference: ResponseReference
}

/** Ideal inductance-free, mass-controlled reference for a conventional LF alignment. */
export function massControlledSplDb(input: CircuitInput): number {
  const { driver, medium } = input
  const { mms, blSquared } = driverMotor(driver, medium)
  const bl = Math.sqrt(blSquared)
  const pressure = medium.densityKgM3 * input.voltageRms * bl * driver.sdM2 * (input.quantity ?? 1) /
    ((input.seriesDrivers ?? 1) * driver.reOhms * mms * (input.radiationSolidAngle ?? 2 * Math.PI) * (input.distanceM ?? 1))
  if (!Number.isFinite(pressure) || pressure <= 0)
    throw new RangeError('Invalid mass-controlled reference pressure')
  return 20 * (Math.log10(pressure) - Math.log10(20e-6))
}

/** Group delay on an ordered grid. Phase must move less than π per interval. */
export function responseGroupDelayMs(points: readonly Pick<ResponsePoint, 'frequency' | 'pressurePa'>[]): (number | null)[] {
  let previousHz = 0
  const phase = points.map(({ frequency, pressurePa }) => {
    if (!(frequency > previousHz) || ![frequency, pressurePa.re, pressurePa.im].every(Number.isFinite))
      throw new RangeError('Response requires finite phasors at increasing positive frequencies')
    previousHz = frequency
    return magnitude(pressurePa) > 0 ? Math.atan2(pressurePa.im, pressurePa.re) : null
  })
  const slopes = phase.slice(1).map((right, index) => {
    const left = phase[index]!
    if (right === null || left === null) return null
    const delta = right - left
    const width = points[index + 1]!.frequency - points[index]!.frequency
    return { width, value: -1000 * Math.atan2(Math.sin(delta), Math.cos(delta)) / (2 * Math.PI) / width }
  })
  return phase.map((_, index) => {
    const left = slopes[index - 1]
    const right = slopes[index]
    if (left && right) return (left.value * right.width + right.value * left.width) / (left.width + right.width)
    return left?.value ?? right?.value ?? null
  })
}

/** Low-side upward crossings use the full grid, even when the reference uses a band. */
export function summarizeResponse(points: readonly ResponsePoint[], options: ResponseSummaryOptions) {
  const delays = responseGroupDelayMs(points)
  const minHz = options.band?.minHz ?? points[0]?.frequency
  const maxHz = options.band?.maxHz ?? points.at(-1)?.frequency
  if (minHz === undefined || maxHz === undefined || minHz <= 0 || maxHz < minHz ||
      ![minHz, maxHz].every(Number.isFinite))
    throw new RangeError('Invalid response band')

  let minSplDb = Infinity
  let maxSplDb = -Infinity
  let minimumImpedance: { value: number; frequency: number } | null = null
  let maxGroupDelayMs: number | null = null
  for (const [index, point] of points.entries()) {
    const impedance = magnitude(point.impedanceOhms)
    if (![point.splDb, impedance].every(Number.isFinite)) throw new RangeError('Invalid response sample')
    if (point.frequency < minHz || point.frequency > maxHz) continue
    minSplDb = Math.min(minSplDb, point.splDb)
    maxSplDb = Math.max(maxSplDb, point.splDb)
    if (!minimumImpedance || impedance < minimumImpedance.value)
      minimumImpedance = { value: impedance, frequency: point.frequency }
    const delay = delays[index]!
    if (delay !== null) maxGroupDelayMs = Math.max(maxGroupDelayMs ?? -Infinity, delay)
  }
  if (!minimumImpedance) throw new RangeError('Response band contains no samples')
  const referenceSplDb = options.reference.kind === 'explicit' ? options.reference.splDb : maxSplDb
  if (!Number.isFinite(referenceSplDb)) throw new RangeError('Invalid response reference')

  function cutoff(dropDb: number): number | null {
    const level = referenceSplDb - dropDb
    for (let i = 1; i < points.length; i++) {
      const left = points[i - 1]!
      const right = points[i]!
      if (left.splDb < level && right.splDb >= level) {
        const t = (level - left.splDb) / (right.splDb - left.splDb)
        return left.frequency + t * (right.frequency - left.frequency)
      }
    }
    return null
  }

  return {
    band: { minHz, maxHz }, referenceKind: options.reference.kind, referenceSplDb,
    f3Hz: cutoff(3), f6Hz: cutoff(6), f10Hz: cutoff(10),
    minSplDb, maxSplDb, rippleDb: maxSplDb - minSplDb, minimumImpedance, maxGroupDelayMs,
  }
}
