import { ductPathTuning, ductPathTuningResidual, type DuctPath } from './ductAcoustics.js'

export interface SealedAlignmentDriver {
  fsHz: number
  vasM3: number
  qts: number
  quantity?: number
}

function requirePositive(...values: number[]): void {
  if (values.some((value) => !Number.isFinite(value) || value <= 0))
    throw new RangeError('Alignment requires positive, finite values')
}

/** Ideal closed-box alignment. Volume is the acoustic compliance volume. */
export function sealedAlignment(driver: SealedAlignmentDriver, volumeM3: number) {
  const quantity = driver.quantity ?? 1
  requirePositive(driver.fsHz, driver.vasM3, driver.qts, quantity, volumeM3)
  if (!Number.isSafeInteger(quantity)) throw new RangeError('Invalid driver quantity')
  const alpha = (driver.vasM3 * quantity) / volumeM3
  const stiffening = Math.sqrt(1 + alpha)
  const fcHz = driver.fsHz * stiffening
  const qtc = driver.qts * stiffening
  const a = (1 / qtc) ** 2 - 2
  const f3Hz = fcHz * Math.sqrt((a + Math.hypot(a, 2)) / 2)
  requirePositive(alpha, fcHz, qtc, f3Hz)
  return { volumeM3, alpha, fcHz, qtc, f3Hz }
}

/** The ideal acoustic volume that achieves a target Qtc. */
export function sealedVolumeForQtc(driver: SealedAlignmentDriver, targetQtc: number) {
  if (!(targetQtc > driver.qts)) throw new RangeError('Target Qtc must exceed Qts')
  const ratio = targetQtc / driver.qts
  const alpha = ((targetQtc - driver.qts) / driver.qts) * (ratio + 1)
  return sealedAlignment(driver, (driver.vasM3 * (driver.quantity ?? 1)) / alpha)
}

/** Helmholtz tuning using total vent area and effective length including corrections. */
export function ventTuningHz(areaM2: number, volumeM3: number, effectiveLengthM: number, soundSpeedMps: number): number {
  requirePositive(areaM2, volumeM3, effectiveLengthM, soundSpeedMps)
  const frequency = (soundSpeedMps / (2 * Math.PI)) * Math.sqrt(areaM2 / (volumeM3 * effectiveLengthM))
  requirePositive(frequency)
  return frequency
}

/** Required effective vent length for a lumped Helmholtz alignment. */
export function ventLengthForTuning(areaM2: number, volumeM3: number, frequencyHz: number, soundSpeedMps: number): number {
  requirePositive(areaM2, volumeM3, frequencyHz, soundSpeedMps)
  const length = (areaM2 / volumeM3) * (soundSpeedMps / (2 * Math.PI * frequencyHz)) ** 2
  requirePositive(length)
  return length
}

/** Required acoustic volume for the fundamental tuning of a fixed distributed duct. */
export function ductVolumeForTuning(path: DuctPath, frequencyHz: number, soundSpeedMps: number): number {
  const intercept = ductPathTuningResidual(path, 0, frequencyHz, soundSpeedMps)
  const slope = ductPathTuningResidual(path, 1, frequencyHz, soundSpeedMps) - intercept
  if (!(slope > 0)) throw new RangeError('Target is outside the fundamental duct tuning branch')
  const volume = -intercept / slope
  requirePositive(volume)
  const tuning = ductPathTuning(path, volume, soundSpeedMps)
  if (Math.abs(tuning / frequencyHz - 1) > 1e-8)
    throw new RangeError('Target is outside the fundamental duct tuning branch')
  return volume
}

export interface DuctLengthTuningInput {
  targetHz: number
  soundSpeedMps: number
  minLengthM: number
  maxLengthM: number
  pathForLength: (lengthM: number) => DuctPath
  volumeForLength: (lengthM: number) => number
  toleranceM?: number
  /** Maximum bisection steps, from 1 through 200. Defaults to 80. */
  maxIterations?: number
}

/** Bisect one realizable interval on which fundamental tuning decreases with length.
 * A 'root' has a bracket no wider than toleranceM. Endpoint results retain the
 * input bracket. Iterations counts completed bisection steps.
 */
export function solveDuctLengthForTuning(input: DuctLengthTuningInput) {
  const { targetHz, soundSpeedMps, pathForLength, volumeForLength, toleranceM = 1e-9, maxIterations = 80 } = input
  let { minLengthM: low, maxLengthM: high } = input
  requirePositive(targetHz, soundSpeedMps, low, high, toleranceM)
  if (high < low) throw new RangeError('Invalid duct length bracket')
  if (!Number.isSafeInteger(maxIterations) || maxIterations < 1 || maxIterations > 200)
    throw new RangeError('Duct length iterations must be a safe integer from 1 through 200')
  const tuning = (lengthM: number) => ductPathTuning(pathForLength(lengthM), volumeForLength(lengthM), soundSpeedMps)
  let iterations = 0
  const bracket = () => ({ minLengthM: low, maxLengthM: high })
  const shortestTuning = tuning(low)
  if (shortestTuning < targetHz)
    return { lengthM: low, tuningHz: shortestTuning, status: 'shortest-tunes-low' as const, bracket: bracket(), iterations }
  const longestTuning = tuning(high)
  if (longestTuning > targetHz)
    return { lengthM: high, tuningHz: longestTuning, status: 'longest-tunes-high' as const, bracket: bracket(), iterations }
  while (iterations < maxIterations && high - low > toleranceM) {
    const mid = low + (high - low) / 2
    if (mid === low || mid === high)
      return { lengthM: mid, tuningHz: tuning(mid),
        status: 'resolution-limit' as const, bracket: bracket(), iterations }
    if (tuning(mid) > targetHz) low = mid
    else high = mid
    iterations++
  }
  const lengthM = low + (high - low) / 2
  const status = high - low <= toleranceM ? 'root' as const : 'budget-exhausted' as const
  return { lengthM, tuningHz: tuning(lengthM), status, bracket: bracket(), iterations }
}
