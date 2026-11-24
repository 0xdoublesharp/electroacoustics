import type { Complex } from './complex.js'

const pressureFloorPa = 1e-12
const referenceLogPa = Math.log10(20e-6)

/** SPL from an RMS phasor without forming a potentially overflowing pressure ratio. */
export function pressureSplDb({ re, im }: Complex): number {
  const scale = Math.max(Math.abs(re), Math.abs(im), pressureFloorPa)
  const normalized = Math.max(Math.hypot(re / scale, im / scale), pressureFloorPa / scale)
  return 20 * (Math.log10(scale) + Math.log10(normalized) - referenceLogPa)
}
