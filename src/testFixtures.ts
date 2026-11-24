import type { DuctPath } from './ductAcoustics.js'

// Synthetic inputs for analytic tests.
export const circuitFixture = {
  driver: {
    fsHz: 25,
    vasM3: 0.08,
    qes: 0.45,
    qms: 8,
    reOhms: 6,
    leHenries: 0,
    sdM2: 0.05,
  },
  volumeM3: 0.07,
  voltageRms: 2.83,
  medium: { densityKgM3: 1.2041, soundSpeedMps: 343 },
  leakageQuality: Infinity,
  absorptionQuality: Infinity,
}

// Independent integration of pressure/volume-flow conservation, without
// transfer matrices or the transformed Webster equation used by production.
export function odeFixture(p: DuctPath, frequency: number, steps = 4000) {
  const omega = 2 * Math.PI * frequency
  const density = 1.2
  const outletArea = p.sections.at(-1)!.outletAreaSquareMeters
  let pressure = omega * density * p.outletCorrectionMeters / outletArea
  let flow = 1
  let peak = 1 / outletArea
  for (const section of p.sections.slice().reverse()) {
    const { lengthMeters: length, inletAreaSquareMeters: inlet, outletAreaSquareMeters: outlet } = section
    const areaAt = (x: number) => section.profile === 'exponential'
      ? inlet * (outlet / inlet) ** (x / length)
      : (Math.sqrt(inlet) + (Math.sqrt(outlet) - Math.sqrt(inlet)) * x / length) ** 2
    const derivative = (x: number, pressure: number, flow: number) => [
      -omega * density * (p.inertanceFactor ?? 1) * flow / areaAt(x),
      omega * (p.complianceFactor ?? 1) * areaAt(x) * pressure / (density * 343 ** 2),
    ]
    const h = -length / steps
    for (let i = 0; i < steps; i++) {
      const x = length + i * h
      const a = derivative(x, pressure, flow)
      const b = derivative(x + h / 2, pressure + h * a[0]! / 2, flow + h * a[1]! / 2)
      const c = derivative(x + h / 2, pressure + h * b[0]! / 2, flow + h * b[1]! / 2)
      const d = derivative(x + h, pressure + h * c[0]!, flow + h * c[1]!)
      pressure += h / 6 * (a[0]! + 2 * b[0]! + 2 * c[0]! + d[0]!)
      flow += h / 6 * (a[1]! + 2 * b[1]! + 2 * c[1]! + d[1]!)
      peak = Math.max(peak, Math.abs(flow) / areaAt(x + h))
    }
  }
  const inletLength = p.inletCorrectionMeters + (p.junctionInertanceLengthsMeters ?? [])
    .reduce((sum, length) => sum + length, 0)
  pressure += omega * density * inletLength * flow / p.sections[0]!.inletAreaSquareMeters
  return { reactance: pressure / flow, ratio: 1 / flow, peak: peak / Math.abs(flow) / p.count }
}
