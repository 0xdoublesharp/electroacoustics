/** One-dimensional, rigid-wall, lossless Webster duct sections. */
export interface DuctSection {
  lengthMeters: number
  inletAreaSquareMeters: number
  outletAreaSquareMeters: number
  profile: 'straight' | 'conical' | 'exponential'
}
export interface DuctPath {
  sections: DuctSection[]
  count: number
  inletCorrectionMeters: number
  outletCorrectionMeters: number
  /** Signed lumped inertance lengths (junctions, mutual coupling, cavity),
   * referenced to the inlet (throat) area and lumped at the inlet. Negative
   * values (e.g. a mitred bend) are allowed while the path's total effective
   * inertance stays positive. Absent = none. */
  junctionInertanceLengthsMeters?: number[]
  /** Reactive boundary-layer factors (Stinson 1991 thin-layer asymptote):
   * the sections' effective density is rho*inertanceFactor and their
   * compliance per length is scaled by complianceFactor. End corrections are
   * radiation masses and are not scaled. Absent = 1 (lossless rigid duct). */
  inertanceFactor?: number
  complianceFactor?: number
}

function positive(value: number): boolean {
  return Number.isFinite(value) && value > 0
}
// Numerical support limits, deliberately wider than cabinet-scale geometry.
// Reject unsupported requests before allocating or searching, rather than
// silently emitting nonfinite responses or blocking a UI update.
function inRange(value: number, low: number, high: number) {
  return Number.isFinite(value) && value >= low && value <= high
}
function finiteResult(...values: number[]) {
  if (!values.every(Number.isFinite))
    throw new RangeError('Duct geometry exceeds finite numerical support')
}
function validateAcoustic(
  frequency: number,
  soundSpeed: number,
  density: number,
) {
  if (
    !inRange(frequency, 1e-6, 1e6) ||
    !inRange(soundSpeed, 1, 1e6) ||
    !inRange(density, 1e-6, 1e6)
  )
    throw new RangeError(
      'Duct frequency or medium exceeds supported numerical range',
    )
}
function junctionLength(path: DuctPath) {
  return path.junctionInertanceLengthsMeters?.reduce((a, b) => a + b, 0) ?? 0
}
function validateExtensions(path: DuctPath) {
  const junctions = path.junctionInertanceLengthsMeters
  if (
    junctions !== undefined &&
    (!Array.isArray(junctions) ||
      junctions.length > 128 ||
      !junctions.every((x) => inRange(x, -1000, 1000)))
  )
    throw new RangeError('Duct junction inertances must be finite and bounded')
  for (const factor of [path.inertanceFactor, path.complianceFactor])
    if (factor !== undefined && !inRange(factor, 1e-3, 1e3))
      throw new RangeError('Duct boundary-layer factors must be positive')
}
function validate(path: DuctPath) {
  validateExtensions(path)
  if (
    !Number.isInteger(path.count) ||
    path.count <= 0 ||
    path.count > 10000 ||
    path.sections.length > 128 ||
    !path.sections.length ||
    !Number.isFinite(path.inletCorrectionMeters) ||
    path.inletCorrectionMeters < 0 ||
    !Number.isFinite(path.outletCorrectionMeters) ||
    path.outletCorrectionMeters < 0
  )
    throw new RangeError(
      'Invalid duct path or more than 128 sections / 10000 parallel ducts',
    )
  if (path.inletCorrectionMeters > 1000 || path.outletCorrectionMeters > 1000)
    throw new RangeError(
      'Duct end correction exceeds supported 1000 meter range',
    )
  for (const s of path.sections) {
    if (
      ![
        s.lengthMeters,
        s.inletAreaSquareMeters,
        s.outletAreaSquareMeters,
      ].every(positive) ||
      !['straight', 'conical', 'exponential'].includes(s.profile) ||
      (s.profile === 'straight' &&
        s.inletAreaSquareMeters !== s.outletAreaSquareMeters)
    )
      throw new RangeError('Invalid duct section')
    if (
      !inRange(s.lengthMeters, 1e-9, 1000) ||
      !inRange(s.inletAreaSquareMeters, 1e-10, 1e4) ||
      !inRange(s.outletAreaSquareMeters, 1e-10, 1e4) ||
      !inRange(s.outletAreaSquareMeters / s.inletAreaSquareMeters, 1e-8, 1e8)
    )
      throw new RangeError(
        'Duct section exceeds supported length, area, or taper numerical range',
      )
  }
  if (
    path.junctionInertanceLengthsMeters !== undefined &&
    !(rawEquivalentLength(path) > 0)
  )
    throw new RangeError(
      'Duct junction inertances leave a non-positive total effective inertance',
    )
}

/** Inlet-area-referenced inertance length, per duct; count does not change length. */
export function ductPathEquivalentLength(path: DuctPath): number {
  validate(path)
  return rawEquivalentLength(path)
}
function rawEquivalentLength(path: DuctPath): number {
  const inlet = path.sections[0]!.inletAreaSquareMeters
  const mouth = path.sections.at(-1)!.outletAreaSquareMeters
  const sections = path.sections.reduce((sum, s) => {
    const ratio = s.outletAreaSquareMeters / s.inletAreaSquareMeters
    const factor =
      ratio === 1
        ? 1
        : s.profile === 'conical'
          ? 1 / Math.sqrt(ratio)
          : -Math.expm1(-Math.log(ratio)) / Math.log(ratio)
    return sum + ((s.lengthMeters * inlet) / s.inletAreaSquareMeters) * factor
  }, 0)
  const base =
    path.inletCorrectionMeters +
    (path.outletCorrectionMeters * inlet) / mouth +
    (path.inertanceFactor === undefined
      ? sections
      : sections * path.inertanceFactor)
  return path.junctionInertanceLengthsMeters === undefined
    ? base
    : base + junctionLength(path)
}

// [p_in,U_in] = [a,j*b;j*c,d] [p_out,U_out], with exp(j*omega*t).
// Webster: p'' + (S'/S)p' + k²p=0; y=sqrt(S)*p reduces it to
// y'' + [k²-(sqrt(S))''/sqrt(S)]y=0. The potential is zero for
// conical sections and constant for exponential sections, so these are exact
// section matrices, including below exponential cutoff. Reference:
// https://www.dsprelated.com/freebooks/pasp/Non_Cylindrical_Acoustic_Tubes.html
function sectionMatrix(
  s: DuctSection,
  omega: number,
  k: number,
  density: number,
) {
  const ratio = Math.sqrt(s.outletAreaSquareMeters / s.inletAreaSquareMeters)
  const g0 =
    s.profile === 'exponential'
      ? Math.log(ratio) / s.lengthMeters
      : (ratio - 1) / s.lengthMeters
  const g1 = s.profile === 'exponential' ? g0 : g0 / ratio
  const q2 = k * k - (s.profile === 'exponential' ? g0 * g0 : 0)
  const q = Math.sqrt(Math.abs(q2))
  const phase = q * s.lengthMeters
  const cosine = q2 >= 0 ? Math.cos(phase) : Math.cosh(phase)
  const sineOverQ =
    q === 0
      ? s.lengthMeters
      : (q2 >= 0 ? Math.sin(phase) : Math.sinh(phase)) / q
  const area = Math.sqrt(s.inletAreaSquareMeters * s.outletAreaSquareMeters)
  const sa = ratio * (cosine - g1 * sineOverQ)
  const sb = ((omega * density) / area) * sineOverQ
  const sc =
    (area / (omega * density)) *
    ((q2 + g0 * g1) * sineOverQ + (g1 - g0) * cosine)
  const sd = (cosine + g0 * sineOverQ) / ratio
  return { a: sa, b: sb, c: sc, d: sd }
}

/** Sections see rho*Fi and wavenumber k*sqrt(Fi*Fc); identity when absent. */
function sectionMedium(
  path: DuctPath,
  omega: number,
  speed: number,
  density: number,
) {
  const k = omega / speed
  if (path.inertanceFactor === undefined && path.complianceFactor === undefined)
    return { k, sectionDensity: density }
  const fi = path.inertanceFactor ?? 1,
    fc = path.complianceFactor ?? 1
  return { k: k * Math.sqrt(fi * fc), sectionDensity: density * fi }
}

function terms(
  path: DuctPath,
  frequency: number,
  speed: number,
  density: number,
) {
  const omega = 2 * Math.PI * frequency
  const { k, sectionDensity } = sectionMedium(path, omega, speed, density)
  let a = 1,
    b = 0,
    c = 0,
    d = 1
  for (const s of path.sections) {
    const {
      a: sa,
      b: sb,
      c: sc,
      d: sd,
    } = sectionMatrix(s, omega, k, sectionDensity)
    ;[a, b, c, d] = [
      a * sa - b * sc,
      a * sb + b * sd,
      c * sa + d * sc,
      d * sd - c * sb,
    ]
  }
  const outletX =
    (omega * density * path.outletCorrectionMeters) /
    path.sections.at(-1)!.outletAreaSquareMeters
  const denominator = d - c * outletX
  const numerator =
    a * outletX +
    b +
    ((omega *
      density *
      (path.junctionInertanceLengthsMeters === undefined
        ? path.inletCorrectionMeters
        : path.inletCorrectionMeters + junctionLength(path))) /
      path.sections[0]!.inletAreaSquareMeters) *
      denominator
  finiteResult(numerator, denominator)
  return { numerator, denominator }
}

/** Resistance is the total parallel-branch series resistance in Pa*s/m³.
 * End corrections are lumped inertances. The mouth is pressure-release;
 * no radiation resistance, directivity, bend loss or transverse modes are fitted.
 * mouthFlowRatio is total mouth flow / total throat flow.
 */
export function ductPathImpedance(
  path: DuctPath,
  frequency: number,
  soundSpeed: number,
  density: number,
  resistance = 0,
) {
  validate(path)
  validateAcoustic(frequency, soundSpeed, density)
  if (
    ![frequency, soundSpeed, density].every(positive) ||
    !Number.isFinite(resistance) ||
    resistance < 0
  )
    throw new RangeError('Invalid duct acoustic parameters')
  const { numerator, denominator } = terms(path, frequency, soundSpeed, density)
  // Bound exact pole evaluation to keep downstream complex arithmetic finite.
  const safeDenominator =
    Math.abs(denominator) < 1e-14
      ? (denominator < 0 ? -1 : 1) * 1e-14
      : denominator
  finiteResult(numerator / safeDenominator / path.count, 1 / safeDenominator)
  return {
    impedance: { re: resistance, im: numerator / safeDenominator / path.count },
    mouthFlowRatio: { re: 1 / safeDenominator, im: 0 },
  }
}

/** Cavity/duct reactive cancellation residual at one frequency, the
 * quantity ductPathTuning brackets: negative below the lowest tuning and
 * non-negative from it up to the first duct pole. It is linear in volume, so
 * two evaluations give the volume that tunes a path to a frequency. */
export function ductPathTuningResidual(
  path: DuctPath,
  volumeM3: number,
  frequency: number,
  soundSpeed: number,
): number {
  validate(path)
  if (
    !inRange(volumeM3, 0, 1e9) ||
    !inRange(soundSpeed, 1, 1e6) ||
    !inRange(frequency, 1e-6, 1e6)
  )
    throw new RangeError('Invalid cavity parameters')
  const t = terms(path, frequency, soundSpeed, 1)
  return (
    ((2 * Math.PI * frequency * volumeM3) / soundSpeed ** 2) * t.numerator -
    path.count * t.denominator
  )
}

/** Lowest cavity/duct reactive admittance cancellation, excluding duct poles. */
export function ductPathTuning(
  path: DuctPath,
  volumeM3: number,
  soundSpeed: number,
): number {
  validate(path)
  if (!inRange(volumeM3, 1e-12, 1e9) || !inRange(soundSpeed, 1, 1e6))
    throw new RangeError('Invalid cavity parameters')
  const length = ductPathEquivalentLength(path)
  const estimate =
    (soundSpeed / (2 * Math.PI)) *
    Math.sqrt(
      (path.count * path.sections[0]!.inletAreaSquareMeters) /
        (volumeM3 * length),
    )
  const physicalLength = path.sections.reduce(
    (sum, s) => sum + s.lengthMeters,
    0,
  )
  // Multiply admittance cancellation by the impedance numerator. This removes
  // tangent poles from the search, without mistaking a pole for a tuning root.
  const residual = (f: number) => {
    const t = terms(path, f, soundSpeed, 1)
    return (
      ((2 * Math.PI * f * volumeM3) / soundSpeed ** 2) * t.numerator -
      path.count * t.denominator
    )
  }
  let low = Math.min(estimate, soundSpeed / physicalLength) * 1e-6
  const step = Math.min(estimate / 32, soundSpeed / physicalLength / 128)
  let high = low
  for (let i = 0; i < 4096; i++) {
    high += step
    if (high > 1e6)
      throw new RangeError('Duct tuning exceeds supported 1 MHz search range')
    if (residual(high) >= 0) {
      for (let n = 0; n < 70; n++) {
        const mid = (low + high) / 2
        if (residual(mid) > 0) high = mid
        else low = mid
      }
      return (low + high) / 2
    }
    low = high
  }
  throw new RangeError(
    'Could not bracket duct tuning within 4096 bounded search steps',
  )
}

/** Maximum particle-speed magnitude per TOTAL inlet volume flow. Searches
 * each rigid-wall section, including interior standing-wave antinodes. */
export function ductPathPeakVelocityRatio(
  path: DuctPath,
  frequency: number,
  soundSpeed: number,
  density: number,
): number {
  const transfer = ductPathImpedance(path, frequency, soundSpeed, density)
  const omega = 2 * Math.PI * frequency
  const { k, sectionDensity } = sectionMedium(path, omega, soundSpeed, density)
  // Set per-duct mouth flow to one. Pressure is purely imaginary because the
  // mouth termination is inertive; inlet series loss does not change this ratio.
  let pressure =
    (omega * density * path.outletCorrectionMeters) /
    path.sections.at(-1)!.outletAreaSquareMeters
  let flow = 1
  let peak = 0
  let totalSamples = 0
  for (let i = path.sections.length - 1; i >= 0; i--) {
    const section = path.sections[i]!
    const areaAt = (fraction: number) =>
      section.profile === 'exponential'
        ? section.inletAreaSquareMeters *
          (section.outletAreaSquareMeters / section.inletAreaSquareMeters) **
            fraction
        : (Math.sqrt(section.inletAreaSquareMeters) +
            (Math.sqrt(section.outletAreaSquareMeters) -
              Math.sqrt(section.inletAreaSquareMeters)) *
              fraction) **
          2
    const velocityAt = (fraction: number) => {
      if (fraction >= 1) return Math.abs(flow) / section.outletAreaSquareMeters
      const area = areaAt(fraction)
      const m = sectionMatrix(
        {
          ...section,
          lengthMeters: section.lengthMeters * (1 - fraction),
          inletAreaSquareMeters: area,
        },
        omega,
        k,
        sectionDensity,
      )
      return Math.abs(m.d * flow - m.c * pressure) / area
    }
    // Resolve both oscillatory phase and area change. Refine each sampled local
    // maximum to avoid missing an antinode between samples. Cost grows with
    // acoustic length, rather than using a fixed fine mesh for every UI update.
    const samples = Math.max(
      16,
      Math.ceil(k * section.lengthMeters * 8),
      Math.ceil(
        Math.abs(
          Math.log(
            section.outletAreaSquareMeters / section.inletAreaSquareMeters,
          ),
        ) * 16,
      ),
    )
    totalSamples += samples + 1
    if (samples > 4096 || totalSamples > 16384)
      throw new RangeError(
        'Duct velocity requires too many samples: shorten path or reduce frequency',
      )
    const values = Array.from({ length: samples + 1 }, (_, j) =>
      velocityAt(j / samples),
    )
    peak = Math.max(peak, ...values)
    for (let j = 1; j < samples; j++) {
      if (values[j]! < values[j - 1]! || values[j]! < values[j + 1]!) continue
      let lo = (j - 1) / samples,
        hi = (j + 1) / samples
      for (let n = 0; n < 32; n++) {
        const left = lo + (hi - lo) / 3,
          right = hi - (hi - lo) / 3
        if (velocityAt(left) < velocityAt(right)) lo = left
        else hi = right
      }
      peak = Math.max(peak, velocityAt((lo + hi) / 2))
    }
    const m = sectionMatrix(section, omega, k, sectionDensity)
    ;[pressure, flow] = [
      m.a * pressure + m.b * flow,
      m.d * flow - m.c * pressure,
    ]
  }
  const result = (peak * Math.abs(transfer.mouthFlowRatio.re)) / path.count
  finiteResult(result)
  return result
}
