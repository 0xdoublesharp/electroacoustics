// Generate a Lean proof from a JSON BandOutputCertificate. The request
// recorded in the certificate becomes exact rational data in the theorem.
import { readFileSync } from 'node:fs'
import { designBiquad, verifyBandOutputCertificate } from '../dist/index.js'

const mode = process.argv[3] ?? '--kernel'
if (process.argv.length < 3 || process.argv.length > 4 || !['--kernel', '--native'].includes(mode))
  throw new Error('Usage: node scripts/replay-band-certificate.mjs certificate.json [--kernel|--native]')
const certificate = JSON.parse(readFileSync(process.argv[2], 'utf8'))
const [input, options] = JSON.parse(certificate.request, (_, value) =>
  value === '+Infinity' ? Infinity : value)
if (!verifyBandOutputCertificate(input, options, certificate))
  throw new Error('The certificate does not match a supported band result')

const bits = new DataView(new ArrayBuffer(8))
const rat = (value) => {
  if (!Number.isFinite(value)) throw new Error('Expected a finite binary64 value')
  bits.setFloat64(0, value)
  const encoded = bits.getBigUint64(0)
  const e = Number((encoded >> 52n) & 2047n)
  let numerator = (encoded & ((1n << 52n) - 1n)) + (e === 0 ? 0n : 1n << 52n)
  if (encoded >> 63n) numerator = -numerator
  if (numerator === 0n) return '(0 : ℚ)'
  let power = Math.max(1, e) - 1075
  while (power < 0 && numerator % 2n === 0n) {
    numerator >>= 1n
    power += 1
  }
  return power < 0
    ? `((${numerator} : ℚ) / ${1n << BigInt(-power)})`
    : `(${numerator << BigInt(power)} : ℚ)`
}
const optional = (value) => value === undefined || value === Infinity ? 'none' : `some ${rat(value)}`
const optionalRating = (value) => optional(value || undefined)
const span = ({ minHz, maxHz }) => `⟨${rat(minHz)}, ${rat(maxHz)}⟩`

const { driver: d, medium: { densityKgM3, soundSpeedMps }, port, passiveRadiator: pr } = input
const circuitLimits = options.xmaxMeters || options.ratedPowerWattsPerDriver ||
  options.maxAmplifierCurrentRms || options.maxRadiatorExcursionPeakM || (options.maxPortMach && port)
function replayDuct(path, quality) {
  const [section] = path.sections
  const junctions = path.junctionInertanceLengthsMeters ?? []
  if (path.sections.length === 1 && section.profile === 'straight' &&
      path.inletCorrectionMeters === 0 && path.outletCorrectionMeters === 0 && junctions.length === 0) {
    const parameters = [path.count, section.inletAreaSquareMeters, section.lengthMeters].map(rat).join(' ')
    return `.openUniformDuct ${parameters} 0 ${rat(path.inertanceFactor ?? 1)}
      ${rat(path.complianceFactor ?? 1)} (${optional(quality)})`
  }
  const sections = path.sections.map((s) =>
    `⟨${[s.lengthMeters, s.inletAreaSquareMeters, s.outletAreaSquareMeters].map(rat).join(', ')}, .${s.profile}⟩`)
  return `.distributedDuct {
    sections := [${sections.join(', ')}]
    count := ${rat(path.count)}
    inletCorrection := ${rat(path.inletCorrectionMeters)}
    outletCorrection := ${rat(path.outletCorrectionMeters)}
    junctionInertances := [${junctions.map(rat).join(', ')}]
    inertanceFactor := ${rat(path.inertanceFactor ?? 1)}
    complianceFactor := ${rat(path.complianceFactor ?? 1)}
  } (${optional(quality)})`
}
const cavity = !circuitLimits ? '.sealed' :
  port?.ductPath ? replayDuct(port.ductPath, port.quality) :
  port ? `.vented ${rat(port.areaM2)} ${rat(port.effectiveLengthM)} (${optional(port.quality)})` :
  pr ? `.passive ${rat(pr.quantity ?? 1)} ${rat(pr.sdM2)} ${rat(pr.movingMassKg)}
    ${rat(pr.complianceMPerN)} ${rat(pr.mechanicalResistanceNsPerM)}` : '.sealed'
const filter = options.filter ?? {}
const sampleRate = filter.digital?.sampleRateHz ?? 1
const stages = (filter.digital?.stages ?? []).map((stage) => {
  const biquad = stage.kind === 'biquad' ? stage : designBiquad(stage, sampleRate)
  return `⟨${[biquad.b0, biquad.b1, biquad.b2, biquad.a1, biquad.a2].map(rat).join(', ')}⟩`
})

const tolerance = rat(options.toleranceDb ?? 0.1)
const tactic = `decide +${mode.slice(2)}`
const spanProofs = certificate.spans.map((current, index) => {
  const left = index === 0 ? 'replayBand.lo' : rat(certificate.spans[index - 1].maxHz)
  return `theorem replaySpan${index} :
    checkSpan replayEnclosure replayCertificate.safe ${left} replayBand.hi ${span(current)} = true := by
  ${tactic}`
})
const coverProof = certificate.spans.map((_, index) => `  apply checkSpans_cons_of_checks replaySpan${index}`).join('\n')

process.stdout.write(`import ElectroacousticsReplay

open Electroacoustics.BandModel
open Electroacoustics.BandCertificate
open Electroacoustics.Interval

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

def replayCircuit : Circuit where
  driver := ⟨${[d.fsHz, d.vasM3, d.qes, d.qms, d.reOhms, d.leHenries, d.sdM2].map(rat).join(', ')}⟩
  volume := ${rat(input.volumeM3)}
  density := ${rat(densityKgM3)}
  soundSpeed := ${rat(soundSpeedMps)}
  count := ${rat(input.quantity ?? 1)}
  series := ${rat(input.seriesDrivers ?? 1)}
  leakage := ${optional(input.leakageQuality)}
  absorption := ${optional(input.absorptionQuality)}
  cavity := ${cavity}

def replayLimits : Limits where
  excursion := ${optionalRating(options.xmaxMeters)}
  mach := ${optional(port ? options.maxPortMach : undefined)}
  thermal := ${optionalRating(options.ratedPowerWattsPerDriver)}
  current := ${optional(options.maxAmplifierCurrentRms)}
  voltage := ${optional(options.maxAmplifierVoltageRms)}
  radiator := ${optional(options.maxRadiatorExcursionPeakM)}

def replayDsp : Dsp where
  gainDb := ${rat(filter.gainDb ?? 0)}
  highpass := ${optional(filter.highpassHz)}
  butterworth := ${filter.highpassType === 'BW24'}
  lowpass := ${optional(filter.lowpassHz)}
  sampleRate := ${rat(sampleRate)}
  stages := [${stages.join(', ')}]

def replayBand : Box := ${span(options)}

def replayCertificate : Certificate where
  spans := [${certificate.spans.map(span).join(',\n    ')}]
  witnessHz := ${rat(certificate.witnessHz)}
  safe := ${rat(certificate.safeInputVoltageRms)}
  upper := ${rat(certificate.upperInputVoltageRms)}
  errorDb := ${rat(certificate.errorBoundDb)}

def replayEnclosure : Box → Option Box :=
  replayEnvelope replayCircuit replayLimits replayDsp replayCertificate.safe replayCertificate.upper

theorem replayWitness :
    checkWitness replayEnclosure replayBand 2.3025850925 ${tolerance} replayCertificate = true := by
  ${tactic}

${spanProofs.join('\n\n')}

theorem replayAccepted :
    checkModel replayCircuit replayLimits replayDsp replayBand ${tolerance} replayCertificate = true := by
  apply checkModel_of_checks replayWitness
${coverProof}
  ${tactic}

theorem replayVerified :
    let u := exactUsage replayCircuit replayLimits replayDsp
    (∀ f, replayBand.Contains f → (replayCertificate.safe : ℝ) * u f ≤ 1) ∧
    (∀ drive : ℝ, (replayCertificate.upper : ℝ) < drive →
      ∃ f, replayBand.Contains f ∧ 1 < drive * u f) ∧
    (∀ drive : ℝ, (replayCertificate.safe : ℝ) ≤ drive →
      drive ≤ (replayCertificate.upper : ℝ) →
      20 / Real.log 10 * Real.log (drive / (replayCertificate.safe : ℝ)) ≤
        (replayCertificate.errorDb : ℝ)) :=
  checkModel_sound replayCircuit replayLimits replayDsp
  (by decide +kernel : replayBand.lo < replayBand.hi) replayAccepted

#print axioms replayVerified
`)
