// Verify a JSON duct certificate and emit its Lean replay theorem.
import { readFileSync } from 'node:fs'
import { verifyDuctPeakVelocityCertificate, verifyDuctTuningCertificate } from '../dist/index.js'

const mode = process.argv[3] ?? '--kernel'
if (process.argv.length < 3 || process.argv.length > 4 || !['--kernel', '--native'].includes(mode))
  throw new Error('Usage: node scripts/replay-duct-certificate.mjs certificate.json [--kernel|--native]')

const certificate = JSON.parse(readFileSync(process.argv[2], 'utf8'))
const tuning = Array.isArray(certificate?.earlierSpans)
const peak = Array.isArray(certificate?.sectionSpans)
if (tuning === peak) throw new Error('Expected one duct tuning or peak velocity certificate')

const [path, first, speed, ...remaining] = JSON.parse(certificate.request)
const [density, tolerance, maxSplits] = tuning ? [undefined, ...remaining] : remaining
const options = { relativeTolerance: tolerance, maxSplits }
const verified = tuning
  ? verifyDuctTuningCertificate(path, first, speed, certificate, options)
  : verifyDuctPeakVelocityCertificate(path, first, speed, density, certificate, options)
if (!verified) throw new Error('The certificate does not match its duct request')

const bits = new DataView(new ArrayBuffer(8))
function rat(value) {
  if (!Number.isFinite(value)) throw new Error('Expected a finite binary64 value')
  bits.setFloat64(0, value)
  const encoded = bits.getBigUint64(0)
  const exponent = Number((encoded >> 52n) & 2047n)
  let numerator = (encoded & ((1n << 52n) - 1n)) + (exponent === 0 ? 0n : 1n << 52n)
  if (encoded >> 63n) numerator = -numerator
  if (numerator === 0n) return '(0 : ℚ)'
  let power = Math.max(1, exponent) - 1075
  while (power < 0 && numerator % 2n === 0n) {
    numerator >>= 1n
    power += 1
  }
  return power < 0
    ? `((${numerator} : ℚ) / ${1n << BigInt(-power)})`
    : `(${numerator << BigInt(power)} : ℚ)`
}

const list = (values, format) => `[${values.map(format).join(', ')}]`
const span = (lo, hi) => `⟨${rat(lo)}, ${rat(hi)}⟩`
const section = ({ lengthMeters, inletAreaSquareMeters, outletAreaSquareMeters, profile }) =>
  `⟨${rat(lengthMeters)}, ${rat(inletAreaSquareMeters)}, ${rat(outletAreaSquareMeters)}, .${profile}⟩`
const detail = tuning
  ? `earlierSpans := ${list(certificate.earlierSpans, ({ minHz, maxHz }) => span(minHz, maxHz))}`
  : `witnessSection := ${certificate.witness.sectionIndex}
  witnessFraction := ${rat(certificate.witness.fraction)}
  sectionSpans := ${list(certificate.sectionSpans, spans =>
    list(spans, ({ minFraction, maxFraction }) => span(minFraction, maxFraction)))}`
const certificateType = tuning ? 'TuningCertificate' : 'PeakVelocityCertificate'
const checker = `check${certificateType}`
const parameters = (tuning ? [first, speed] : [first, speed, density]).map(rat).join(' ')

process.stdout.write(`import Electroacoustics.DuctCertificate

open Electroacoustics.DuctCertificate Electroacoustics.DuctInterval

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

def replayPath : DuctPath where
  sections := ${list(path.sections, section)}
  count := ${rat(path.count)}
  inletCorrection := ${rat(path.inletCorrectionMeters)}
  outletCorrection := ${rat(path.outletCorrectionMeters)}
  junctionInertances := ${list(path.junctionInertanceLengthsMeters ?? [], rat)}
  inertanceFactor := ${rat(path.inertanceFactor ?? 1)}
  complianceFactor := ${rat(path.complianceFactor ?? 1)}

def replayCertificate : ${certificateType} where
  lower := ${rat(certificate.lower)}
  upper := ${rat(certificate.upper)}
  ${detail}
  relativeTolerance := ${rat(certificate.relativeTolerance)}

theorem replayAccepted : ${checker} 160 replayPath ${parameters} replayCertificate = true := by
  decide +${mode.slice(2)}

theorem replayVerified : type_of% (${checker}_sound replayAccepted) :=
  ${checker}_sound replayAccepted

#print axioms replayVerified
`)
