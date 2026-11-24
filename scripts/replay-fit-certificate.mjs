// Verify a JSON impedance-fit certificate and emit its Lean replay theorem.
import { readFileSync } from 'node:fs'
import {
  verifyDriverImpedanceFitCertificate,
  verifyEnclosureImpedanceFitCertificate,
} from '../dist/index.js'

const mode = process.argv[3] ?? '--kernel'
if (process.argv.length < 3 || process.argv.length > 4 || !['--kernel', '--native'].includes(mode))
  throw new Error('Usage: node scripts/replay-fit-certificate.mjs certificate.json [--kernel|--native]')

const certificate = JSON.parse(readFileSync(process.argv[2], 'utf8'))
const request = JSON.parse(certificate.request, (_, value) => value === '+Infinity' ? Infinity : value)
const driver = certificate.kind === 'driver'
const [input, samples, parameters, options] = request
const verified = driver
  ? verifyDriverImpedanceFitCertificate(input, certificate)
  : certificate.kind === 'enclosure' &&
    verifyEnclosureImpedanceFitCertificate(input, samples, parameters, certificate, options)
if (!verified) throw new Error('The certificate does not match its impedance fit request')

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
const tuple = (...values) => `⟨${values.map(rat).join(', ')}⟩`
const optionalQuality = (value) => value === Infinity ? 'none' : `(some ${rat(value)})`
const optionalArray = (values) => values === undefined ? 'none' : `some ${list(values, rat)}`
const medium = ({ densityKgM3, soundSpeedMps }) => tuple(densityKgM3, soundSpeedMps)
const range = ({ min, max }) => tuple(min, max)
const bound = ({ lower, upper }) => tuple(lower, upper)

function sweep(samples) {
  return list(samples, ({ frequency, impedanceOhms }) => {
    const measurement = typeof impedanceOhms === 'number'
      ? `.magnitude ${rat(impedanceOhms)}`
      : `.complex ${rat(impedanceOhms.re)} ${rat(impedanceOhms.im)}`
    return `⟨${rat(frequency)}, ${measurement}⟩`
  })
}

function condition({ kind, massKg, volumeM3 }) {
  if (kind === 'added-mass') return `(.addedMass ${rat(massKg)})`
  if (kind === 'sealed-box') return `(.sealedBox ${rat(volumeM3)})`
  throw new Error('Unsupported driver perturbation')
}

function enclosure({ port, passiveRadiator: pr }) {
  if (port?.ductPath) throw new Error('Lean impedance replay requires a lumped port')
  if (port) return `(.vented ${rat(port.areaM2)} ${rat(port.effectiveLengthM)} ${optionalQuality(port.quality)})`
  if (pr) return `(.passive ${[
    pr.quantity ?? 1, pr.sdM2, pr.movingMassKg, pr.complianceMPerN, pr.mechanicalResistanceNsPerM,
  ].map(rat).join(' ')})`
  return '.sealed'
}

const driverKeys = ['fsHz', 'vasM3', 'qes', 'qms', 'reOhms', 'leHenries']
const enclosureKeys = {
  volumeM3: '.volume',
  leakageQuality: '.leakage',
  absorptionQuality: '.absorption',
  portQuality: '.portQuality',
  effectiveLengthM: '.effectiveLength',
  radiatorMassKg: '.radiatorMass',
}
const statuses = {
  'residual-target': '.residualTarget',
  stationary: '.stationary',
  'bound-constrained': '.boundConstrained',
  'poorly-identified': '.poorlyIdentified',
  stalled: '.stalled',
  'iteration-limit': '.iterationLimit',
}
const parameterCount = driver ? driverKeys.length : parameters.length
let leanRequest
if (driver) {
  const { initial, bounds, freeAir, perturbed, tolerance = 1e-9 } = input
  const ranges = driverKeys.map((key) => bounds?.[key] ?? (key === 'leHenries'
    ? { min: 0, max: Math.max(initial.leHenries * 4, 0.002) }
    : { min: initial[key] / 4, max: initial[key] * 4 }))
  leanRequest = `driverRequest ${rat(initial.sdM2)} ${medium(input.medium)}
    ${condition(perturbed.condition)}
    ${sweep(freeAir)}
    ${sweep(perturbed.samples)}
    (fun i => (${list(ranges, range)} : List Range).getD i ⟨0, 0⟩) ${rat(tolerance)}`
} else {
  const d = input.driver
  const leanInput = `⟨${tuple(...driverKeys.map((key) => d[key]), d.sdM2)}, ${medium(input.medium)},
      ${rat(input.volumeM3)}, ${rat(input.quantity ?? 1)}, ${rat(input.seriesDrivers ?? 1)},
      ${optionalQuality(input.leakageQuality)}, ${optionalQuality(input.absorptionQuality)},
      ${enclosure(input)}⟩`
  leanRequest = `enclosureRequest ${leanInput}
    (fun i => (${list(parameters, ({ parameter }) => enclosureKeys[parameter])} :
      List EnclosureParameter).getD i .volume)
    ${sweep(samples)}
    (fun i => (${list(parameters, range)} : List Range).getD i ⟨0, 0⟩)
    ${rat(options?.tolerance ?? 1e-9)}`
}

process.stdout.write(`import Electroacoustics.ImpedanceCertificate

open Electroacoustics.ImpedanceCertificate

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

def replayRequest : FitRequest ${parameterCount} :=
  ${leanRequest}

def replayCertificate : FitCertificate where
  version := ${certificate.version}
  kind := ${driver ? '.driver' : '.enclosure'}
  status := ${statuses[certificate.status]}
  values := ${list(certificate.values, rat)}
  rms := ${bound(certificate.rmsRelativeErrorBound)}
  pg := ${bound(certificate.projectedGradientBound)}
  sensitivityRank := ${certificate.sensitivityRank}
  sensitivityFloor := ${rat(certificate.sensitivityFloor)}
  preconditioner := ${optionalArray(certificate.preconditioner)}
  weakDirection := ${optionalArray(certificate.weakDirection)}

theorem replayAccepted : checkFitCertificate replayRequest replayCertificate = true := by
  decide +${mode.slice(2)}

theorem replayVerified : replayRequest.Verified replayCertificate :=
  checkFitCertificate_sound replayAccepted

#print axioms replayVerified
`)
