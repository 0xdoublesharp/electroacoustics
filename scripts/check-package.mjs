import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { copyFileSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { basename, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const root = fileURLToPath(new URL('../', import.meta.url))
const tsc = fileURLToPath(new URL('../node_modules/typescript/lib/tsc.js', import.meta.url))
const npmCli = process.env.npm_execpath
assert.ok(npmCli, 'Run this through npm run check:pack.')

const modules = [
  'alignment', 'bandCircuit', 'bandFilter', 'bandOutputLimit', 'binary64', 'biquadArithmetic', 'circuit', 'complex', 'driverMotor',
  'ductAcoustics', 'ductBounds', 'dyadicInterval', 'filters', 'impedance', 'impedanceCert', 'index', 'interval', 'operating', 'passiveRadiator', 'pressure', 'response', 'sampling',
  'sensitivity', 'sweep',
]
const allowedFiles = [
  'LICENSE', 'README.md', 'package.json',
  ...modules.flatMap((name) => [`dist/${name}.js`, `dist/${name}.d.ts`]),
].sort()

const output = process.argv[2] ? resolve(process.argv[2]) : undefined
const temp = mkdtempSync(join(tmpdir(), 'electroacoustics-pack-'))

function runNpm(args, cwd) {
  return execFileSync(process.execPath, [npmCli, ...args], { cwd, encoding: 'utf8' })
}

try {
  const [pack] = JSON.parse(
    runNpm(['pack', '--ignore-scripts', '--json', '--pack-destination', temp], root),
  )
  assert.deepEqual(pack.files.map(({ path }) => path).sort(), allowedFiles)

  const tarball = join(temp, basename(pack.filename))
  const consumer = join(temp, 'consumer')
  mkdirSync(consumer)
  writeFileSync(join(consumer, 'package.json'), '{"private":true}\n')
  runNpm(['install', '--offline', '--ignore-scripts', '--no-audit', '--no-fund', '--no-package-lock', tarball], consumer)

  writeFileSync(join(consumer, 'consumer.mts'), `
    import {
      analyzeBandOutputLimit, analyzeOutputLimit, boundDuctPathPeakVelocityRatio, boundDuctPathTuning,
      c, createCircuit, createDriverImpedance, div, ductPathTuning, ductVolumeForTuning, fitDriverImpedance,
      fitEnclosureImpedance, operatingSourceFromCircuit, sealedVolumeForQtc, solveDuctLengthForTuning,
      summarizeResponse, sweepCircuit, ventLengthForTuning, verifyBandOutputCertificate,
      verifyDriverImpedanceFitCertificate, verifyDuctPeakVelocityCertificate, verifyDuctTuningCertificate,
      verifyEnclosureImpedanceFitCertificate, type BandOutputLimitOptions, type CircuitInput, type CircuitPoint,
      type DriverImpedanceFit, type DuctPath, type EnclosureFitParameter,
    } from '${pack.name}'

    function check(condition: unknown, message: string): asserts condition {
      if (!condition) throw new Error(message)
    }

    function jsonRoundTrip<T>(value: T): T {
      return JSON.parse(JSON.stringify(value))
    }

    const input: CircuitInput = {
      driver: { fsHz: 25, vasM3: 0.08, qes: 0.45, qms: 8, reOhms: 6, leHenries: 0, sdM2: 0.05 },
      volumeM3: 0.07, voltageRms: 2.83,
      medium: { densityKgM3: 1.2041, soundSpeedMps: 343 },
      leakageQuality: Infinity, absorptionQuality: Infinity,
    }
    const { driver, medium } = input
    const { soundSpeedMps: speed, densityKgM3: density } = medium
    const resonance = driver.fsHz * Math.sqrt(1 + driver.vasM3 / input.volumeM3)
    const result: CircuitPoint = createCircuit(input)(resonance)
    check(Math.abs(result.impedanceOhms.im) < 1e-8, 'Expected real impedance at resonance')
    check(Number.isFinite(result.splDb), 'Expected finite SPL')
    const quotient = div(c(Number.MIN_VALUE, 1), c(0, 0.5))
    check(quotient.re === 2 && quotient.im === -2 * Number.MIN_VALUE, 'Incorrect subnormal complex quotient')
    const extremeSpl = createCircuit({ ...input, distanceM: 1e-305 })(resonance).splDb
    check(Math.abs(extremeSpl - result.splDb - 6100) < 1e-9, 'Incorrect SPL at extreme distance')

    // The same SI inputs passed by a cabinet-design adapter such as Subchecker.
    const qts = 1 / (1 / driver.qes + 1 / driver.qms)
    const box = sealedVolumeForQtc({ fsHz: driver.fsHz, vasM3: driver.vasM3, qts }, 0.707)
    check(Math.abs(box.qtc - 0.707) < 1e-10, 'Incorrect sealed alignment')
    const areaM2 = 0.012
    const port = { areaM2, effectiveLengthM: ventLengthForTuning(areaM2, input.volumeM3, 35, speed), quality: 7 }
    const vented = { ...input, port }
    const points = sweepCircuit(vented, { minHz: 14, maxHz: 120 }).points
    const summary = summarizeResponse(points, { reference: { kind: 'band-peak' } })
    check(summary.minimumImpedance.value > 0, 'Expected positive minimum impedance')
    const output = analyzeOutputLimit(operatingSourceFromCircuit(vented, points, {
      xmaxMeters: 0.01, ratedPowerWattsPerDriver: 150,
    }), { maxPortMach: 0.07, maxAmplifierVoltageRms: 50, maxAmplifierCurrentRms: 7 })
    check(output.points.length === points.length &&
      output.points.every((point) => Number.isFinite(point.maxSplDb)), 'Expected an SPL limit at every sweep point')
    const band = analyzeBandOutputLimit(vented, { minHz: 14, maxHz: 120, maxPortMach: 0.07 })
    check(band.status === 'resolved' && band.safeInputVoltageRms !== null && band.safeInputVoltageRms > 0 &&
      band.errorBoundDb !== null && band.errorBoundDb <= 0.1, 'Expected a certified lumped-port limit')

    function bandCertificate(label: string, circuit: CircuitInput, options: BandOutputLimitOptions) {
      const band = analyzeBandOutputLimit(circuit, options)
      check(band.status === 'resolved' && band.certificate, label + ' failed: ' + band.reason)
      const certificate = jsonRoundTrip(band.certificate)
      check(certificate.safeInputVoltageRms > 0 && certificate.errorBoundDb <= (options.toleranceDb ?? 0.1),
        label + ' exceeded the requested band error')
      check(verifyBandOutputCertificate(circuit, options, certificate), label + ' certificate rejected')
      check(!verifyBandOutputCertificate(circuit, options, { ...certificate, spans: certificate.spans.slice(1) }),
        label + ' accepted an incomplete band cover')
      return certificate
    }

    const eq: BandOutputLimitOptions = { minHz: 30, maxHz: 80, maxAmplifierVoltageRms: 20, filter: {
      digital: { sampleRateHz: 48000, stages: [
        { kind: 'peaking', frequencyHz: 51, q: 60, gainDb: 20 * Math.log10(1.36) },
      ] },
    } }
    const eqCertificate = bandCertificate('Peaking EQ', input, eq)
    check(eqCertificate.safeInputVoltageRms <= 20 / 1.36, 'Peaking EQ overstated the safe voltage')
    check(!verifyBandOutputCertificate(input, { ...eq, maxAmplifierVoltageRms: 19 }, eqCertificate),
      'Accepted a certificate for a different voltage limit')
    check(!verifyBandOutputCertificate(input, eq, { ...eqCertificate, safeInputVoltageRms: 15 }),
      'Accepted an unsafe EQ voltage')

    const straight: DuctPath = { count: 1, inletCorrectionMeters: 0, outletCorrectionMeters: 0,
      sections: [{ lengthMeters: 0.3, inletAreaSquareMeters: areaM2, outletAreaSquareMeters: areaM2, profile: 'straight' }] }
    const straightCertificate = bandCertificate('Straight duct', { ...input, port: { quality: Infinity, ductPath: straight } },
      { minHz: 250, maxHz: 310, maxPortMach: 0.004, xmaxMeters: 0.008 })
    const tapered: DuctPath = { count: 1, inletCorrectionMeters: 0.015, outletCorrectionMeters: 0.02,
      sections: [
        { lengthMeters: 0.12, inletAreaSquareMeters: areaM2, outletAreaSquareMeters: 0.0125, profile: 'conical' },
        { lengthMeters: 0.18, inletAreaSquareMeters: 0.0125, outletAreaSquareMeters: 0.013, profile: 'exponential' },
      ] }
    const taperedCertificate = bandCertificate('Corrected tapered duct', { ...input, port: { quality: 8, ductPath: tapered } },
      { minHz: 250, maxHz: 250.25, maxPortMach: 0.004 })

    const antinode: DuctPath = { count: 1, inletCorrectionMeters: 0.015, outletCorrectionMeters: 0.025,
      sections: [
        { lengthMeters: 0.6, inletAreaSquareMeters: 0.005, outletAreaSquareMeters: 0.005, profile: 'straight' },
        { lengthMeters: 0.3, inletAreaSquareMeters: 0.005, outletAreaSquareMeters: 0.04, profile: 'conical' },
      ] }
    check(ductVolumeForTuning(antinode, 35, speed) > 0, 'Expected positive cavity volume for tuning')
    const tuningOptions = { relativeTolerance: 0.01 }
    const tuning = boundDuctPathTuning(antinode, input.volumeM3, speed, tuningOptions)
    check(tuning.status === 'resolved', 'Tapered duct tuning failed')
    const tuningCertificate = jsonRoundTrip(tuning.certificate)
    check(tuning.lower > 0 && tuning.upper > tuning.lower &&
      (tuning.upper - tuning.lower) / tuning.lower <= tuningOptions.relativeTolerance, 'Incorrect tuning bracket width')
    check(verifyDuctTuningCertificate(antinode, input.volumeM3, speed, tuningCertificate, tuningOptions),
      'Tuning certificate rejected')
    check(!verifyDuctTuningCertificate(antinode, input.volumeM3, speed,
      { ...tuningCertificate, earlierSpans: [] }, tuningOptions), 'Accepted tuning without earlier-root exclusion')

    const velocityHz = speed / 1.2
    const velocityOptions = { relativeTolerance: 0.08 }
    const velocity = boundDuctPathPeakVelocityRatio(antinode, velocityHz, speed, density, velocityOptions)
    check(velocity.status === 'resolved', 'Tapered duct peak velocity failed')
    const velocityCertificate = jsonRoundTrip(velocity.certificate)
    const { sectionIndex, fraction } = velocityCertificate.witness
    check(sectionIndex === 0 && fraction > 0 && fraction < 1, 'Expected an interior antinode in the first section')
    check(velocity.lower > 1 / antinode.sections[0]!.inletAreaSquareMeters &&
      (velocity.upper - velocity.lower) / velocity.lower <= velocityOptions.relativeTolerance, 'Incorrect peak velocity bound')
    check(verifyDuctPeakVelocityCertificate(antinode, velocityHz, speed, density, velocityCertificate, velocityOptions),
      'Peak velocity certificate rejected')
    check(!verifyDuctPeakVelocityCertificate(antinode, velocityHz, speed, density,
      { ...velocityCertificate, sectionSpans: [] }, velocityOptions), 'Accepted peak velocity without a position cover')

    function pathForLength(lengthMeters: number): DuctPath {
      return { ...straight, inletCorrectionMeters: 0.02, outletCorrectionMeters: 0.02,
        sections: [{ ...straight.sections[0]!, lengthMeters }] }
    }
    const volumeForLength = (length: number) => input.volumeM3 - areaM2 * length
    const targetHz = ductPathTuning(pathForLength(0.4), volumeForLength(0.4), speed)
    const length = solveDuctLengthForTuning({
      minLengthM: 0.1, maxLengthM: 0.9, targetHz, soundSpeedMps: speed, pathForLength, volumeForLength,
    })
    const { minLengthM, maxLengthM } = length.bracket
    check(length.status === 'root' && length.iterations === 30, 'Unexpected length solver stop')
    check(minLengthM <= 0.4 && 0.4 <= maxLengthM && maxLengthM - minLengthM <= 1e-9 &&
      ductPathTuning(pathForLength(minLengthM), volumeForLength(minLengthM), speed) >= targetHz &&
      ductPathTuning(pathForLength(maxLengthM), volumeForLength(maxLengthM), speed) <= targetHz, 'Incorrect length bracket')

    const fitDriver = { ...driver, leHenries: 0.0005 }
    const condition = { kind: 'added-mass', massKg: 0.08 } as const
    const frequencies = [15, 25, 45, 100]
    function sweep(at: (frequency: number) => { re: number; im: number }, atHz = frequencies) {
      return atHz.map((frequency) => ({ frequency, impedanceOhms: at(frequency) }))
    }
    const driverRequest: DriverImpedanceFit = {
      initial: { ...fitDriver, fsHz: 26, vasM3: 0.085 }, medium, tolerance: 1e-8,
      freeAir: sweep(createDriverImpedance(fitDriver, medium)),
      perturbed: { condition, samples: sweep(createDriverImpedance(fitDriver, medium, condition)) },
    }
    const driverFit = fitDriverImpedance(driverRequest)
    check(driverFit.status === 'residual-target' && driverFit.certificate?.sensitivityRank === 6,
      'Expected a full-rank driver fit at the residual target')
    const driverCertificate = jsonRoundTrip(driverFit.certificate)
    check(verifyDriverImpedanceFitCertificate(driverRequest, driverCertificate), 'Driver fit certificate rejected')
    check(!verifyDriverImpedanceFitCertificate(driverRequest, { ...driverCertificate, sensitivityRank: 0 }),
      'Accepted a forged driver fit rank')

    const enclosure: CircuitInput = { ...input, driver: fitDriver, leakageQuality: 7 }
    const enclosureAt = (circuit: CircuitInput) => {
      const at = createCircuit(circuit)
      return (frequency: number) => at(frequency).impedanceOhms
    }
    const enclosureSamples = sweep(enclosureAt({ ...enclosure, leakageQuality: 15 }))
    const enclosureBounds: { parameter: EnclosureFitParameter; min: number; max: number }[] = [
      { parameter: 'leakageQuality', min: 2, max: 8 },
    ]
    const enclosureFit = fitEnclosureImpedance(enclosure, enclosureSamples, enclosureBounds)
    check(enclosureFit.status === 'bound-constrained' && enclosureFit.certificate?.sensitivityRank === 1 &&
      enclosureFit.input.leakageQuality === 8, 'Expected a full-rank enclosure fit on the upper bound')
    const enclosureCertificate = jsonRoundTrip(enclosureFit.certificate)
    check(verifyEnclosureImpedanceFitCertificate(enclosure, enclosureSamples, enclosureBounds, enclosureCertificate),
      'Enclosure fit certificate rejected')
    check(!verifyEnclosureImpedanceFitCertificate(enclosure, enclosureSamples, enclosureBounds,
      { ...enclosureCertificate, values: [9] }), 'Accepted an enclosure fit outside its parameter bounds')

    const weakSamples = sweep(enclosureAt(enclosure), [1e7, 2e7])
    const weakBounds = [{ parameter: 'volumeM3' as const, min: 0.04, max: 0.09 }]
    const weakFit = fitEnclosureImpedance(enclosure, weakSamples, weakBounds)
    check(weakFit.status === 'poorly-identified' && weakFit.certificate?.sensitivityRank === 0,
      'Expected a poorly identified enclosure fit')
    const weakCertificate = jsonRoundTrip(weakFit.certificate)
    check(verifyEnclosureImpedanceFitCertificate(enclosure, weakSamples, weakBounds, weakCertificate),
      'Poorly identified fit certificate rejected')
    check(!verifyEnclosureImpedanceFitCertificate(enclosure, weakSamples, weakBounds,
      { ...weakCertificate, weakDirection: [0] }), 'Accepted a zero weak direction')

    console.log(JSON.stringify({
      'band-eq': eqCertificate, 'band-straight-duct': straightCertificate, 'band-tapered-duct': taperedCertificate,
      'duct-tuning': tuningCertificate, 'duct-peak-velocity': velocityCertificate, 'fit-driver': driverCertificate,
      'fit-enclosure': enclosureCertificate, 'fit-poorly-identified': weakCertificate,
    }))
  `)
  execFileSync(process.execPath, [
    tsc, '--strict', '--module', 'NodeNext', '--target', 'ES2022', '--ignoreConfig', 'consumer.mts',
  ], { cwd: consumer, stdio: 'inherit' })
  const certificates = JSON.parse(execFileSync(process.execPath, ['consumer.mjs'], { cwd: consumer, encoding: 'utf8' }))
  const writeCertificate = (path, name) => writeFileSync(path, JSON.stringify(certificates[name]) + '\n')
  const replayDir = process.env.ELECTROACOUSTICS_REPLAY_DIR
  if (replayDir) {
    mkdirSync(replayDir, { recursive: true })
    for (const name of Object.keys(certificates)) writeCertificate(join(replayDir, name + '.json'), name)
  }
  if (process.env.ELECTROACOUSTICS_REPLAY_CERTIFICATE)
    writeCertificate(process.env.ELECTROACOUSTICS_REPLAY_CERTIFICATE, 'band-eq')
  if (process.env.ELECTROACOUSTICS_DUCT_REPLAY_CERTIFICATE)
    writeCertificate(process.env.ELECTROACOUSTICS_DUCT_REPLAY_CERTIFICATE, 'band-straight-duct')

  if (output) {
    mkdirSync(output, { recursive: true })
    copyFileSync(tarball, join(output, basename(pack.filename)))
  }
  console.log(`Verified ${pack.name}@${pack.version} (${allowedFiles.length} files, ESM and types).`)
} finally {
  rmSync(temp, { recursive: true, force: true })
}
