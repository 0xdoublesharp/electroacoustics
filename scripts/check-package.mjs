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
  'alignment', 'circuit', 'complex', 'driverMotor', 'ductAcoustics', 'filters',
  'impedance', 'index', 'operating', 'passiveRadiator', 'response', 'sampling',
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

  const inputLiteral = `{
    driver: { fsHz: 25, vasM3: 0.08, qes: 0.45, qms: 8, reOhms: 6, leHenries: 0, sdM2: 0.05 },
    volumeM3: 0.07, voltageRms: 2.83,
    medium: { densityKgM3: 1.2041, soundSpeedMps: 343 },
    leakageQuality: Infinity, absorptionQuality: Infinity,
  }`
  writeFileSync(join(consumer, 'consumer.mts'), `
    import { analyzeOutputLimit, createCircuit, operatingSourceFromCircuit, summarizeResponse,
      type CircuitInput, type CircuitPoint } from '${pack.name}'
    const input: CircuitInput = ${inputLiteral}
    export const result: CircuitPoint = createCircuit(input)(40)
    export const output = analyzeOutputLimit(operatingSourceFromCircuit(input, [result], {
      xmaxMeters: 0.01, ratedPowerWattsPerDriver: 100,
    }), { maxAmplifierCurrentRms: 2 })
    export const summary = summarizeResponse([result], { reference: { kind: 'band-peak' } })
  `)
  execFileSync(process.execPath, [
    tsc, '--strict', '--module', 'NodeNext', '--target', 'ES2022',
    '--noEmit', '--ignoreConfig', 'consumer.mts',
  ], { cwd: consumer, stdio: 'inherit' })
  execFileSync(process.execPath, ['--input-type=module', '-e', `
    import assert from 'node:assert/strict'
    import { analyzeOutputLimit, createCircuit, ductVolumeForTuning, operatingSourceFromCircuit,
      sealedVolumeForQtc, summarizeResponse, sweepCircuit, ventLengthForTuning } from '${pack.name}'
    const input = ${inputLiteral}
    const resonance = input.driver.fsHz * Math.sqrt(1 + input.driver.vasM3 / input.volumeM3)
    const result = createCircuit(input)(resonance)
    assert.ok(Math.abs(result.impedanceOhms.im) < 1e-8)
    assert.ok(Number.isFinite(result.splDb))
    // The same SI inputs passed by a cabinet-design adapter such as Subchecker.
    const { driver, medium } = input
    const qts = 1 / (1 / driver.qes + 1 / driver.qms)
    const box = sealedVolumeForQtc({ fsHz: driver.fsHz, vasM3: driver.vasM3, qts }, 0.707)
    assert.ok(Math.abs(box.qtc - 0.707) < 1e-10)
    const areaM2 = 0.012
    const port = { areaM2, effectiveLengthM: ventLengthForTuning(areaM2, input.volumeM3, 35, medium.soundSpeedMps), quality: 7 }
    const vented = { ...input, port }
    const points = sweepCircuit(vented, { minHz: 14, maxHz: 120 }).points
    const summary = summarizeResponse(points, { reference: { kind: 'band-peak' } })
    assert.ok(summary.minimumImpedance.value > 0)
    const output = analyzeOutputLimit(operatingSourceFromCircuit(vented, points, {
      xmaxMeters: 0.01, ratedPowerWattsPerDriver: 150,
    }), { maxPortMach: 0.07, maxAmplifierVoltageRms: 50, maxAmplifierCurrentRms: 7 })
    assert.equal(output.points.length, points.length)
    assert.ok(output.points.every((point) => Number.isFinite(point.maxSplDb)))
    const duct = { count: 1, inletCorrectionMeters: 0.02, outletCorrectionMeters: 0.02,
      sections: [{ lengthMeters: 0.3, inletAreaSquareMeters: areaM2, outletAreaSquareMeters: areaM2, profile: 'straight' }] }
    assert.ok(ductVolumeForTuning(duct, 35, medium.soundSpeedMps) > 0)
  `], { cwd: consumer, stdio: 'inherit' })

  if (output) {
    mkdirSync(output, { recursive: true })
    copyFileSync(tarball, join(output, basename(pack.filename)))
  }
  console.log(`Verified ${pack.name}@${pack.version} (${allowedFiles.length} files, ESM and types).`)
} finally {
  rmSync(temp, { recursive: true, force: true })
}
