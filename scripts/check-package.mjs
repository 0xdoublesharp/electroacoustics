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
  'circuit', 'complex', 'ductAcoustics', 'filters', 'index',
  'operating', 'sampling', 'sensitivity', 'sweep',
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
    import { createCircuit, type CircuitInput, type CircuitPoint } from '${pack.name}'
    const input: CircuitInput = ${inputLiteral}
    export const result: CircuitPoint = createCircuit(input)(40)
  `)
  execFileSync(process.execPath, [
    tsc, '--strict', '--module', 'NodeNext', '--target', 'ES2022',
    '--noEmit', '--ignoreConfig', 'consumer.mts',
  ], { cwd: consumer, stdio: 'inherit' })
  execFileSync(process.execPath, ['--input-type=module', '-e', `
    import assert from 'node:assert/strict'
    import { createCircuit } from '${pack.name}'
    const input = ${inputLiteral}
    const resonance = input.driver.fsHz * Math.sqrt(1 + input.driver.vasM3 / input.volumeM3)
    const result = createCircuit(input)(resonance)
    assert.ok(Math.abs(result.impedanceOhms.im) < 1e-8)
    assert.ok(Number.isFinite(result.splDb))
  `], { cwd: consumer, stdio: 'inherit' })

  if (output) {
    mkdirSync(output, { recursive: true })
    copyFileSync(tarball, join(output, basename(pack.filename)))
  }
  console.log(`Verified ${pack.name}@${pack.version} (${allowedFiles.length} files, ESM and types).`)
} finally {
  rmSync(temp, { recursive: true, force: true })
}
