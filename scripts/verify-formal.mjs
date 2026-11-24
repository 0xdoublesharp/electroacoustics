import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs'
import { homedir } from 'node:os'
import { basename, delimiter, join, resolve } from 'node:path'
import { performance } from 'node:perf_hooks'
import { fileURLToPath } from 'node:url'

const root = fileURLToPath(new URL('../', import.meta.url))
const scratchVolume = '/Volumes/Scratch'
const scratchRoot = process.env.ELECTROACOUSTICS_SCRATCH_DIR ||
  (existsSync(scratchVolume) ? join(scratchVolume, 'electroacoustics') : process.env.TMPDIR)
assert.ok(scratchRoot, 'Mount /Volumes/Scratch or set ELECTROACOUSTICS_SCRATCH_DIR or TMPDIR.')
const scratch = resolve(scratchRoot)
const npmCli = process.env.npm_execpath
assert.ok(npmCli, 'Run this through npm run verify:formal.')

const band = { script: 'band', rejection: 'The certificate does not match a supported band result' }
const duct = { script: 'duct', rejection: 'The certificate does not match its duct request' }
const fit = { script: 'fit', rejection: 'The certificate does not match its impedance fit request' }
const replays = [
  { name: 'band-eq', ...band, tamper: () => ({ spans: [] }) },
  { name: 'band-straight-duct', ...band, tamper: () => ({ spans: [] }) },
  { name: 'band-tapered-duct', ...band, tamper: () => ({ spans: [] }) },
  { name: 'duct-tuning', ...duct, tamper: () => ({ earlierSpans: [] }) },
  { name: 'duct-peak-velocity', ...duct, tamper: () => ({ sectionSpans: [] }) },
  { name: 'fit-driver', ...fit, tamper: () => ({ sensitivityRank: 0 }) },
  { name: 'fit-enclosure', ...fit, tamper: ({ values }) => ({ values: [0, ...values.slice(1)] }) },
  { name: 'fit-poorly-identified', ...fit, tamper: ({ weakDirection }) => ({ weakDirection: weakDirection.map(() => 0) }) },
]
const allowedAxioms = new Set(['propext', 'Classical.choice', 'Quot.sound'])

function assertSucceeded(command, args, result) {
  if (result.error) throw result.error
  if (result.status !== 0) {
    const output = [result.stdout, result.stderr].filter(Boolean).join('\n').trim()
    throw new Error(`${command} ${args.join(' ')} failed (${result.signal ?? result.status})${output ? '\n' + output : ''}`)
  }
  return result.stdout
}

function replayAxioms(output, name) {
  const reports = [...output.matchAll(/^'replayVerified' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\.?\r?$/gm)]
  assert.equal(reports.length, 1, `${name} must report the axioms of replayVerified\n${output}`)
  const list = reports[0][1]?.trim()
  const axioms = list ? list.split(',').map((axiom) => axiom.trim()) : []
  for (const axiom of axioms)
    assert.ok(allowedAxioms.has(axiom), `${name} depends on unexpected axiom ${axiom}`)
  return axioms
}

let build
let temp
try {
  const buildRoot = join(scratch, 'build')
  const tempRoot = join(scratch, 'tmp')
  mkdirSync(buildRoot, { recursive: true })
  mkdirSync(tempRoot, { recursive: true })
  build = mkdtempSync(join(buildRoot, 'formal-'))
  temp = mkdtempSync(join(tempRoot, 'formal-'))

  const npmProject = join(build, 'npm')
  const leanProject = join(build, 'lean')
  const replayDir = join(temp, 'certificates')
  const jobs = process.env.COMPUTE_JOBS
  const env = {
    ...process.env,
    PATH: [join(homedir(), '.elan', 'bin'), process.env.PATH].filter(Boolean).join(delimiter),
    TMPDIR: temp,
    MATHLIB_CACHE_DIR: process.env.MATHLIB_CACHE_DIR
      ? resolve(process.env.MATHLIB_CACHE_DIR)
      : join(scratch, 'mathlib-cache'),
    npm_config_cache: join(temp, 'npm-cache'),
    npm_config_update_notifier: 'false',
    ELECTROACOUSTICS_REPLAY_DIR: replayDir,
    ELECTROACOUSTICS_REPLAY_CERTIFICATE: '',
    ELECTROACOUSTICS_DUCT_REPLAY_CERTIFICATE: '',
    ...(jobs ? { LEAN_NUM_THREADS: jobs, VITEST_MAX_WORKERS: jobs } : {}),
  }
  const run = (command, args, cwd, capture = false) =>
    assertSucceeded(command, args, spawnSync(command, args, {
      cwd, env, encoding: 'utf8', stdio: capture ? 'pipe' : 'inherit',
    }))

  // Build and pack a scratch copy so npm writes dist and coverage there.
  mkdirSync(npmProject)
  for (const path of [
    'LICENSE', 'README.md', 'package.json', 'package-lock.json', 'scripts', 'src',
    'tsconfig.json', 'tsconfig.build.json', 'vitest.config.ts',
  ])
    cpSync(join(root, path), join(npmProject, path), { recursive: true })
  cpSync(realpathSync(join(root, 'node_modules')), join(npmProject, 'node_modules'), {
    recursive: true, verbatimSymlinks: true,
  })
  run(process.execPath, [npmCli, 'run', 'check'], npmProject)

  cpSync(join(root, 'verification', 'lean'), leanProject, {
    recursive: true, filter: (path) => basename(path) !== '.lake',
  })
  run('lake', ['exe', 'cache', 'get'], leanProject)
  run('lake', ['build'], leanProject)

  const summary = []
  for (const replay of replays) {
    const { name, script, rejection, tamper } = replay
    const certificatePath = join(replayDir, name + '.json')
    const scriptPath = join('scripts', `replay-${script}-certificate.mjs`)
    const replayPath = join(temp, name + '.lean')
    const start = performance.now()
    console.log(`Checking ${name} with the Lean kernel`)
    writeFileSync(replayPath, run(process.execPath, [scriptPath, certificatePath, '--kernel'], npmProject, true))
    const output = run('lake', ['env', 'lean', '-DwarningAsError=true', replayPath], leanProject, true)
    const axioms = replayAxioms(output, name)
    const seconds = ((performance.now() - start) / 1000).toFixed(2)

    const certificate = JSON.parse(readFileSync(certificatePath, 'utf8'))
    const tamperedPath = join(temp, name + '-tampered.json')
    writeFileSync(tamperedPath, JSON.stringify({ ...certificate, ...tamper(certificate) }))
    const rejected = spawnSync(process.execPath, [scriptPath, tamperedPath, '--kernel'], {
      cwd: npmProject, env, encoding: 'utf8',
    })
    if (rejected.error) throw rejected.error
    assert.ok(rejected.status === 1 && rejected.stdout === '' && rejected.stderr.includes('Error: ' + rejection),
      `${name} did not reject tampering as expected\n${rejected.stderr}`)

    summary.push({
      Certificate: name + '.json', Seconds: seconds, Axioms: axioms.join(', ') || 'none', Tampered: 'rejected',
    })
  }
  console.table(summary)
} finally {
  try {
    if (temp) rmSync(temp, { recursive: true, force: true })
  } finally {
    if (build) rmSync(build, { recursive: true, force: true })
  }
}
