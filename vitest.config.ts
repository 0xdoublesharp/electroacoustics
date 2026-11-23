import { defineConfig } from 'vitest/config'

function fuzzInteger(name: string, fallback: number, min: number, max: number) {
  const raw = process.env[name] ?? String(fallback)
  const value = Number(raw)
  if (!/^-?\d+$/.test(raw) || value < min || value > max)
    throw new RangeError(`${name} must be an integer from ${min} to ${max}`)
  return value
}

const path = process.env.FUZZ_PATH

export default defineConfig({
  test: {
    provide: {
      fuzz: {
        numRuns: fuzzInteger('FUZZ_RUNS', 100, 1, Number.MAX_SAFE_INTEGER),
        seed: fuzzInteger('FUZZ_SEED', 20261123, -(2 ** 31), 2 ** 31 - 1),
        ...(path === undefined ? {} : { path, endOnFailure: true }),
      },
    },
    coverage: {
      provider: 'v8',
      include: ['src/**/*.ts'],
      exclude: ['src/**/*.test.ts', 'src/testFixtures.ts'],
      reporter: ['text', 'text-summary', 'lcovonly'],
      thresholds: {
        branches: 100,
        functions: 100,
        lines: 100,
        statements: 100,
      },
    },
  },
})
