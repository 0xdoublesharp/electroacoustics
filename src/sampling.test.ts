import { describe, expect, it } from 'vitest'
import { sampleAdaptive } from './sampling'

describe('adaptive frequency sampling', () => {
  it('samples a supplied resonance landmark accurately against a dense reference', () => {
    const center = 137
    const width = 2.5
    const response = (frequency: number) =>
      1 / (1 + ((frequency - center) / width) ** 2)
    const result = sampleAdaptive(response, (value) => [value], {
      minHz: 20,
      maxHz: 2_000,
      initialPoints: 12,
      maxPoints: 300,
      relativeTolerance: 0.002,
      landmarksHz: [center],
    })
    const densePeak = Math.max(
      ...Array.from({ length: 20_001 }, (_, index) =>
        response(20 + (index / 20_000) * 1_980),
      ),
    )
    const sampledPeak = Math.max(...result.samples.map(({ value }) => value))
    expect(sampledPeak).toBe(1)
    expect(sampledPeak - densePeak).toBeLessThan(0.0001)
    expect(result.samples.some(({ frequency }) => frequency === center)).toBe(
      true,
    )
  })

  it('recognizes a log-linear metric after one midpoint probe per interval', () => {
    const result = sampleAdaptive(
      (frequency) => 3 + 2 * Math.log(frequency),
      (value) => [value],
      { minHz: 1, maxHz: 1_000, initialPoints: 5, maxPoints: 9 },
    )
    expect(result.diagnostics).toMatchObject({
      converged: true,
      evaluations: 9,
      unresolvedIntervals: 0,
    })
    expect(result.diagnostics.maxEstimatedError).toBeLessThan(1e-12)
  })

  it('computes interpolation error without overflowing finite metrics', () => {
    const result = sampleAdaptive(
      () => Number.MAX_VALUE,
      (value) => [value],
      {
        minHz: 1,
        maxHz: 100,
        initialPoints: 2,
        maxPoints: 3,
      },
    )
    expect(result.diagnostics).toMatchObject({
      converged: true,
      maxEstimatedError: 0,
    })
  })

  it('reports the largest accepted interval error after convergence', () => {
    const result = sampleAdaptive(
      (frequency) => 10 + Math.log(frequency) ** 2,
      (value) => [value],
      {
        minHz: 1,
        maxHz: 100,
        initialPoints: 3,
        maxPoints: 200,
        relativeTolerance: 0.01,
      },
    )
    expect(result.diagnostics.converged).toBe(true)
    expect(result.diagnostics.maxEstimatedError).toBeLessThanOrEqual(0.01)
  })

  it('returns ordered unique samples with exact endpoints and deduplicated landmarks', () => {
    const landmarks = [1, 10, 10, 100, 0.5, 101]
    const result = sampleAdaptive(
      (frequency) => frequency,
      (value) => [value],
      {
        minHz: 1,
        maxHz: 100,
        initialPoints: 3,
        maxPoints: 20,
        landmarksHz: landmarks,
      },
    )
    landmarks[1] = 33
    const frequencies = result.samples.map(({ frequency }) => frequency)
    expect(frequencies[0]).toBe(1)
    expect(frequencies.at(-1)).toBe(100)
    expect(frequencies).toContain(10)
    expect(frequencies).not.toContain(0.5)
    expect(frequencies).not.toContain(101)
    expect(frequencies).not.toContain(33)
    expect(frequencies).toEqual([...new Set(frequencies)].sort((a, b) => a - b))
  })

  it('coalesces near-coincident bounds and landmarks while permitting refinement', () => {
    const result = sampleAdaptive(Math.log, (value) => [value], {
      minHz: 1,
      maxHz: 10,
      initialPoints: 2,
      maxPoints: 8,
      landmarksHz: [
        1 + Number.EPSILON,
        10 - 10 * Number.EPSILON,
        3,
        3 + 3 * Number.EPSILON,
      ],
    })
    const frequencies = result.samples.map((point) => point.frequency)
    expect(frequencies[0]).toBe(1)
    expect(frequencies.at(-1)).toBe(10)
    expect(
      frequencies.filter((frequency) => Math.abs(frequency - 3) < 1e-12),
    ).toEqual([3])
    expect(result.diagnostics.converged).toBe(true)
    expect(result.diagnostics.evaluations).toBe(5)
  })

  it('finishes intervals with no representable interior frequency', () => {
    const result = sampleAdaptive(
      () => 1,
      (value) => [value],
      {
        minHz: 1,
        maxHz: 1 + Number.EPSILON,
        initialPoints: 2,
        maxPoints: 3,
      },
    )
    expect(result.samples.map((point) => point.frequency)).toEqual([
      1,
      1 + Number.EPSILON,
    ])
    expect(result.diagnostics.converged).toBe(true)
    expect(result.diagnostics.evaluations).toBe(2)
  })

  it('keeps midpoint probes inside narrow bounds at large frequencies', () => {
    const minHz = 1e20
    const maxHz = minHz * (1 + 4 * Number.EPSILON)
    const visited: number[] = []
    const result = sampleAdaptive(
      (frequency) => {
        visited.push(frequency)
        return 1
      },
      (value) => [value],
      { minHz, maxHz, initialPoints: 2, maxPoints: 3 },
    )
    expect(visited).toHaveLength(3)
    expect(visited[2]).toBeGreaterThan(minHz)
    expect(visited[2]).toBeLessThan(maxHz)
    expect(result.samples[0]!.frequency).toBe(minHz)
    expect(result.samples.at(-1)!.frequency).toBe(maxHz)
  })

  it.each([1, 1e100, 1e-100])(
    'rejects an initial grid between adjacent frequencies near %s before evaluation',
    (minHz) => {
      const frequencyBits = new DataView(new ArrayBuffer(8))
      frequencyBits.setFloat64(0, minHz)
      frequencyBits.setBigUint64(0, frequencyBits.getBigUint64(0) + 1n)
      const maxHz = frequencyBits.getFloat64(0)
      let evaluations = 0
      expect(() =>
        sampleAdaptive(
          (frequency) => {
            evaluations++
            return frequency
          },
          (value) => [value],
          { minHz, maxHz, initialPoints: 3, maxPoints: 4 },
        ),
      ).toThrow(/supported numerical resolution/)
      expect(evaluations).toBe(0)
    },
  )

  it('reports unresolved intervals when the evaluation budget cannot probe them', () => {
    let evaluations = 0
    const result = sampleAdaptive(
      (frequency) => {
        evaluations += 1
        return frequency
      },
      (value) => [value],
      { minHz: 10, maxHz: 1_000, initialPoints: 4, maxPoints: 4 },
    )
    expect(result.diagnostics).toMatchObject({
      converged: false,
      evaluations: 4,
      maxPoints: 4,
      unresolvedIntervals: 3,
    })
    expect(result.diagnostics.maxEstimatedError).toBe(Infinity)
    expect(evaluations).toBe(4)
    expect(result.samples).toHaveLength(4)
  })

  it('never evaluates beyond maxPoints while retaining every evaluated point', () => {
    const visited: number[] = []
    const result = sampleAdaptive(
      (frequency) => {
        visited.push(frequency)
        return Math.sin(100 * Math.log(frequency))
      },
      (value) => [value],
      {
        minHz: 1,
        maxHz: 1_000,
        initialPoints: 6,
        maxPoints: 11,
        relativeTolerance: 1e-8,
      },
    )
    expect(visited).toHaveLength(11)
    expect(result.diagnostics.evaluations).toBe(11)
    expect(
      result.samples.map(({ frequency }) => frequency).sort((a, b) => a - b),
    ).toEqual([...visited].sort((a, b) => a - b))
    expect(result.diagnostics.converged).toBe(false)
    expect(result.diagnostics.unresolvedIntervals).toBeGreaterThan(0)
  })

  it('rejects invalid options before evaluation', () => {
    const invalid = [
      { minHz: 0, maxHz: 10 },
      { minHz: 10, maxHz: 10 },
      { minHz: 1, maxHz: Infinity },
      { minHz: 1, maxHz: 10, initialPoints: 1 },
      { minHz: 1, maxHz: 10, initialPoints: 4, maxPoints: 3 },
      { minHz: 1, maxHz: 10, maxPoints: 8_193 },
      { minHz: 1, maxHz: 10, relativeTolerance: 0 },
      { minHz: 1, maxHz: 10, relativeTolerance: 1.1 },
      { minHz: 1, maxHz: 10, landmarksHz: [NaN] },
      { minHz: 1, maxHz: 10, landmarksHz: [Infinity] },
    ]
    for (const options of invalid) {
      let called = false
      expect(() =>
        sampleAdaptive(
          () => {
            called = true
            return 1
          },
          (value) => [value],
          options,
        ),
      ).toThrow(RangeError)
      expect(called).toBe(false)
    }
  })

  it.each([
    { minHz: 1, maxHz: 100, initialPoints: 3, maxPoints: 4, landmarksHz: [7] },
    {
      minHz: 1,
      maxHz: 1000,
      initialPoints: 4,
      maxPoints: 4,
      landmarksHz: [10],
    },
    { minHz: 1, maxHz: 100, maxPoints: 48 },
  ])(
    'reserves boundary capacity without losing landmarks for %j',
    (options) => {
      const result = sampleAdaptive(Math.log, (value) => [value], {
        ...options,
        reservedLandmarksHz: [13],
      })
      const frequencies = result.samples.map((point) => point.frequency)
      expect(frequencies).toHaveLength(options.maxPoints)
      expect(frequencies[0]).toBe(options.minHz)
      expect(frequencies.at(-1)).toBe(options.maxHz)
      expect(frequencies).toContain(13)
      for (const landmark of options.landmarksHz ?? [])
        expect(frequencies).toContain(landmark)
      expect(result.diagnostics).toMatchObject({
        evaluations: options.maxPoints,
        maxPoints: options.maxPoints,
        converged: false,
      })
    },
  )

  it('keeps the grid when reserved landmarks are duplicates or out of range', () => {
    const options = {
      minHz: 1,
      maxHz: 100,
      initialPoints: 3,
      maxPoints: 4,
      landmarksHz: [7],
    }
    const baseline = sampleAdaptive(Math.log, (value) => [value], options)
    expect(
      sampleAdaptive(Math.log, (value) => [value], {
        ...options,
        reservedLandmarksHz: [0.5, 101, 1, 7, 7, 100],
      }),
    ).toEqual(baseline)
  })

  it.each([
    { initialPoints: 4, maxPoints: 3 },
    { initialPoints: 3, maxPoints: 3, landmarksHz: [7] },
    { initialPoints: 2, maxPoints: 2 },
    { maxPoints: 47 },
    { reservedLandmarksHz: [NaN] },
  ])(
    'rejects invalid or impossible reserved budgets %j before evaluation',
    (options) => {
      let called = false
      expect(() =>
        sampleAdaptive(
          () => {
            called = true
            return 1
          },
          (value) => [value],
          { minHz: 1, maxHz: 100, reservedLandmarksHz: [13], ...options },
        ),
      ).toThrow(RangeError)
      expect(called).toBe(false)
    },
  )

  it('rejects empty, changing-length, and nonfinite metrics', () => {
    expect(() =>
      sampleAdaptive(
        (frequency) => frequency,
        () => [],
        {
          minHz: 1,
          maxHz: 10,
          initialPoints: 2,
          maxPoints: 3,
        },
      ),
    ).toThrow(/nonempty/)
    expect(() =>
      sampleAdaptive(
        (frequency) => frequency,
        (value) => (value === 1 ? [value] : [value, value]),
        { minHz: 1, maxHz: 10, initialPoints: 2, maxPoints: 3 },
      ),
    ).toThrow(/constant length/)
    for (const bad of [NaN, Infinity, -Infinity])
      expect(() =>
        sampleAdaptive(
          () => bad,
          (value) => [value],
          {
            minHz: 1,
            maxHz: 10,
            initialPoints: 2,
            maxPoints: 3,
          },
        ),
      ).toThrow(/finite/)
  })
})
