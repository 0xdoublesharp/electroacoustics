export interface SamplingOptions {
  minHz: number
  maxHz: number
  initialPoints?: number
  maxPoints?: number
  relativeTolerance?: number
  landmarksHz?: readonly number[]
  /** Required boundaries that may reduce regular seeds to fit maxPoints.
   * The original grid and landmarks must still fit before reserving them.
   */
  reservedLandmarksHz?: readonly number[]
}

interface Evaluated<T> {
  frequency: number
  value: T
  metrics: readonly number[]
}

interface Interval<T> {
  left: Evaluated<T>
  right: Evaluated<T>
}

export function sampleAdaptive<T>(
  evaluate: (frequency: number) => T,
  metrics: (value: T) => readonly number[],
  source: SamplingOptions,
): {
  samples: { frequency: number; value: T }[]
  diagnostics: {
    converged: boolean
    evaluations: number
    maxPoints: number
    relativeTolerance: number
    unresolvedIntervals: number
    maxEstimatedError: number
  }
} {
  const options = {
    ...source,
    landmarksHz: [...(source.landmarksHz ?? [])],
  }
  const reservedLandmarks = [...(source.reservedLandmarksHz ?? [])]
  const landmarks = [...options.landmarksHz, ...reservedLandmarks]
  const initialPoints = options.initialPoints ?? 48
  const maxPoints = options.maxPoints ?? 768
  const relativeTolerance = options.relativeTolerance ?? 0.005
  validateOptions(
    options.minHz,
    options.maxHz,
    initialPoints,
    maxPoints,
    relativeTolerance,
    landmarks,
  )

  let frequencies = initialFrequencies(
    options.minHz,
    options.maxHz,
    initialPoints,
    options.landmarksHz,
  )
  if (frequencies.length > maxPoints)
    throw new RangeError('Initial grid and landmarks exceed maxPoints')

  if (reservedLandmarks.length > 0) {
    // Validate the caller's original grid above before making room for
    // required boundaries. Duplicate and out-of-range seeds need no space.
    for (let count = initialPoints; count >= 2; count -= 1) {
      frequencies = initialFrequencies(
        options.minHz,
        options.maxHz,
        count,
        landmarks,
      )
      if (frequencies.length <= maxPoints) break
    }
    if (frequencies.length > maxPoints)
      throw new RangeError('Initial grid and landmarks exceed maxPoints')
  }

  let metricCount: number | undefined
  const evaluated = new Map<number, Evaluated<T>>()
  const evaluateAt = (frequency: number): Evaluated<T> => {
    const value = evaluate(frequency)
    const measured = [...metrics(value)]
    if (measured.length === 0)
      throw new RangeError('Sampling metrics must be nonempty')
    if (metricCount !== undefined && measured.length !== metricCount)
      throw new RangeError('Sampling metrics must have constant length')
    if (!measured.every(Number.isFinite))
      throw new RangeError('Sampling metrics must be finite')
    metricCount = measured.length
    const point = { frequency, value, metrics: measured }
    evaluated.set(frequency, point)
    return point
  }

  const initial = frequencies.map(evaluateAt)
  const pending: Interval<T>[] = []
  for (let index = 1; index < initial.length; index += 1)
    pending.push({ left: initial[index - 1]!, right: initial[index]! })

  let cursor = 0
  let maxAcceptedError = 0
  while (cursor < pending.length && evaluated.size < maxPoints) {
    const interval = pending[cursor++]!
    const midpoint = geometricMidpoint(
      interval.left.frequency,
      interval.right.frequency,
    )
    if (
      midpoint === interval.left.frequency ||
      midpoint === interval.right.frequency
    )
      // No representable interior frequency remains to probe.
      continue
    const middle = evaluateAt(midpoint)
    const error = interpolationError(interval.left, middle, interval.right)
    if (error > relativeTolerance) {
      pending.push({ left: interval.left, right: middle })
      pending.push({ left: middle, right: interval.right })
    } else maxAcceptedError = Math.max(maxAcceptedError, error)
  }

  const unresolvedIntervals = pending.length - cursor
  return {
    samples: [...evaluated.values()]
      .sort((a, b) => a.frequency - b.frequency)
      .map(({ frequency, value }) => ({ frequency, value })),
    diagnostics: {
      converged: unresolvedIntervals === 0,
      evaluations: evaluated.size,
      maxPoints,
      relativeTolerance,
      unresolvedIntervals,
      maxEstimatedError:
        unresolvedIntervals === 0 ? maxAcceptedError : Infinity,
    },
  }
}

function validateOptions(
  minHz: number,
  maxHz: number,
  initialPoints: number,
  maxPoints: number,
  tolerance: number,
  landmarks: readonly number[],
): void {
  if (
    !Number.isFinite(minHz) ||
    minHz <= 0 ||
    !Number.isFinite(maxHz) ||
    maxHz <= minHz
  )
    throw new RangeError(
      'Frequency bounds must be finite, positive and increasing',
    )
  if (!Number.isSafeInteger(initialPoints) || initialPoints < 2)
    throw new RangeError('initialPoints must be an integer of at least 2')
  if (
    !Number.isSafeInteger(maxPoints) ||
    maxPoints < initialPoints ||
    maxPoints > 8_192
  )
    throw new RangeError(
      'maxPoints must be an integer from initialPoints to 8192',
    )
  if (!Number.isFinite(tolerance) || tolerance <= 0 || tolerance > 1)
    throw new RangeError('relativeTolerance must be finite and in (0, 1]')
  if (!landmarks.every(Number.isFinite))
    throw new RangeError('Landmark frequencies must be finite')
}

function initialFrequencies(
  minHz: number,
  maxHz: number,
  count: number,
  landmarks: readonly number[],
): number[] {
  const logMin = Math.log(minHz)
  const logSpan = Math.log(maxHz) - logMin
  const frequencies: number[] = [minHz]
  for (let index = 1; index < count - 1; index += 1)
    frequencies.push(Math.exp(logMin + (index / (count - 1)) * logSpan))
  frequencies.push(maxHz)
  for (const landmark of landmarks) {
    if (landmark < minHz || landmark > maxHz) continue
    const nearIndex = frequencies.findIndex(
      (frequency) =>
        Math.abs(frequency - landmark) <=
        4 * Number.EPSILON * Math.max(frequency, landmark),
    )
    if (nearIndex > 0 && nearIndex < count - 1)
      frequencies[nearIndex] = landmark
    else if (nearIndex < 0) frequencies.push(landmark)
  }
  const result = [...new Set(frequencies)].sort((a, b) => a - b)
  if (result.length < count)
    throw new RangeError(
      'Frequency range exceeds supported numerical resolution',
    )
  return result
}

function geometricMidpoint(left: number, right: number): number {
  const midpoint = Math.exp(
    Math.log(left) + (Math.log(right) - Math.log(left)) / 2,
  )
  // Log/exp can lose the few low bits that distinguish close frequencies.
  return midpoint > left && midpoint < right
    ? midpoint
    : left + (right - left) / 2
}

function interpolationError<T>(
  left: Evaluated<T>,
  middle: Evaluated<T>,
  right: Evaluated<T>,
): number {
  let maximum = 0
  for (let index = 0; index < middle.metrics.length; index += 1) {
    const actual = middle.metrics[index]!
    const scale = Math.max(
      Math.abs(left.metrics[index]!),
      Math.abs(actual),
      Math.abs(right.metrics[index]!),
      1e-12,
    )
    const expectedNormalized =
      left.metrics[index]! / scale / 2 + right.metrics[index]! / scale / 2
    maximum = Math.max(maximum, Math.abs(actual / scale - expectedNormalized))
  }
  return maximum
}
