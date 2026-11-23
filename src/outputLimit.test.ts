import { expect, it } from 'vitest'
import * as api from './index.js'
import { circuitFixture } from './testFixtures.js'

it('reports an amplifier-current bottleneck and subtracts DSP boost from headroom', () => {
  const source = {
    perDriverReferenceVoltage: 2, seriesDriversPerString: 2, parallelStrings: 1,
    dcResistancePerDriver: 3, xmaxMeters: 0, ratedPowerWattsPerDriver: 0,
    points: [
      { frequency: 25, coneExcursionMeters: 0.001, portVelocity: 0, portMach: 0, impedanceOhms: 4, splDb: 80 },
      { frequency: 50, coneExcursionMeters: 0.001, portVelocity: 0, portMach: 0, impedanceOhms: 10, splDb: 90 },
    ],
  }
  const result = api.analyzeOutputLimit(source, {
    maxAmplifierVoltageRms: 15, maxAmplifierCurrentRms: 2,
    driveVoltageRms: 4, filter: { gainDb: 6.020599913279624 },
  })
  expect(result.points[0]).toMatchObject({ maxTerminalVoltageRms: 8,
    maxInputVoltageRms: 4, limitingFactor: 'amplifier-current', headroomDb: 0 })
  expect(result.points[0]!.maxSplDb).toBeCloseTo(86.0206)
  expect(result.points[1]).toMatchObject({ maxTerminalVoltageRms: 15, limitingFactor: 'amplifier-voltage' })
  expect(result.bandInputLimit).toEqual({ value: 4, frequency: 25 })
})

it('reports unavailable headroom for missing limits, pressure, and DSP at a null', () => {
  const at = api.createCircuit(circuitFixture)
  const src = api.operatingSourceFromCircuit(circuitFixture, [at(25)], { xmaxMeters: 0, ratedPowerWattsPerDriver: 0 })
  expect(api.analyzeOutputLimit(src).points[0]!.limitingFactor).toBeNull()
  const quiet = api.analyzeOutputLimit(src, { maxAmplifierVoltageRms: 2, filter: { gainDb: -8000 } })
  expect(quiet.points[0]).toMatchObject({ maxTerminalVoltageRms: 2, maxInputVoltageRms: null, maxSplDb: null })
  const { splDb: _, ...point } = src.points[0]!
  const missing = { ...src, points: [{ ...point, radiatorExcursionPeakM: 0 }] }
  expect(api.analyzeOutputLimit(missing, { maxRadiatorExcursionPeakM: 1, maxAmplifierVoltageRms: 2, driveVoltageRms: 3 }).points[0])
    .toMatchObject({ limitingFactor: 'amplifier-voltage', plannedSplDb: null, maxSplDb: null })
  expect(() => api.analyzeOutputLimit(src, { maxRadiatorExcursionPeakM: 1 })).toThrow(/radiator/)
  expect(() => api.analyzeOutputLimit(src, { maxAmplifierCurrentRms: -1 })).toThrow(/finite limits/)
  expect(() => api.analyzeOutputLimit(src, { maxAmplifierCurrentRms: Number.MAX_VALUE })).toThrow(/numeric range/)
  expect(() => api.analyzeOutputLimit(src, { maxAmplifierVoltageRms: 2, filter: { gainDb: -6400 } })).toThrow(/DSP input limit/)
})
