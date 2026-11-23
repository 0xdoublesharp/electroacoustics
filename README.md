<p align="center">
  <img src="https://raw.githubusercontent.com/0xdoublesharp/electroacoustics/main/assets/logo.png" width="160" alt="Electroacoustics logo showing a mint sine wave across a loudspeaker cone">
</p>
<h1 align="center">Electroacoustics</h1>

Dependency-free TypeScript solvers for low-frequency loudspeaker circuits, ducts, and filters. Supply the driver, acoustic volume, and duct geometry in SI units to predict impedance, sound pressure, cone excursion, and port velocity.

## Install

```sh
npm install @0xdoublesharp/electroacoustics
```

The package ships ESM and TypeScript declarations for Node.js 22 or later and modern browser bundlers.

## Solve a loudspeaker circuit

```ts
import { createCircuit, sweepCircuit, type CircuitInput } from '@0xdoublesharp/electroacoustics'

const sealed: CircuitInput = {
  driver: {
    fsHz: 25,
    vasM3: 0.08,
    qes: 0.45,
    qms: 8,
    reOhms: 6,
    leHenries: 0,
    sdM2: 0.05,
  },
  volumeM3: 0.07,
  voltageRms: 2.83,
  medium: { densityKgM3: 1.2041, soundSpeedMps: 343 },
  leakageQuality: 15,
  absorptionQuality: 30,
}

const point = createCircuit(sealed)(40)
console.log(point.impedanceOhms, point.splDb, point.coneExcursionPeakM)

const vented: CircuitInput = {
  ...sealed,
  port: { areaM2: 0.012, effectiveLengthM: 0.3, quality: 7 },
}

const response = sweepCircuit(vented, {
  minHz: 10,
  maxHz: 200,
  relativeTolerance: 0.005,
  maxPoints: 768,
  filter: { highpassHz: 24, highpassType: 'BW24' },
})
console.log(response.points.length, response.sampling.converged)
```

These values describe an illustrative driver and enclosure. To use a distributed port, pass `port.ductPath` with straight, conical, or exponential sections and retain `port.quality`. The path takes precedence over the lumped area and effective length.

## Solver API

| Task | Exports |
| --- | --- |
| Solve a circuit or sweep a frequency band | `createCircuit`, `sweepCircuit`, `referenceResonanceHz` |
| Evaluate duct impedance, tuning, or velocity | `ductPathImpedance`, `ductPathTuning`, `ductPathTuningResidual`, `ductPathEquivalentLength`, `ductPathPeakVelocityRatio` |
| Evaluate complex filter transfer functions | `lr24Transfer`, `bw24Transfer`, `composeFilters`, `lr24AttenuationDb`, `bw24AttenuationDb` |
| Estimate drive and filtered voltage limits | `analyzeOperatingDrive`, `analyzeFilteredVoltageLimit` |
| Refine a frequency grid or vary inputs | `sampleAdaptive`, `analyzeSensitivity` |

## Model conventions

- Voltage, current, pressure, and volume-flow phasors use RMS values and the `exp(jωt)` convention. Cone excursion and port speed are sinusoidal peak values.
- The default radiation convention is half-space (2π steradians) at 1 m. Pressure combines cone, mouth, and leakage flow and excludes propagation delay.
- Wiring defaults to one driver. For multiple identical drivers in a shared cavity, specify `quantity` and the number of drivers per series string in `seriesDrivers`. Set a loss quality factor to `Infinity` to remove that loss branch.
- Adaptive sweeps report numerical convergence and unresolved intervals. Sensitivity varies one caller-supplied parameter at a time on a shared frequency grid.
- The circuit assumes a linear driver, a lumped cavity, and rigid one-dimensional ducts. Operating estimates scale the small-signal response against caller-supplied limits. The thermal proxy represents copper loss. Validate real cabinet behavior with measurements.

## Development

Run `npm ci` followed by `npm run check`. The tests use synthetic inputs, analytic limits, and independent numerical comparisons. See [how to contribute](https://github.com/0xdoublesharp/electroacoustics/blob/main/CONTRIBUTING.md) and the [release policy](https://github.com/0xdoublesharp/electroacoustics/blob/main/PUBLISHING.md).

[MIT license](https://github.com/0xdoublesharp/electroacoustics/blob/main/LICENSE)
