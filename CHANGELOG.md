# Changelog

All notable changes to `@0xdoublesharp/electroacoustics` are documented in this file.
This project follows [Semantic Versioning](https://semver.org/).

## [0.2.0] - 2026-11-23

### Added

- **Continuous-band headroom certification** (`analyzeBandOutputLimit`, `verifyBandOutputCertificate`, `BandOutputCertificate`): encloses the single-tone voltage ceiling across a closed frequency band `[minHz, maxHz]` with a 0.1 dB default error bound for sealed, lumped-vented, passive-radiator, and general distributed-duct enclosures (including tapered and multi-section ducts with mouth corrections, junction inertances, and reactive boundary-layer factors). Returns JSON-serializable, 160-bit dyadically self-verified certificates on `resolved` results and dyadically verified partial bounds on `unresolved` results.
- **Certified distributed-duct tuning and peak airspeed bounds** (`boundDuctPathTuning`, `verifyDuctTuningCertificate`, `DuctTuningCertificate`, `boundDuctPathPeakVelocityRatio`, `verifyDuctPeakVelocityCertificate`, `DuctPeakVelocityCertificate`): enclose the first positive pole-free physical tuning (with earlier-root exclusion back to DC) and the peak particle speed across every section interior and junction, with JSON-serializable 160-bit dyadic certificates.
- **Certified impedance-fit diagnostics** (`ImpedanceFitStatus`, `ImpedanceFitCertificate`, `verifyDriverImpedanceFitCertificate`, `verifyEnclosureImpedanceFitCertificate`): computes exact 160-bit forward-mode dual-dyadic residuals, Jacobian, projected KKT gradient, and preconditioned Gram-matrix full-rank or weak-direction witnesses to classify fits as `residual-target`, `stationary`, `bound-constrained`, `poorly-identified`, `stalled`, or `iteration-limit`.
- **Lean 4 formal verification and installed-archive replay** (`npm run verify:formal`, `scripts/replay-band-certificate.mjs`, `scripts/replay-duct-certificate.mjs`, `scripts/replay-fit-certificate.mjs`, `verification/lean/`): 17 Lean library modules (629 audited theorems) plus `ElectroacousticsReplay` (24 axiom checks), verifying all eight certificate classes extracted from the installed npm archive via `decide +kernel` using only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Solver accuracy contracts & high-precision validation** (`docs/CONTRACTS.md`, `src/highPrecision.test.ts`): documents exact domains, units, numerical guarantees, failure modes, and proof boundaries for all 99 public functions and types, validated against independent BigInt/RK4 references and three published measured-box impedance fixtures.

### Changed

- **`solveDuctLengthForTuning`** now accepts an optional `maxIterations` budget (1–200, default 80), returns `bracket` and `iterations` on every result, reserves `status: 'root'` strictly for brackets with `high - low <= toleranceM`, and reports `'budget-exhausted'` or `'resolution-limit'` on early stops.
- **`fitDriverImpedance` and `fitEnclosureImpedance`** now accept `normalizedStepTolerance` and return `status`, `activeBounds`, `projectedGradient`, `sensitivityRank`, and an optional self-verified `certificate`.

### Fixed

- **Complex division underflow, overflow, and rounding** (`div`, `reciprocal`): replaced floating-point complex division with exact integer-scaled arithmetic and ties-to-even binary64 rounding, throwing `RangeError` on true overflow instead of returning nonfinite results or underflowing subnormals.
- **SPL overflow to `Infinity` at extreme pressure scales** (`createCircuit`, `sweepCircuit`): moved pressure scaling into log space so extreme pressure ratios remain finite across the binary64 range.
- **Biquad transfer cancellation near DC, Nyquist, and unit-circle poles** (`biquadTransfer`): switched to 160-bit dyadic centered versine arithmetic with exact `2 * frequencyHz > sampleRateHz` Nyquist validation, guaranteeing per-component error `≤ 2^-40 × max(1, |exact|)` or throwing `RangeError`.
- **Silent nonfinite results in frequency and passive-radiator resonance** (`createCircuit`, `createDriverImpedance`, `passiveRadiatorResonanceHz`): added finite angular-frequency guards and split square-root evaluation to avoid spurious overflow.
- **False `'root'` reporting in `solveDuctLengthForTuning`**: prevented returning `'root'` when bisection stopped before satisfying `toleranceM`.
- **Impedance-fit upper-bound drift and status classification**: pinned normalized `x === 1` unpacking directly to `max` and replaced the finite-difference convergence heuristic with certified dual-dyadic diagnostics.
- **Between-sample headroom overstatement**: closed the reproduced 36% sampled-grid overstatement on narrow EQ peaks with continuous-band interval refinement.

## [0.1.0] - 2026-11-23

### Added

- Initial release of `@0xdoublesharp/electroacoustics` with dependency-free ESM and TypeScript declarations for sealed, lumped-vented, distributed-duct, and passive-radiator enclosures, analog/digital filters, adaptive sweeps, response summaries, operating-limit analysis, sensitivity analysis, and impedance fitting.
