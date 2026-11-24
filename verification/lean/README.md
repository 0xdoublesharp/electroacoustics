# Electroacoustics proofs

Install [Elan](https://lean-lang.org/install/) to use the Lean version pinned in this directory. From the repository root, run the full verification.

```sh
npm ci
npm run verify:formal
```

The runner executes `npm run check`, builds `Electroacoustics` and `ElectroacousticsReplay` with warnings treated as errors, and checks the axiom dependencies of eight installed-archive certificate replays. It also checks that each replay script rejects a tampered certificate. The cases cover peaking EQ, straight and mouth-corrected tapered duct headroom, tapered duct tuning and peak velocity, and driver, full-rank enclosure, and poorly identified enclosure fits.

The runner uses isolated build and temporary directories under `/Volumes/Scratch/electroacoustics`. Set `ELECTROACOUSTICS_SCRATCH_DIR` to override that location or use `TMPDIR` as a fallback on a host without that volume. The runner removes its build and temporary directories and retains the shared Mathlib download cache. Set `MATHLIB_CACHE_DIR` to use an existing cache in another location.

To check only the Lean project, copy this directory to Scratch and run `lake exe cache get` followed by `lake build` in the copy. The first run fetches the pinned dependencies, including the interval evaluator. [LeanCert](https://github.com/alerad/leancert/tree/44b323a0d6af00211d5013f6e021432db032087c)

## Replay certificates in Lean

Build the npm package and check the Lean project first. Save a returned `certificate` as JSON, then run the relevant command from the repository root. Set `LEAN_PROJECT` to the absolute path of the checked Lean project and `TMPDIR` to an existing Scratch directory for the generated Lean file. The scripts validate the certificate against the recorded request in TypeScript, encode finite binary64 values as exact binary rationals, and emit a theorem checked with `decide +kernel` by default. The generated theorem prints its axiom dependencies. The optional `--native` mode evaluates the Boolean checks with compiled code and adds an evaluation axiom.

### Replay a band certificate

Use a resolved result from `analyzeBandOutputLimit`. The [band replay script](../../scripts/replay-band-certificate.mjs) and [Lean evaluator](ElectroacousticsReplay.lean) cover sealed, lumped-vented, passive-radiator, and distributed-duct models, including straight, conical, and exponential sections, multiple sections and parallel paths, inlet and outlet corrections, signed junction inertances, and reactive section factors. Replay uses the designed or supplied normalized biquad coefficients and independently checks the full-band voltage cover, upper witness, and dB gap. The distributed model evaluates the coupled circuit through duct impedance poles and encloses Mach over every position in each section.

```sh
node scripts/replay-band-certificate.mjs /path/to/band.json > "$TMPDIR/BandReplay.lean"
(cd "$LEAN_PROJECT" && lake env lean "$TMPDIR/BandReplay.lean")
```

`npm run check:pack` writes all eight installed-archive certificates when `ELECTROACOUSTICS_REPLAY_DIR` is set. The individual output variables `ELECTROACOUSTICS_REPLAY_CERTIFICATE` and `ELECTROACOUSTICS_DUCT_REPLAY_CERTIFICATE` select the peaking EQ and uncorrected straight duct band cases, respectively. Unresolved band results can carry runtime dyadic-verified partial bounds. Full replay requires a resolved certificate.

### Replay a duct certificate

The duct replay script accepts a resolved certificate from `boundDuctPathTuning` or `boundDuctPathPeakVelocityRatio`. The Lean tuning checker verifies endpoint signs, pole exclusion, and strict negativity on the earlier-frequency cover from DC. The peak velocity checker verifies a witness and a complete position cover for each section, normalized by total throat flow. Both checks certify the requested relative width. [Duct replay script](../../scripts/replay-duct-certificate.mjs) · [Duct certificate checker](Electroacoustics/DuctCertificate.lean)

```sh
node scripts/replay-duct-certificate.mjs /path/to/duct.json > "$TMPDIR/DuctReplay.lean"
(cd "$LEAN_PROJECT" && lake env lean "$TMPDIR/DuctReplay.lean")
```

### Replay an impedance-fit certificate

Use the optional certificate from `fitDriverImpedance` or `fitEnclosureImpedance`. The [fit replay script](../../scripts/replay-fit-certificate.mjs) supports driver fits with a known added mass or sealed test box, and enclosure fits for sealed, lumped-vented, and passive-radiator systems. Lean independently encloses the residuals and exact normalized-coordinate derivatives at the fitted point. It checks parameter feasibility, the RMS and projected-gradient bounds, the sensitivity witness, and the endpoint conditions for the status.

```sh
node scripts/replay-fit-certificate.mjs /path/to/fit.json > "$TMPDIR/FitReplay.lean"
(cd "$LEAN_PROJECT" && lake env lean "$TMPDIR/FitReplay.lean")
```

## Verified properties

| Module | What Lean checks |
| --- | --- |
| [Accuracy](Electroacoustics/Accuracy.lean) | Finite binary64 decoding, exact-ratio nearest-even rounding on the chosen grid, the interval representative error criterion, outward endpoint rounding, and the scaled RMS pressure logarithm with floor. |
| [Interval](Electroacoustics/Interval.lean) | Rational enclosure arithmetic, guarded division, square and square root, widening, and integer dyadic floor, ceiling, and square-root bounds. |
| [Transcendentals](Electroacoustics/Transcendentals.lean) | Rational brackets for π, ln(10), and ln(2), transcendental remainder and range reduction bounds, and the continuous duct wave functions through cutoff. |
| [Circuit](Electroacoustics/Circuit.lean) | Cleared small-signal balances, power conservation, passivity and denominator nonvanishing under the model hypotheses, terminal impedance and coil loss under series/parallel wiring, and the mass-controlled limit. |
| [Radiator](Electroacoustics/Radiator.lean) | Cleared radiator balances, denominator nonvanishing under passivity hypotheses, power including radiator damping, and cancellation at the free lossless radiator notch. |
| [Filters](Electroacoustics/Filters.lean) | Exact biquad stability predicate, nonzero unit-circle denominator, centered and endpoint transfer identities, peaking and shelf properties, analog transfer magnitudes and dB formulas, and pure delay and cascade magnitude identities. |
| [Design](Electroacoustics/Design.lean) | Sealed Q and F3, lumped vent and radiator inverses, affine duct-volume inverse, length bisection given continuity and antitonicity, known measurement perturbations, and exact DSP scaling and biquad identities. |
| [Operating](Electroacoustics/Operating.lean) | Sampled drive ceilings for linear travel and Mach, per-driver coil loss, amplifier voltage and current, and the exact feasibility and dB headroom identities. |
| [BandHeadroom](Electroacoustics/BandHeadroom.lean) | Frequency cover preservation, safe voltage from utilization ceilings, infeasibility above a witness-derived voltage, and the dB gap bound. |
| [BandCertificate](Electroacoustics/BandCertificate.lean) | Soundness of the rational full-cover, safe-voltage, witness, and gap checks given a sound evaluator. The partial checker proves individual bound and partition properties. |
| [ElectroacousticsReplay](ElectroacousticsReplay.lean) | Independent interval model for the circuit and DSP, including the general distributed branch and full-section Mach bounds, connected to the full band certificate checker. |
| [Duct](Electroacoustics/Duct.lean) | Cleared tuning residual, pole and first-root exclusion, bracket preservation, and spatial and frequency-position peak bounds from covers and witnesses. |
| [DuctTransfer](Electroacoustics/DuctTransfer.lean) | Propagating, evanescent and cutoff transfer determinants, cascaded power and DC inertance, inertive termination, and the cleared passive circuit. The uncorrected uniform open duct has a unique tuning before its first pole and a mouth peak. |
| [DuctInterval](Electroacoustics/DuctInterval.lean) | Sound enclosures for general duct transfer, DC mass, tuning residual, and the spatial peak over a frequency box. |
| [DuctCertificate](Electroacoustics/DuctCertificate.lean) | First positive pole-free tuning bracket with a DC-to-bracket exclusion cover, and normalized peak velocity from a witness and per-section covers, both within the stated relative tolerance. |
| [Numerics](Electroacoustics/Numerics.lean) | Positive damped normal form, feasible projection, local first-order bounds, RMS and Jacobian rank criteria, equivalent cavity loss splits, and interpolated cutoff. |
| [ImpedanceCertificate](Electroacoustics/ImpedanceCertificate.lean) | Dual interval evaluation of residuals and derivatives, endpoint feasibility, RMS and projected gradient, full-rank or weak-direction witnesses, and status implications. |
| [Summaries](Electroacoustics/Summaries.lean) | Adaptive midpoint test and landmark properties, filtered phasor scaling, phase wrap and sampled delay, summary bounds, and scenario envelope and ranking. |
| [Audit](Electroacoustics/Audit.lean) | Checks every public theorem in the 17 library modules. The library audit, the replay model audit, and the installed-archive replays allow only `propext`, `Classical.choice`, and `Quot.sound`. |

## Scope and assumptions

The proofs concern exact real and complex models. A successful kernel replay certifies the particular band enclosure, standalone duct tuning or speed bound, or supported fit endpoint encoded in the generated Lean file. Runtime dyadic checks cover partial band bounds and can also certify distributed-duct impedance fits. Distributed-duct fits are outside the fit replay script's scope. General TypeScript and V8 binary64 correspondence, the floating search trajectory, and global fit optimality are outside kernel replay. Fit replay proves a weak direction for poor identification and a local first-order bound at the returned point. The runtime fit checker handles the exact deficient-rank count and the search distinction between a stalled step and the iteration limit. [Solver accuracy contracts](../../docs/CONTRACTS.md) · [Invariant tests](../../src/invariants.test.ts) · [High-precision references](../../src/highPrecision.test.ts)

## Measured impedance spot checks

The fixtures and measurement comparisons are in the [high-precision regression suite](../../src/highPrecision.test.ts).

- **Sealed.** The THOR model gives a 36.03 Hz characteristic resonance from the published driver and box inputs. The impedance-derived pole frequencies imply about 35.68 Hz. [THOR measurements](https://www.linkwitzlab.com/thor-measmt.htm) · [Driver datasheet](https://madisound.com/pdf/peerless/830500.pdf)
- **Vented.** The Illinois Altec 755-C fixture gives modeled impedance peaks at 28.74 and 83.83 Hz using the published geometry and conventional end corrections. The measured peaks are at 28.91 and 72.62 Hz. The report identifies uncertainty in the free-air driver measurement. [Illinois fixture report](https://courses.physics.illinois.edu/phys406/sp2017/Student_Projects/Spring16/Thomas_Jerome_Physics_406_Final_Report_Sp16.pdf)
- **Passive radiator.** The PURIFI test-box model gives peaks at 28.11 and 56.24 Hz, near 28 and 56 Hz on the published measured trace. This spot check uses PURIFI’s fitted parameters and approximates the driver’s blocked impedance with a single inductance. [PURIFI test-box measurements](https://purifi-audio.com/blog/tech-notes-1/spk16-reference-design-12)
