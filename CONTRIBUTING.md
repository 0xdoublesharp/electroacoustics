# Contributing

Use a minimal, synthetic input to reproduce an issue. Include the frequency range, SI parameters, expected result, and actual result. For numerical changes, link the published equation or describe the independent calculation that establishes the expected result.

Keep library code deterministic and dependency-free at runtime. Provide driver parameters, geometry, losses, and operating limits as explicit inputs. Keep manufacturer catalogs, design files, measured responses, calibration tables, and private research out of source, tests, and package artifacts. Cite references without copying their figures, tables, or code unless the material is compatible with the project's license.

## Check a change

```sh
npm ci
npm run check
```

The check typechecks the source, requires 100% statement, branch, function, and line coverage, and installs the actual npm archive in a clean consumer to verify its contents, ESM entry point, and TypeScript declarations. Add a synthetic regression when changing solver behavior. Document changed units, phase conventions, defaults, or error behavior in the pull request.

## Run the invariant tests

The regular test suite runs 100 generated cases per invariant with a fixed seed. Run just the invariant tests with `npm run test:fuzz`. Set `FUZZ_RUNS` and `FUZZ_SEED` for a longer campaign with a different seed.

```sh
FUZZ_RUNS=1000 FUZZ_SEED=12345 npm run test:fuzz
```

On failure, fast-check reports a reduced counterexample and its seed and path. Replay it by setting `FUZZ_SEED` and `FUZZ_PATH` from the report and selecting the failed test by name with `npm run test:fuzz -- -t 'test name'`.

## Check the mathematical proofs

The local Lean 4 project checks operating limits, circuit equations, and duct tuning invariants. See the [proof commands and assumptions](verification/lean/README.md).

Contributions are distributed under the [MIT license](LICENSE). See the [release policy](PUBLISHING.md) for package and versioning rules.
