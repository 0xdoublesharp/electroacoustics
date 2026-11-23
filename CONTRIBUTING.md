# Contributing

Use a minimal, synthetic input to reproduce an issue. Include the frequency range, SI parameters, expected result, and actual result. For numerical changes, link the published equation or describe the independent calculation that establishes the expected result.

Keep library code deterministic and dependency-free at runtime. Provide driver parameters, geometry, losses, and operating limits as explicit inputs. Keep manufacturer catalogs, design files, measured responses, calibration tables, and private research out of source, tests, and package artifacts. Cite references without copying their figures, tables, or code unless the material is compatible with the project's license.

## Check a change

```sh
npm ci
npm run check
```

The check typechecks the source, runs the solver tests, and installs the actual npm archive in a clean consumer to verify its contents, ESM entry point, and TypeScript declarations. Add a synthetic regression when changing solver behavior. Document changed units, phase conventions, defaults, or error behavior in the pull request.

Contributions are distributed under the [MIT license](LICENSE). See the [release policy](PUBLISHING.md) for package and versioning rules.
