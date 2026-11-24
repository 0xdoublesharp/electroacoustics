# Publishing

Maintainers release `@0xdoublesharp/electroacoustics` from a reviewed commit on `main`. Use [Semantic Versioning](https://semver.org/). Changes to exported types, units, sign conventions, defaults, or numerical behavior belong in the release notes. Compatibility-breaking changes require an explicit version bump.

## Verify and publish the release

1. Update the version in `package.json` and `package-lock.json` together. Merge the changes to `main` and wait for CI.
2. Push an annotated tag named `v<version>` for the reviewed commit. Pushing a `v*` tag triggers [Publish npm release](https://github.com/0xdoublesharp/electroacoustics/actions/workflows/publish.yml) automatically (or trigger it manually with `gh workflow run publish.yml --ref v<version>`).
3. The `verify` job confirms that the tag matches `package.json` and is an ancestor of `origin/main`, runs `typecheck`, `test`, `build`, and `check:pack`, and passes the verified `.tgz` artifact to the `publish` job.
4. The `publish` job publishes directly to npm with GitHub Actions OIDC trusted publishing and provenance (no stored npm token or 2FA prompt). Verify the registry version and create the GitHub release for the tag.

```sh
git tag -a v0.2.1 -m "Release v0.2.1"
git push origin v0.2.1
npm view @0xdoublesharp/electroacoustics@0.2.1 version
```

## First release and trusted publishing

Use Node.js 24 with npm 11.15 or later for OIDC trusted publishing. A new package needs an npm registry entry before a trusted publisher can be configured. For the initial release, a maintainer with rights to the npm scope builds the approved tag, runs the same validation locally, and publishes the verified archive using an authenticated npm session.

```sh
npm ci
npm run typecheck
npm test
npm run build
npm run check:pack -- /absolute/path/to/release
npm publish /absolute/path/to/release/0xdoublesharp-electroacoustics-0.1.0.tgz --access public
```

Before the first OIDC release, create the `npm-release` environment in GitHub repository settings. Under deployment branches and tags, select **Selected branches and tags** and add `v*` as a **Tag** rule. Once the package exists, configure the GitHub Actions trusted publisher on npm with **Direct publishing** enabled.

| Setting | Value |
| --- | --- |
| Organization | `0xdoublesharp` |
| Repository | `electroacoustics` |
| Workflow | `publish.yml` |
| GitHub environment | `npm-release` |
| Allowed operations | Direct publishing (`--allow-publish`) |

The equivalent configuration command is available in an authenticated npm session (if switching from stage-only publishing, revoke the existing stage-only trust ID from `npm trust list @0xdoublesharp/electroacoustics` first or update it in the npm package settings).

```sh
npm trust github @0xdoublesharp/electroacoustics \
  --repo 0xdoublesharp/electroacoustics --file publish.yml \
  --env npm-release --allow-publish
```

The `publish` job requests an OIDC token on a GitHub-hosted runner and publishes with provenance directly to npm. Restrict token-based publishing in the npm package settings so only the trusted publisher can release.

[Trusted publishing](https://docs.npmjs.com/trusted-publishers/)
