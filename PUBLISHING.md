# Publishing

Maintainers release `@0xdoublesharp/electroacoustics` from a reviewed commit on `main`. Use [Semantic Versioning](https://semver.org/). Changes to exported types, units, sign conventions, defaults, or numerical behavior belong in the release notes. Compatibility-breaking changes require an explicit version bump.

## Verify the release

1. Update the version in `package.json` and `package-lock.json` together. Merge the changes and wait for CI.
2. Tag the reviewed commit as `v<version>`. The workflow checks the tag against the manifest and checks that the commit is on `main`.
3. Run [Stage npm release](https://github.com/0xdoublesharp/electroacoustics/actions/workflows/publish.yml) for that tag. The build tests the archive before passing the same file to the staging job. The archive contains compiled ESM, declarations, and required package metadata.
4. Review the staged version on npm. Approve it with 2FA, verify the registry version, and then create the GitHub release for the tag.

```sh
gh workflow run publish.yml --ref v0.1.1
npm stage list @0xdoublesharp/electroacoustics
npm stage approve <stage-id>
npm view @0xdoublesharp/electroacoustics@0.1.1 version
```

## First release and trusted publishing

A new package needs an npm registry entry before a trusted publisher can be configured. For the initial release, a maintainer with rights to the npm scope builds the approved tag, runs the same validation locally, and stages the verified archive using an authenticated npm session with 2FA available for approval.

```sh
npm ci
npm run typecheck
npm test
npm run build
npm run check:pack -- /absolute/path/to/release
npm stage publish /absolute/path/to/release/0xdoublesharp-electroacoustics-0.1.0.tgz --access public
```

Once the package exists, configure the GitHub Actions trusted publisher in npm when the first OIDC release is ready. npm requires a new connection to complete its first successful publish within two days.

| Setting | Value |
| --- | --- |
| Organization | `0xdoublesharp` |
| Repository | `electroacoustics` |
| Workflow | `publish.yml` |
| GitHub environment | `npm-release` |
| Allowed operations | Stage publishing |

The stage job requests an OIDC token on a GitHub-hosted runner. A maintainer approves public publication on npm. After the first successful OIDC release, restrict token-based publishing in the npm package settings.

[Staged publishing](https://docs.npmjs.com/staged-publishing/) · [Trusted publishing](https://docs.npmjs.com/trusted-publishers/)
