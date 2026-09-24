# Contributing to Specula

Thank you for your interest in contributing to Specula!

## Developer Certificate of Origin (DCO)

This project uses the [Developer Certificate of Origin (DCO)](https://developercertificate.org/).
By contributing, you certify that you have the right to submit the work under
the project's open source license (Apache 2.0).

All commits must be signed off to indicate agreement with the DCO:

```
Signed-off-by: Your Name <your.email@example.com>
```

### How to sign off

Add `-s` (or `--signoff`) when committing:

```bash
git commit -s -m "your commit message"
```

If you forgot to sign off, amend the last commit:

```bash
git commit --amend -s
```

### What it means

By signing off, you agree to the terms in the [DCO](DCO) file — essentially
that the contribution is your own work (or you have the right to submit it)
under the project's license.

## Getting Started

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Ensure all commits are signed off
5. Submit a pull request

## Specula Lite resources

Lite bundles existing skill guides and the TLC output reader so it can be installed independently. Edit their original files, then regenerate the resource archive with `python3 scripts/infra/bundle_lite.py`. CI checks that `skills/specula-lite/assets/shared.zip` matches those sources. Lite-specific workflow rules belong in `skills/specula-lite/SKILL.md`.

## License

By contributing, you agree that your contributions will be licensed under the
[Apache License 2.0](LICENSE).
