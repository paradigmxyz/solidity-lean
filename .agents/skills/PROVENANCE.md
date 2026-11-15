# Provenance of the vendored Lean skills

Upstream: https://github.com/leanprover/skills
Commit: `7d3da0282e7b724b07620e45cf212f2e05e19334` (2026-02-21)
License: Apache-2.0, upstream's `LICENSE` copied unchanged into this directory.

Copied byte for byte from upstream's `skills/<name>/SKILL.md`, nothing else:

| Skill | sha256 |
|---|---|
| `lean-proof` | `362c42ddae83b8d52ceaadd6efa32f707a15ebe83e25038fc08d75a329d60a41` |
| `lean-mwe` | `fac0a3b05adcba700d1c80fd79feab81305c468fbb42bf35d20cb4e6fa9b62f6` |
| `mathlib-build` | `1fc8be5e72f07de5c8cc3d7daf6325ce6079eb353773f72889d765cb28f2f4f8` |
| `lean-bisect` | `c1a997f1c709b835b8cfeae16b5c5c8aa262030a32be1e78eac81abee448e7d1` |
| `LICENSE` | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |

Left out on purpose: `lean-setup` (builds the Lean compiler with CMake; this repository uses
Lake and the toolchain pinned in `lean-toolchain`), `lean-pr`, `mathlib-pr`, `mathlib-review`
and `nightly-testing` (upstream contribution workflows), and upstream's test fixtures and plugin
manifests. The files are not edited: this repository's overrides live in the root `AGENTS.md`
("Skills"), which takes precedence over them.

## Updating the pin

```sh
rev=<new upstream commit>
git clone https://github.com/leanprover/skills /tmp/lean-skills && git -C /tmp/lean-skills checkout "$rev"
for s in lean-proof lean-mwe mathlib-build lean-bisect; do
  cp /tmp/lean-skills/skills/$s/SKILL.md .agents/skills/$s/SKILL.md
done
cp /tmp/lean-skills/LICENSE .agents/skills/LICENSE
(cd .agents/skills && sha256sum LICENSE */SKILL.md)
```

Then update the commit and hashes above, read the upstream diff for advice that conflicts with
the root `AGENTS.md` (`sorry`, axioms, `native_decide`, toolchain changes), and adjust the
overrides there in the same change.
