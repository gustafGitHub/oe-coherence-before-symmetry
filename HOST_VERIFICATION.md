# Verification environment

5 November 2026. macOS 26.6.2 (Apple silicon, arm64), official Lean 4.19.0
release (commit 6caaee842e94) installed by elan, Apple clang 21.0.0.

The six source/configuration files (two libraries, Audit.lean, lean-toolchain,
lakefile.toml, lake-manifest.json) were copied into a fresh directory with no
.lake tree. Lake cloned all dependencies via Git, `lake exe cache get`
supplied the compiled mathlib files, and `lake build` and
`lake env lean Audit.lean` then completed successfully. Afterwards the six
inputs were compared byte for byte with the package files, and every
dependency HEAD was checked against its manifest revision.

The compiled mathlib files came from the user-level mathlib cache
(`~/.cache/mathlib`), which `lake exe cache get` had populated from the
official mathlib cache server on 27 October 2026; CACHE_LOG.txt therefore
reports "No files to download". This is a cache retrieval, not a from-source
rebuild of all of mathlib.

## macOS 26 linker settings

On macOS 26, executables that Lean 4.19.0 links with its bundled linker are
rejected at launch (`dyld: __DATA_CONST segment missing SG_READ_ONLY flag`).
This affects mathlib's `cache` tool, so a plain `lake exe cache get` fails.
The `lean` and `lake` binaries themselves are unaffected. The build therefore
ran with the system compiler and the toolchain's static libraries:

```sh
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.19.0
export LIBRARY_PATH="$TC/lib:$TC/lib/lean" LEAN_CC=/usr/bin/clang
lake exe cache get
lake build
lake env lean Audit.lean
```

These settings only change how the cache tool is linked. No proof, kernel,
library, manifest, or dependency source was modified. They should not be
needed on Linux; earlier macOS versions were not tested.

CACHE_LOG.txt, BUILD_LOG.txt, AXIOM_AUDIT.txt and DEPENDENCY_REVISIONS.txt
record this run.

The recorded JSON reports were produced earlier with the same scripts. On this machine
(Python 3.9.6, numpy 2.0.2, scipy 1.13.1, matplotlib 3.9.4) they again report
PASS. All non-floating-point fields of both JSON reports are identical to the
recorded reports, and floating-point values differ by at most 1.4e-15. The
recorded reports are kept unchanged.
