# Coherence Before Symmetry — Lean formalization and numerical checks

Companion code to Gustaf Ullman, *Coherence Before Symmetry: Positive Kernels,
Random Frames, and Compatible Perspective Transformations*, version 1
(5 November 2026).

The article shows when positive comparisons between perspectives become a
system of unitary transformations: maximal overlap forces exact composition,
and when a group organizes the perspectives, a positive-definite comparison
function with maximal overlap must itself be a unitary representation. This
repository contains the Lean 4/mathlib formalization of the core reconstruction
and the seeded numerical checks. The article itself is archived on Zenodo.

<!-- Add the article DOI (Zenodo) here once it is known. -->

## Contents

- `CoherentPerspectives.lean`: verified Gram-family and scalar core.
- `CoherentExtensions.lean`: block positivity in arbitrary finite dimension,
  homogeneous representations, vector defect bound, and cocycle algebra.
- `Audit.lean`, `AXIOM_AUDIT.txt`, `BUILD_LOG.txt`, `CACHE_LOG.txt`,
  `DEPENDENCY_REVISIONS.txt`: build and axiom audit.
- `HOST_VERIFICATION.md`: environment of that run and the macOS 26 linker settings.
- `LEAN_COVERAGE.md`: exact coverage and exclusions.
- `verify_model.py`, `verify_extensions.py`: seeded numerical checks; they also
  write `triangle_constraint.pdf`/`.png`.
- `NUMERICAL_CHECKS.json`, `EXTENDED_NUMERICAL_CHECKS.json`: recorded results.
- `verify_release.sh`, `SHA256SUMS.txt`: checksum, build and audit check.
- `CHANGES.md`, `CITATION.cff`.

## Lean build

Use Lean 4.19.0 (installed automatically by elan from `lean-toolchain`) and the
pinned mathlib commit in the manifest.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

On macOS 26, first set the linker variables described in `HOST_VERIFICATION.md`;
without them `lake exe cache get` fails with a `dyld` error.

The audit covers 35 theorem/construction declarations. Dependencies are limited
to `propext`, `Classical.choice`, and `Quot.sound`; some statements use only
`propext`. No admitted proofs or additional axioms occur. The article's full
analytic and probabilistic content is not thereby formalized; consult the
coverage file.

For a combined checksum, build and audit check from a fresh clone, run
`bash verify_release.sh` (with the macOS 26 variables exported, if applicable).

This is a standalone project. Its Lean pin has not been migrated to the newer
ObserverEquivariance toolchain.

## Numerical checks

```sh
python3 -m pip install -r requirements.txt
python3 verify_extensions.py
```

The extensions script imports and runs the base numerical script. It rewrites
both JSON reports and the figure files. Tests of the exact two-frame law cover
a special case of concentration and the mean-deficit asymptotic, not a numerical
proof of the general-graph theorems. No MCMC results are claimed. With Python
3.9.6, numpy 2.0.2, scipy 1.13.1 and matplotlib 3.9.4 the reports agree with the
recorded ones up to floating-point rounding (at most 1.4e-15).

## License

Copyright 2026 Gustaf Ullman. Licensed under the Apache License 2.0; see
`LICENSE`. The article is published separately on Zenodo under Creative Commons
Attribution 4.0 International.

## Citation

Please cite the article; see `CITATION.cff`.
