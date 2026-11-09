# Version 1 — 9 November 2026

First public release, accompanying version 1 of the article *Coherence Before
Symmetry: Positive Kernels, Random Frames, and Compatible Perspective
Transformations* (archived on Zenodo).

- `CoherentPerspectives.lean`, `CoherentExtensions.lean`: Lean 4.19.0/mathlib
  formalization of the core reconstruction. `Audit.lean` audits 35
  declarations; only standard logical axioms are used.
- `verify_model.py`, `verify_extensions.py`: seeded numerical checks with
  recorded reports.
- Build, audit and environment records from macOS 26; see `HOST_VERIFICATION.md`.
