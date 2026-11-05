# Version 6 — 5 November 2026

Publication version. Article (archived separately on Zenodo): the title page no longer marks a working draft; OE and SBP are defined at first use and the notation Pair(G) is explained. Theorem-like labels carry their type, so cross-references print correctly with current cleveref (TeX Live 2025). The triangle figure is drawn by pgfplots from the analytic formulas inside the article; `triangle_constraint.pdf`/`.png` remain as output of the numerical scripts. Section 8 describes the version 6 verification.

Lean comment headers are version-neutral; no statement or proof changed. Both libraries were rebuilt and audited on macOS 26 with the unchanged manifest; the audit is identical to version 5. This repository now holds only code and verification records, under Apache-2.0; the article is archived on Zenodo under CC BY 4.0. Added CITATION.cff and .gitignore. The version 5 Linux verification records moved to `history/`. See HOST_VERIFICATION.md.

# Draft 5

Editorial polish after v4 review; published DOI added; consistent Lean headers; fresh Git-manifest build, dependency revision check and 35-declaration audit. Versioned filenames retained. See history/v5_linux_verification/HOST_VERIFICATION.md.

# Draft 4

Corrected Gamma expectation subscript; supplied elementary spectral proof of projection estimate; added precise calibration corollary; distinguished classification from reconstruction; moved polygon criterion before determinant formulas; explained reference-measure dependence and cited Hwang; updated published references and narrowed Lean claims. All new deliverables have v4 filenames.

# Working draft 3 — 26 October 2026

Substantive revision responding to the supplied Claude review. Adds homogeneous
representation and covariant descent theorems, finite-group rounding, the Z3
Bargmann interpretation, the unique Gibbs limit, mean-deficit asymptotics, and
an exact two-frame law. Revises physical interpretation and literature positioning.

Adds CoherentExtensions.lean, rebuilds both libraries and re-audits 35 declarations.
Adds verify_extensions.py and its numerical report. See LEAN_COVERAGE.md
for qualifications and scope.

---

# Working draft 2 — 26 October 2026

- Added Sarlette and Sepulchre, *Consensus optimization on manifolds*, and an explicit comparison with reference-free Grassmann consensus.
- Clarified that the selection energy is projector-distance alignment and that Gibbs concentration is a general mathematical mechanism.
- Rewrote the contribution around reconstructing comparison composition from representability and losslessness.
- Distinguished this interpretive contribution from mathematical priority, empirical novelty, and a physical derivation of the selection principle.
- Explained why equivalent relational and ambient-space descriptions do not settle ontological priority.
- Specified concrete requirements for further physical and mathematical progress.
- Updated abstract, introduction, discussion, conclusion, and bibliography.

The numbered mathematical statements and Lean source are unchanged. The original successful build and axiom audit remain applicable to that exact source. They were not rerun for this textual revision. The coverage document identifies the certified results and the unformalized parts.
