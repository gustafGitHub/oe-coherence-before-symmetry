# Lean coverage — version 6

Lean 4.19.0; mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
Both libraries were rebuilt for version 6 from a fresh copy of the sources, using the unchanged distributed Git manifest. All 35 declarations in Audit.lean were audited again; the result is identical to the version 5 audit. Exact dependency revisions are recorded in DEPENDENCY_REVISIONS.txt. Since version 5 only the comment headers of the two Lean libraries changed; no statement or proof changed.

## Original core: CoherentPerspectives.lean

`GramFamily` assumes local linear isometries and the overlap/adjoint identity.
It does not assume the composition law.

Verified: `residual_sq`, `contraction`, `coherence_le`,
`lossless_of_maximal_coherence`, `transport`, `diagonal`, `composition`,
`composition_of_right_lossless`, `lossless_trans`,
`maximal_coherence_composition`, `lossless_of_chain`,
`lossless_of_connected_maximal`, `unitary`, `reference_factorization`,
`triangle_holonomy` (in namespace GramFamily).

Also verified: `saturated_vectors`, `scalar_gram_composition`,
`positive_matrix_gram`, `positive_saturated_composition`,
`positive_saturated_factorization`, `phase_gauge_unique`,
`positive_saturated_triangle`, `frustratedTriangle_not_positive`.

## New core: CoherentExtensions.lean

| Declaration | Mathematical content |
| --- | --- |
| `positive_block_gram` | Matrix.PosSemidef on I × D and identity diagonal blocks imply a GramFamily with exactly the input overlap matrices. |
| `positive_block_saturated_composition` | Entrywise Frobenius saturation gives actual matrix multiplication/composition in all finite dimensions. |
| `positive_block_unitary` | Both conjugate-transpose inverse identities for every overlap block. |
| `positive_homogeneous_multiplicative` | Finite-group homogeneous positive block data imply φ(a)φ(b)=φ(ab). |
| `homogeneousMatrixHom` | Bundled matrix-valued monoid homomorphism constructed from those hypotheses. |
| `positive_homogeneous_unitary` | Every value of that homomorphism is unitary. |
| `GramFamily.vector_defect_bound` | Cauchy–Schwarz vector composition-defect inequality, with the reversed left overlap in the deficit. |
| `homogeneous_multiplicative` | General Gram-family homogeneous composition; the label group need not be finite. |
| `pure_gauge_trivialization` | Abstract group identity underlying trivialization of a factorized comparison system. |
| `gauge_cocycle` | Gauge coordinate changes preserve the cocycle law. |
| `constant_of_identity_covariance` | Abstract group implication u(g,i)u(g,j)⁻¹ = 1 ⇒ u(g,i)=u(g,j), underlying identity-gauge covariance. |
| `descendedCocycleHom` | The resulting normalized residual cocycle is a bundled group homomorphism. |

The matrix homomorphism has codomain matrices; unitarity is supplied by a separate
verified theorem. The specialization of the abstract gauge group U to U(d), with adjoint equal to inverse, is not formalized. The covariant algebra is not a formalization of the full quotient
classification modulo conjugation.

## Outside the formalization

- Minimal-rank and common-range equivalences; K²=nK; effective-rank inequality.
- Infinite-set Hilbert completion and full covariant Kolmogorov construction.
- Full moduli classification of joint (K,u) data, the calibration corollary, and categorical equivalences.
- Frobenius matrix-norm defect theorem and sparse-graph path bound as such.
- Averaging/spectral-projection rounding and its quantitative bound.
- Finite Bochner/Fourier decomposition, determinant, flux and acceptance formulas.
- Haar/Stiefel distributions, concentration, unique weak limit, Morse–Bott
  asymptotics, and the Gamma law.
- All physical and ontological interpretations.

These have ordinary arguments in the article, with selected numerical checks.
No numerical computation is a premise of a Lean theorem. Formal validity does not
establish novelty or empirical adequacy.
