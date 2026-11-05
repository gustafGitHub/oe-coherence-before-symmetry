import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Coherence before symmetry

Companion to Gustaf Ullman, "Coherence Before Symmetry".
Lean 4.19.0 / mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.

Inner products are conjugate-linear in the first argument. A comparison
`K i j` transports coordinates at j to coordinates at i.

The key assumption is norm preservation of overlaps, NOT their composition.
The latter is proved from the normalized Gram realization.
-/

noncomputable section
open scoped ComplexConjugate ComplexOrder
open InnerProductSpace

namespace CoherentPerspectives

section GramFamily

variable {I E H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A normalized Gram realization. The overlap equation is an adjoint relation;
it contains no assumption of transport composition. -/
structure GramFamily (I E H : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  frame : I → E →ₗᵢ[ℂ] H
  overlap : I → I → E →ₗ[ℂ] E
  gram : ∀ i j x y,
    @inner ℂ _ _ (frame i x) (frame j y) = @inner ℂ _ _ x (overlap i j y)

namespace GramFamily

variable (F : GramFamily I E H)

/-- Losslessness is norm preservation, not a group law. -/
def Lossless (i j : I) : Prop := ∀ x, ‖F.overlap i j x‖ = ‖x‖

/-- The squared residual is the norm lost by an overlap. -/
theorem residual_sq (i j : I) (x : E) :
    ‖F.frame i (F.overlap i j x) - F.frame j x‖ ^ 2 =
      ‖x‖ ^ 2 - ‖F.overlap i j x‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), F.gram, inner_self_eq_norm_sq]
  simp only [LinearIsometry.norm_map]
  ring

/-- Normalized Gram overlaps are contractions. -/
theorem contraction (i j : I) (x : E) : ‖F.overlap i j x‖ ≤ ‖x‖ := by
  have h := F.residual_sq i j x
  have hp := sq_nonneg ‖F.frame i (F.overlap i j x) - F.frame j x‖
  nlinarith [norm_nonneg x, norm_nonneg (F.overlap i j x)]

/-- The squared Hilbert--Schmidt overlap in an orthonormal basis. -/
def coherence {D : Type*} [Fintype D] (e : OrthonormalBasis D ℂ E) (i j : I) : ℝ :=
  ∑ a, ‖F.overlap i j (e a)‖ ^ 2

theorem coherence_le {D : Type*} [Fintype D] (e : OrthonormalBasis D ℂ E)
    (i j : I) : F.coherence e i j ≤ Fintype.card D := by
  calc
    F.coherence e i j ≤ ∑ _a : D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      have h := F.contraction i j (e a)
      rw [e.orthonormal.norm_eq_one] at h
      nlinarith [norm_nonneg (F.overlap i j (e a))]
    _ = Fintype.card D := by simp

/-- Maximal Hilbert--Schmidt coherence implies losslessness on every vector.
Thus the hypothesis of the transport theorem follows from a scalar optimum. -/
theorem lossless_of_maximal_coherence {D : Type*} [Fintype D]
    (e : OrthonormalBasis D ℂ E) (i j : I)
    (hmax : F.coherence e i j = Fintype.card D) : F.Lossless i j := by
  have hsum : ∑ a : D, ‖F.frame i (F.overlap i j (e a)) - F.frame j (e a)‖ ^ 2 = 0 := by
    simp_rw [F.residual_sq, e.orthonormal.norm_eq_one, one_pow]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact sub_eq_zero.mpr hmax.symm
  have hb : ∀ a, F.frame i (F.overlap i j (e a)) = F.frame j (e a) := by
    intro a
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b (_ : b ∈ (Finset.univ : Finset D)) => sq_nonneg
        ‖F.frame i (F.overlap i j (e b)) - F.frame j (e b)‖)).mp hsum a (Finset.mem_univ a)
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  have hmap : (F.frame i).toLinearMap.comp (F.overlap i j) = (F.frame j).toLinearMap :=
    e.toBasis.ext hb
  intro x
  have hx := congrArg (fun f : E →ₗ[ℂ] H => ‖f x‖) hmap
  simpa using hx

/-- A lossless comparison identifies the represented vectors. -/
theorem transport (i j : I) (h : F.Lossless i j) (x : E) :
    F.frame i (F.overlap i j x) = F.frame j x := by
  have hz : ‖F.frame i (F.overlap i j x) - F.frame j x‖ ^ 2 = 0 := by
    rw [F.residual_sq, h, sub_self]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The diagonal overlaps are identities, independently of saturation. -/
theorem diagonal (i : I) : F.overlap i i = LinearMap.id := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [← F.gram]
  exact (F.frame i).inner_map_map x y

/-- Two lossless edges force the composition law; the third edge need not
be assumed lossless. -/
theorem composition (i j k : I) (_hij : F.Lossless i j) (hjk : F.Lossless j k) :
    (F.overlap i j).comp (F.overlap j k) = F.overlap i k := by
  ext x
  apply ext_inner_left ℂ
  intro y
  calc
    @inner ℂ _ _ y (F.overlap i j (F.overlap j k x)) =
        @inner ℂ _ _ (F.frame i y) (F.frame j (F.overlap j k x)) :=
      (F.gram _ _ _ _).symm
    _ = @inner ℂ _ _ (F.frame i y) (F.frame k x) := by rw [F.transport j k hjk]
    _ = @inner ℂ _ _ y (F.overlap i k x) := F.gram _ _ _ _

/-- In fact, losslessness of the second edge alone suffices for this identity. -/
theorem composition_of_right_lossless (i j k : I) (hjk : F.Lossless j k) :
    (F.overlap i j).comp (F.overlap j k) = F.overlap i k := by
  ext x
  apply ext_inner_left ℂ
  intro y
  change @inner ℂ _ _ y (F.overlap i j (F.overlap j k x)) =
    @inner ℂ _ _ y (F.overlap i k x)
  rw [← F.gram, F.transport j k hjk, F.gram]

theorem lossless_trans (i j k : I) (hij : F.Lossless i j) (hjk : F.Lossless j k) :
    F.Lossless i k := by
  intro x
  have h := LinearMap.congr_fun (F.composition i j k hij hjk) x
  change F.overlap i j (F.overlap j k x) = F.overlap i k x at h
  rw [← h, hij, hjk]

/-- A complete saturation hypothesis yields the comparison law directly. -/
theorem maximal_coherence_composition {D : Type*} [Fintype D]
    (e : OrthonormalBasis D ℂ E)
    (hmax : ∀ i j, F.coherence e i j = Fintype.card D) (i j k : I) :
    (F.overlap i j).comp (F.overlap j k) = F.overlap i k :=
  F.composition i j k (F.lossless_of_maximal_coherence e i j (hmax i j))
    (F.lossless_of_maximal_coherence e j k (hmax j k))

/-- Losslessness propagates along any finite chain of lossless comparisons. -/
theorem lossless_of_chain (i j : I) (h : Relation.ReflTransGen F.Lossless i j) :
    F.Lossless i j := by
  have hr : Reflexive F.Lossless := by
    intro a x
    rw [F.diagonal]
    rfl
  have ht : Transitive F.Lossless := by
    intro a b c hab hbc
    exact F.lossless_trans a b c hab hbc
  rw [Relation.reflTransGen_eq_self hr ht] at h
  exact h

/-- Connected saturated comparisons imply global losslessness. The relation
may be the symmetric adjacency relation of an undirected graph. -/
theorem lossless_of_connected_maximal {D : Type*} [Fintype D]
    (e : OrthonormalBasis D ℂ E) (R : I → I → Prop)
    (hconn : ∀ i j, Relation.ReflTransGen R i j)
    (hedge : ∀ i j, R i j → F.coherence e i j = Fintype.card D) :
    ∀ i j, F.Lossless i j := by
  intro i j
  apply F.lossless_of_chain i j
  exact (hconn i j).mono (fun a b hab => F.lossless_of_maximal_coherence e a b (hedge a b hab))

/-- At saturation an overlap has an inverse and is a linear isometry equivalence. -/
def unitary (h : ∀ i j, F.Lossless i j) (i j : I) : E ≃ₗᵢ[ℂ] E where
  toFun := F.overlap i j
  invFun := F.overlap j i
  map_add' := (F.overlap i j).map_add
  map_smul' := (F.overlap i j).map_smul
  norm_map' := h i j
  left_inv x := by
    have hc := LinearMap.congr_fun (F.composition j i j (h j i) (h i j)) x
    simpa [F.diagonal] using hc
  right_inv x := by
    have hc := LinearMap.congr_fun (F.composition i j i (h i j) (h j i)) x
    simpa [F.diagonal] using hc

/-- Reference factorization: no preferred reference is assumed. -/
theorem reference_factorization (h : ∀ i j, F.Lossless i j) (o i j : I) :
    (F.overlap i o).comp (F.overlap o j) = F.overlap i j :=
  F.composition i o j (h i o) (h o j)

/-- Transport around a triangle is the identity. -/
theorem triangle_holonomy (h : ∀ i j, F.Lossless i j) (i j k : I) :
    ((F.overlap i j).comp (F.overlap j k)).comp (F.overlap k i) = LinearMap.id := by
  rw [F.composition i j k (h i j) (h j k),
    F.composition i k i (h i k) (h k i), F.diagonal]

end GramFamily
end GramFamily

section Scalar

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The equality case of Cauchy--Schwarz with the coefficient fixed by the
inner product, rather than merely an existential collinearity witness. -/
theorem saturated_vectors {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ‖@inner ℂ _ _ x y‖ = 1) : y = (@inner ℂ _ _ x y) • x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  obtain ⟨c, _, hc⟩ := (norm_inner_eq_norm_iff (𝕜 := ℂ) hx0 hy0).mp
    (by simpa [hx, hy] using hxy)
  have hcoeff : @inner ℂ _ _ x y = c := by
    rw [hc, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
    simp
  simpa [hcoeff] using hc

/-- Saturated normalized scalar Gram kernels obey composition. -/
theorem scalar_gram_composition (v : I → H) (hn : ∀ i, ‖v i‖ = 1)
    (hs : ∀ i j, ‖@inner ℂ _ _ (v i) (v j)‖ = 1) (i j k : I) :
    @inner ℂ _ _ (v i) (v j) * @inner ℂ _ _ (v j) (v k) = @inner ℂ _ _ (v i) (v k) := by
  conv_rhs => rw [saturated_vectors (hn j) (hn k) (hs j k)]
  rw [inner_smul_right, mul_comm]

end Scalar

section PositiveMatrices

open Matrix
variable {I : Type*} [Fintype I]

/-- Every finite complex positive matrix is realized as a Gram matrix.
This bridges mathlib's `Matrix.PosSemidef` to the scalar theorem. -/
theorem positive_matrix_gram (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    ∃ v : I → EuclideanSpace ℂ I, ∀ i j, K i j = @inner ℂ _ _ (v i) (v j) := by
  obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hK
  let v : I → EuclideanSpace ℂ I := fun i => (WithLp.equiv 2 _).symm (fun r => B r i)
  refine ⟨v, ?_⟩
  intro i j
  rw [hB]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, v,
    EuclideanSpace.inner_piLp_equiv_symm, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro r _
  exact mul_comm _ _

/-- The scalar positive-kernel theorem, with positivity as an actual premise
and no Gram factorization or composition law assumed. -/
theorem positive_saturated_composition (K : Matrix I I ℂ) (hK : K.PosSemidef)
    (hdiag : ∀ i, K i i = 1) (hsat : ∀ i j, ‖K i j‖ = 1) (i j k : I) :
    K i j * K j k = K i k := by
  obtain ⟨v, hv⟩ := positive_matrix_gram K hK
  have hn : ∀ i, ‖v i‖ = 1 := by
    intro i
    have hr : ‖v i‖ ^ 2 = 1 := by
      calc
        ‖v i‖ ^ 2 = RCLike.re (@inner ℂ _ _ (v i) (v i)) :=
          (inner_self_eq_norm_sq (𝕜 := ℂ) (v i)).symm
        _ = 1 := by rw [← hv, hdiag]; rfl
    nlinarith [norm_nonneg (v i)]
  simpa only [← hv] using scalar_gram_composition v hn
    (by intro a b; simpa only [← hv] using hsat a b) i j k

/-- A reference gives phases; changing reference cannot affect the kernel. -/
theorem positive_saturated_factorization (K : Matrix I I ℂ) (hK : K.PosSemidef)
    (hdiag : ∀ i, K i i = 1) (hsat : ∀ i j, ‖K i j‖ = 1) (o : I) :
    ∃ u : I → ℂ, (∀ i, ‖u i‖ = 1) ∧
      ∀ i j, K i j = u i * conj (u j) := by
  refine ⟨fun i => K i o, fun i => hsat i o, ?_⟩
  intro i j
  have hh : conj (K j o) = K o j := hK.isHermitian.apply o j
  rw [hh]
  exact (positive_saturated_composition K hK hdiag hsat i o j).symm

/-- Gauge uniqueness in the scalar case. -/
theorem phase_gauge_unique {I : Type*} (u v : I → ℂ) (o : I)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (h : ∀ i j, u i * conj (u j) = v i * conj (v j)) :
    ∃ q : ℂ, ‖q‖ = 1 ∧ ∀ i, v i = u i * q := by
  refine ⟨conj (u o) * v o, by simp [norm_mul, hu, hv], ?_⟩
  intro i
  have hvv : conj (v o) * v o = 1 := by
    rw [mul_comm, Complex.mul_conj', hv]
    norm_num
  have heq := congrArg (fun z : ℂ => z * v o) (h i o)
  simpa only [mul_assoc, hvv, mul_one] using heq.symm

/-- A saturated positive kernel has trivial scalar loop holonomy. -/
theorem positive_saturated_triangle (K : Matrix I I ℂ) (hK : K.PosSemidef)
    (hdiag : ∀ i, K i i = 1) (hsat : ∀ i j, ‖K i j‖ = 1) (i j k : I) :
    K i j * K j k * K k i = 1 := by
  rw [positive_saturated_composition K hK hdiag hsat i j k,
    positive_saturated_composition K hK hdiag hsat i k i, hdiag]

/-- Every off-diagonal entry has modulus one, but the loop is frustrated. -/
def frustratedTriangle : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 1, -1; 1, 1, 1; -1, 1, 1]

theorem frustratedTriangle_not_positive : ¬ frustratedTriangle.PosSemidef := by
  intro h
  have hd : ∀ i, frustratedTriangle i i = 1 := by
    intro i
    fin_cases i <;> norm_num [frustratedTriangle]
  have hs : ∀ i j, ‖frustratedTriangle i j‖ = 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [frustratedTriangle]
  have hc := positive_saturated_composition frustratedTriangle h hd hs 0 1 2
  change (1 : ℂ) * 1 = -1 at hc
  norm_num at hc

end PositiveMatrices

end CoherentPerspectives
