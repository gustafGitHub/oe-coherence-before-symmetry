import CoherentPerspectives

/-! Extensions: finite block positivity, homogeneous representations,
vector defect bounds, and the algebraic core of equivariant descent. -/
noncomputable section
open scoped ComplexConjugate ComplexOrder
open InnerProductSpace Matrix
set_option maxHeartbeats 800000
namespace CoherentPerspectives
section Block
variable {I D : Type*} [Fintype I] [Fintype D] [DecidableEq D]

/-- A block with matrix, rather than pointwise, multiplication. -/
def kernelBlock (K : Matrix (I × D) (I × D) ℂ) (i j : I) : Matrix D D ℂ :=
  Matrix.of (fun a b => K (i,a) (j,b))

/-- Positive block matrices with identity diagonal blocks have isometric
Gram realizations with exactly the prescribed overlap matrices. -/
theorem positive_block_gram (K : Matrix (I × D) (I × D) ℂ)
    (hK : K.PosSemidef)
    (hd : ∀ i a b, K (i,a) (i,b) = if a = b then 1 else 0) :
    ∃ F : GramFamily I (EuclideanSpace ℂ D) (EuclideanSpace ℂ (I × D)),
      ∀ i j, LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun D ℂ)
        (F.overlap i j) = fun a b => K (i,a) (j,b) := by
  classical
  obtain ⟨v, hv⟩ := positive_matrix_gram K hK
  let e := EuclideanSpace.basisFun D ℂ
  let f (i : I) := e.toBasis.constr ℂ (fun a => v (i,a))
  have he (i : I) (a : D) : f i (e a) = v (i,a) :=
    e.toBasis.constr_basis ℂ (fun a => v (i,a)) a
  have hf (i : I) : Orthonormal ℂ (f i ∘ e.toBasis) := by
    apply orthonormal_iff_ite.mpr
    intro a b
    change @inner ℂ _ _ (f i (e a)) (f i (e b)) = _
    rw [he, he, ← hv]
    exact hd i a b
  let V (i : I) := (f i).isometryOfOrthonormal (v := e.toBasis) e.orthonormal (hf i)
  let F : GramFamily I (EuclideanSpace ℂ D) (EuclideanSpace ℂ (I × D)) :=
    { frame := V
      overlap := fun i j => (LinearMap.adjoint (f i)).comp (f j)
      gram := fun i j x y => (LinearMap.adjoint_inner_right (f i) x (f j y)).symm }
  refine ⟨F, ?_⟩
  intro i j
  ext a b
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  change @inner ℂ _ _ (e a) (LinearMap.adjoint (f i) (f j (e b))) = _
  rw [LinearMap.adjoint_inner_right, he, he]
  exact (hv (i,a) (j,b)).symm

/-- Composition directly from positive block data and maximal Frobenius overlap. -/
theorem positive_block_saturated_composition
    (K : Matrix (I × D) (I × D) ℂ) (hK : K.PosSemidef)
    (hd : ∀ i a b, K (i,a) (i,b) = if a = b then 1 else 0)
    (hs : ∀ i j, ∑ b : D, ∑ a : D, ‖K (i,a) (j,b)‖ ^ 2 = Fintype.card D)
    (i j k : I) : kernelBlock K i j * kernelBlock K j k = kernelBlock K i k := by
  obtain ⟨F, hF⟩ := positive_block_gram K hK hd
  let e := EuclideanSpace.basisFun D ℂ
  have hmax : ∀ a b, F.coherence e a b = Fintype.card D := by
    intro a b
    unfold GramFamily.coherence
    calc
      (∑ y : D, ‖F.overlap a b (e y)‖ ^ 2) =
          ∑ y : D, ∑ x : D, ‖@inner ℂ _ _ (e x) (F.overlap a b (e y))‖ ^ 2 := by
        simp only [e.sum_sq_norm_inner]
      _ = ∑ y : D, ∑ x : D, ‖K (a,x) (b,y)‖ ^ 2 := by
        simp_rw [← LinearMap.toMatrixOrthonormal_apply_apply]
        simp only [e, hF]
      _ = Fintype.card D := hs a b
  have hc := F.maximal_coherence_composition e hmax i j k
  have hm := congrArg (LinearMap.toMatrixOrthonormal e) hc
  dsimp only [e] at hm
  simpa only [← Module.End.mul_eq_comp, map_mul, hF, kernelBlock, Matrix.of_apply] using hm

/-- The overlap matrices have two-sided unitary inverses. -/
theorem positive_block_unitary
    (K : Matrix (I × D) (I × D) ℂ) (hK : K.PosSemidef)
    (hd : ∀ i a b, K (i,a) (i,b) = if a = b then 1 else 0)
    (hs : ∀ i j, ∑ b : D, ∑ a : D, ‖K (i,a) (j,b)‖ ^ 2 = Fintype.card D)
    (i j : I) :
    let B : Matrix D D ℂ := kernelBlock K i j
    B.conjTranspose * B = 1 ∧ B * B.conjTranspose = 1 := by
  have hr : (kernelBlock K i j).conjTranspose = kernelBlock K j i := by
    ext a b
    exact hK.isHermitian.apply (j,a) (i,b)
  have hi (i : I) : kernelBlock K i i = (1 : Matrix D D ℂ) := by
    ext a b
    simp only [kernelBlock, Matrix.of_apply, hd, Matrix.one_apply]
  dsimp only
  rw [hr]
  exact ⟨(positive_block_saturated_composition K hK hd hs j i j).trans (hi j),
    (positive_block_saturated_composition K hK hd hs i j i).trans (hi i)⟩

/-- Homogeneous multiplication directly from finite block positivity. -/
theorem positive_homogeneous_multiplicative {G : Type*} [Group G] [Fintype G]
    (φ : G → Matrix D D ℂ)
    (hp : Matrix.PosSemidef (fun (x y : G × D) => φ (x.1⁻¹ * y.1) x.2 y.2))
    (h1 : φ 1 = 1)
    (hs : ∀ g, ∑ b : D, ∑ a : D, ‖φ g a b‖ ^ 2 = Fintype.card D)
    (a b : G) : φ a * φ b = φ (a*b) := by
  have hd : ∀ (g : G) (x y : D), φ (g⁻¹*g) x y = if x=y then 1 else 0 := by
    intro g x y
    simp only [inv_mul_cancel, h1, Matrix.one_apply]
  have hc := positive_block_saturated_composition
    (fun (x y : G × D) => φ (x.1⁻¹*y.1) x.2 y.2) hp hd
    (fun g h => hs (g⁻¹*h)) 1 a (a*b)
  simpa only [kernelBlock, Matrix.of_apply, inv_one, one_mul, inv_mul_cancel_left] using hc

/-- The reconstructed bundled matrix homomorphism. -/
def homogeneousMatrixHom {G : Type*} [Group G] [Fintype G]
    (φ : G → Matrix D D ℂ)
    (hp : Matrix.PosSemidef (fun (x y : G × D) => φ (x.1⁻¹ * y.1) x.2 y.2))
    (h1 : φ 1 = 1)
    (hs : ∀ g, ∑ b : D, ∑ a : D, ‖φ g a b‖ ^ 2 = Fintype.card D) :
    G →* Matrix D D ℂ where
  toFun := φ
  map_one' := h1
  map_mul' a b := (positive_homogeneous_multiplicative φ hp h1 hs a b).symm

/-- Each value of the homogeneous homomorphism is unitary. -/
theorem positive_homogeneous_unitary {G : Type*} [Group G] [Fintype G]
    (φ : G → Matrix D D ℂ)
    (hp : Matrix.PosSemidef (fun (x y : G × D) => φ (x.1⁻¹ * y.1) x.2 y.2))
    (h1 : φ 1 = 1)
    (hs : ∀ g, ∑ b : D, ∑ a : D, ‖φ g a b‖ ^ 2 = Fintype.card D)
    (g : G) : (φ g).conjTranspose * φ g = 1 ∧ φ g * (φ g).conjTranspose = 1 := by
  have hd : ∀ (g : G) (x y : D), φ (g⁻¹*g) x y = if x=y then 1 else 0 := by
    intro g x y
    simp only [inv_mul_cancel, h1, Matrix.one_apply]
  have h := positive_block_unitary
    (fun (x y : G × D) => φ (x.1⁻¹*y.1) x.2 y.2) hp hd
    (fun g h => hs (g⁻¹*h)) 1 g
  simpa only [kernelBlock, Matrix.of_apply, inv_one, one_mul] using h
end Block

section Defect
variable {I E H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem GramFamily.vector_defect_bound (F : GramFamily I E H)
    (i j k : I) (x y : E) :
    ‖@inner ℂ _ _ y (F.overlap i k x - F.overlap i j (F.overlap j k x))‖ ^ 2 ≤
      (‖y‖ ^ 2 - ‖F.overlap j i y‖ ^ 2) *
      (‖x‖ ^ 2 - ‖F.overlap j k x‖ ^ 2) := by
  let a := F.frame j (F.overlap j i y) - F.frame i y
  let b := F.frame j (F.overlap j k x) - F.frame k x
  have he : @inner ℂ _ _ a b =
      @inner ℂ _ _ y (F.overlap i k x - F.overlap i j (F.overlap j k x)) := by
    dsimp [a, b]
    simp only [inner_sub_left, inner_sub_right, (F.frame j).inner_map_map, F.gram]
    ring
  rw [← F.residual_sq j i y, ← F.residual_sq j k x, ← he]
  change ‖@inner ℂ _ _ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2
  have h := norm_inner_le_norm (𝕜 := ℂ) a b
  nlinarith [norm_nonneg (@inner ℂ _ _ a b), norm_nonneg a, norm_nonneg b]
end Defect

section Homogeneous
variable {G E H : Type*} [Group G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem homogeneous_multiplicative (F : GramFamily G E H)
    (φ : G → E →ₗ[ℂ] E)
    (hh : ∀ g h, F.overlap g h = φ (g⁻¹ * h))
    (hl : ∀ g h, F.Lossless g h) (a b : G) :
    (φ a).comp (φ b) = φ (a * b) := by
  have hc := F.composition 1 a (a*b) (hl 1 a) (hl a (a*b))
  simpa only [hh, inv_one, one_mul, inv_mul_cancel_left] using hc
end Homogeneous

section Covariance
variable {G I U : Type*} [Group G] [Group U] [MulAction G I]
theorem pure_gauge_trivialization (v : I → U) (i j : I) :
    (v i)⁻¹ * (v i * (v j)⁻¹) * v j = 1 := by group

theorem gauge_cocycle (u : G → I → U)
    (hu : ∀ g h i, u (g*h) i = u g (h • i) * u h i)
    (q : I → U) (g h : G) (i : I) :
    (q ((g*h) • i))⁻¹ * u (g*h) i * q i =
      ((q (g • (h • i)))⁻¹ * u g (h • i) * q (h • i)) *
      ((q (h • i))⁻¹ * u h i * q i) := by
  rw [hu, MulAction.mul_smul]
  group

omit [Group G] [MulAction G I] in
/-- Identity-kernel covariance makes the residual cocycle constant. -/
theorem constant_of_identity_covariance (u : G → I → U)
    (hc : ∀ g i j, u g i * (u g j)⁻¹ = 1) (g : G) (i j : I) :
    u g i = u g j := mul_inv_eq_one.mp (hc g i j)

def descendedCocycleHom (u : G → I → U)
    (hu : ∀ g h i, u (g*h) i = u g (h • i) * u h i)
    (h1 : ∀ i, u 1 i = 1)
    (hc : ∀ g i j, u g i * (u g j)⁻¹ = 1) (o : I) : G →* U where
  toFun := fun g => u g o
  map_one' := h1 o
  map_mul' g h := by
    rw [hu, constant_of_identity_covariance u hc g (h • o) o]
end Covariance
end CoherentPerspectives
