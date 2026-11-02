import krylov.XR.HermitianNorm

/-!
Article: main_krylov, prop:cert and apH:canon.
Use: prove exact coordinate and pair-rescaling invariance for skew defects;
the older symmetric Loewner argument does not apply to these defects.
Source: invertible Hermitian congruence and the proved strict norm test.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped ComplexOrder Matrix.Norms.L2Operator
variable {p : ℕ}

/-- The conjugate transpose of a complexified real matrix is its true
real transpose. Article: main_krylov, prop:cert. -/
theorem ofReal_conjTranspose (C : Matrix (Fin p) (Fin p) ℝ) :
    (C.map Complex.ofReal)ᴴ=Cᵀ.map Complex.ofReal := by
  ext i j
  simp

/-- The actual Hermitian test is covariant under an arbitrary physical
coefficient congruence. Article: main_krylov, prop:cert. -/
theorem hermitianTest_general_congruence (θ : ℝ) (T D C : Matrix (Fin p) (Fin p) ℝ) :
    (C.map Complex.ofReal)ᴴ*hermitianTest θ T D*C.map Complex.ofReal=
      hermitianTest θ (Cᵀ*T*C) (Cᵀ*D*C) := by
  rw [ofReal_conjTranspose]
  unfold hermitianTest
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    ←ofReal_matrix_mul]

/-- Every invertible coefficient change preserves the original test,
including arbitrary nonorthogonal pair rescalings. Article: prop:cert. -/
theorem hermitianTest_congruence_iff (θ : ℝ) (T D C : Matrix (Fin p) (Fin p) ℝ)
    (hC : IsUnit C.det) :
    (hermitianTest θ (Cᵀ*T*C) (Cᵀ*D*C)).PosDef ↔ (hermitianTest θ T D).PosDef := by
  rw [←hermitianTest_general_congruence]
  have hu : IsUnit (C.map Complex.ofReal) :=
    ((isUnit_iff_isUnit_det C).mpr hC).map Complex.ofRealHom.mapMatrix
  exact hu.posDef_star_left_conjugate_iff

/-- The genuine relative spectral norm of a skew defect is invariant
under every invertible real congruence. Article: main_krylov, apH:canon. -/
theorem relativeBudget_skew_congruence (T D C : Matrix (Fin p) (Fin p) ℝ)
    (hT : T.PosDef) (hD : Dᵀ= -D) (hC : IsUnit C.det) :
    relativeBudget (Cᵀ*T*C) (Cᵀ*D*C)=relativeBudget T D := by
  have hTC : (Cᵀ*T*C).PosDef := by
    have hu := (isUnit_iff_isUnit_det C).mpr hC
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hT.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
  have hDC : (Cᵀ*D*C)ᵀ= -(Cᵀ*D*C) := by
    simp only [transpose_mul,transpose_transpose,hD,Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc]
  have he (θ : ℝ) (hθ : 0<θ) :
      relativeBudget (Cᵀ*T*C) (Cᵀ*D*C)<θ ↔ relativeBudget T D<θ := by
    have hh := hermitianTest_congruence_iff θ T D C hC
    rw [hermitianTest_posDef_iff θ hθ _ _ hTC.isHermitian.isSymm hDC,
      hermitianTest_posDef_iff θ hθ T D hT.isHermitian.isSymm hD] at hh
    simpa only [hTC,hT,true_and] using hh
  have ha : 0≤relativeBudget (Cᵀ*T*C) (Cᵀ*D*C) := norm_nonneg _
  have hb : 0≤relativeBudget T D := norm_nonneg _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · have hm : 0<(relativeBudget (Cᵀ*T*C) (Cᵀ*D*C)+relativeBudget T D)/2 := by linarith
    have hh := (he _ hm).mp (by linarith)
    linarith
  · have hm : 0<(relativeBudget (Cᵀ*T*C) (Cᵀ*D*C)+relativeBudget T D)/2 := by linarith
    have hh := (he _ hm).mpr (by linarith)
    linarith

/-- A fixed diagonal correction preserved by restriction inherits the
same test, as required for the function-value model. Article: prop:cert. -/
theorem hermitianTest_submatrix (θ : ℝ) (T D : Matrix (Fin p) (Fin p) ℝ)
    {q : ℕ} (f : Fin q → Fin p) :
    hermitianTest θ (T.submatrix f f) (D.submatrix f f)=
      (hermitianTest θ T D).submatrix f f := rfl

/-- Every retained subwindow passes whenever the fixed original model
and defect pass. Article: main_krylov, prop:cert, corrected-model clause. -/
theorem hermitianTest_posDef_submatrix (θ : ℝ) (T D : Matrix (Fin p) (Fin p) ℝ)
    {q : ℕ} (f : Fin q → Fin p) (hf : Function.Injective f)
    (hH : (hermitianTest θ T D).PosDef) :
    (hermitianTest θ (T.submatrix f f) (D.submatrix f f)).PosDef := by
  rw [hermitianTest_submatrix]
  exact hH.submatrix hf

end
end krylov.XR
