import krylov.XR.SkewTestNorm
import krylov.Secant.Metric

/-!
Article: main_krylov, prop:cert, the complete metric equivalence.
Use: the original observed complex test is equivalent to positivity of
the real model and a strict bound on its genuine relative skew norm.
Source: positive-root congruence and the proved sharp real skew criterion.
-/

/-!
Article: krylov, Proposition F.2 [prop:cert].

The real-model/skew-norm test is equivalent to actual complex Hermitian positivity, inherited
by ordered restrictions. Reversed Cholesky produces exactly the longest positive chronological
suffix.
The generic empty suffix is allowed; actual stored positive secants ensure the one-pair suffix
and justify the clamp in the printed algorithm.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder
variable {p : ℕ}

/-- The true complex test for a supplied real model and skew defect.
Article: main_krylov, prop:cert. -/
def hermitianTest (θ : ℝ) (T D : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℂ :=
  T.map Complex.ofReal+Complex.I • (θ⁻¹ • D).map Complex.ofReal

/-- Complexification preserves actual finite matrix products.
Article: main_krylov, prop:cert. -/
theorem ofReal_matrix_mul (A B : Matrix (Fin p) (Fin p) ℝ) :
    (A*B).map Complex.ofReal=A.map Complex.ofReal*B.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- Real metric congruence commutes with the actual complex test.
Article: main_krylov, prop:cert. -/
theorem hermitianTest_congruence (θ : ℝ) (T D A : Matrix (Fin p) (Fin p) ℝ) :
    A.map Complex.ofReal*hermitianTest θ T D*A.map Complex.ofReal=
      hermitianTest θ (A*T*A) (A*D*A) := by
  unfold hermitianTest
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    ←ofReal_matrix_mul]

/-- The original Hermitian test restricted to real vectors is precisely
the real model quadratic form. Article: main_krylov, prop:cert. -/
theorem hermitianTest_real_form (θ : ℝ) (T D : Matrix (Fin p) (Fin p) ℝ)
    (x : Fin p → ℝ) :
    (star (complexVector x 0) ⬝ᵥ (hermitianTest θ T D*ᵥ complexVector x 0)).re=
      x ⬝ᵥ (T*ᵥ x) := by
  unfold hermitianTest
  rw [hermitian_pair_quadratic_re]
  simp

/-- Passing the complex test forces actual real-model positivity.
Article: main_krylov, prop:cert. -/
theorem posDef_of_hermitianTest (θ : ℝ) (T D : Matrix (Fin p) (Fin p) ℝ)
    (hT : T.IsSymm) (hH : (hermitianTest θ T D).PosDef) : T.PosDef := by
  have hs : T.IsHermitian := by
    simpa only [IsHermitian,conjTranspose_eq_transpose_of_trivial] using hT.eq
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro x hx
  have hn := complexVector_ne_zero_iff x 0 |>.mpr (Or.inl hx)
  have hh := hH.re_dotProduct_pos hn
  change 0<(star (complexVector x 0) ⬝ᵥ (hermitianTest θ T D*ᵥ complexVector x 0)).re at hh
  rw [hermitianTest_real_form] at hh
  simpa only [star_trivial] using hh

/-- Real positive-root normalization preserves the skew character of
the actual observed defect. Article: main_krylov, prop:cert. -/
theorem relativeOperator_skew (T D : Matrix (Fin p) (Fin p) ℝ) (hD : Dᵀ= -D) :
    (relativeOperator T D)ᵀ= -relativeOperator T D := by
  simp only [relativeOperator,transpose_mul,transpose_nonsing_inv,
    (metricRoot_isSymm T).eq,hD,Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc]

/-- Positive-root whitening of the test is exact on its genuine
invertible domain. Article: main_krylov, prop:cert. -/
theorem hermitianTest_whiten (θ : ℝ) (T D : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef) :
    ((hermitianTest θ T D).PosDef ↔
      (1+Complex.I • (relativeOperator T (θ⁻¹ • D)).map Complex.ofReal).PosDef) := by
  let A := (metricRoot T)⁻¹
  have hs : A.IsSymm := by
    simp only [A,IsSymm,transpose_nonsing_inv,(metricRoot_isSymm T).eq]
  have hu : IsUnit (A.map Complex.ofReal) := by
    have hr : IsUnit (metricRoot T) := (isUnit_iff_isUnit_det _).mpr (metricRoot_det_unit T hT)
    exact (Matrix.isUnit_nonsing_inv_iff.mpr hr).map Complex.ofRealHom.mapMatrix
  have hc := hu.posDef_star_left_conjugate_iff (x := hermitianTest θ T D)
  have he : star (A.map Complex.ofReal)*hermitianTest θ T D*A.map Complex.ofReal=
      1+Complex.I • (relativeOperator T (θ⁻¹ • D)).map Complex.ofReal := by
    rw [star_eq_conjTranspose,(ofReal_isHermitian A hs).eq,hermitianTest_congruence]
    change hermitianTest θ (relativeOperator T T) (relativeOperator T D)=_
    rw [relativeOperator_base T hT]
    unfold hermitianTest
    rw [relativeOperator_smul]
    congr 1
    ext i j
    by_cases hij : i=j
    · subst j
      simp
    · simp [hij]
  rw [he] at hc
  exact hc.symm

/-- Complete exact equivalence between complex positivity and the
article's actual strict relative spectral bound. Article: prop:cert. -/
theorem hermitianTest_posDef_iff (θ : ℝ) (hθ : 0<θ)
    (T D : Matrix (Fin p) (Fin p) ℝ) (hT : T.IsSymm) (hD : Dᵀ= -D) :
    (hermitianTest θ T D).PosDef ↔ T.PosDef ∧ relativeBudget T D<θ := by
  have hsk : (relativeOperator T (θ⁻¹ • D))ᵀ= -relativeOperator T (θ⁻¹ • D) := by
    apply relativeOperator_skew
    simp only [transpose_smul,hD,smul_neg]
  have hn : ‖relativeOperator T (θ⁻¹ • D)‖=relativeBudget T D/θ := by
    rw [relativeOperator_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hθ)]
    change θ⁻¹*‖relativeOperator T D‖=‖relativeOperator T D‖/θ
    rw [div_eq_mul_inv,mul_comm]
  constructor
  · intro hH
    have hp := posDef_of_hermitianTest θ T D hT hH
    refine ⟨hp,?_⟩
    have hh := (normalized_skew_posDef_iff _ hsk).mp ((hermitianTest_whiten θ T D hp).mp hH)
    rw [hn,div_lt_one hθ] at hh
    exact hh
  · rintro ⟨hp,hnorm⟩
    apply (hermitianTest_whiten θ T D hp).mpr
    apply (normalized_skew_posDef_iff _ hsk).mpr
    rw [hn,div_lt_one hθ]
    exact hnorm

/-- The actual chronological observed test equals the general real-model
test; division and scalar-multiplication conventions agree exactly.
Article: main_krylov, prop:cert. -/
theorem hermitianWindowMatrix_eq (θ : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) :
    hermitianWindowMatrix θ M=hermitianTest θ (latest M) (defect M) := by
  ext i j
  simp only [hermitianWindowMatrix,hermitianTest,Matrix.add_apply,Matrix.smul_apply,
    Matrix.map_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_inv]
  ring

/-- The source's Hermitian predicate is precisely its original real
positive-model and relative-defect definition. Article: prop:cert. -/
theorem windowUnrefuted_iff (θ : ℝ) (hθ : 0<θ) (M : Matrix (Fin p) (Fin p) ℝ) :
    windowUnrefuted θ M ↔ (latest M).PosDef ∧ relativeBudget (latest M) (defect M)<θ := by
  rw [windowUnrefuted,hermitianWindowMatrix_eq]
  exact hermitianTest_posDef_iff θ hθ _ _ (latest_isSymm M) (defect_transpose M)

end
end krylov.XR
