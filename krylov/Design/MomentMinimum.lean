import krylov.Design.MomentGram

/-!
Article: main_krylov, thm:B, the exact moment-inverse Christoffel formula.
Use: construct the genuine minimizing polynomial for every nonsingular compact
measure, and identify the actual variational infimum with reciprocal c-information.
Source: the classical constrained positive quadratic-form minimization; the
proof completes the square, retaining the original polynomial normalization.
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory Matrix
open scoped BigOperators

/-- The normalized inverse column is the coefficient vector of the c-information minimizer.
Article: main_krylov, thm:B. -/
def normalizedInverseColumn {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (i : n) : n → ℝ :=
  (G⁻¹ i i)⁻¹ • (G⁻¹ *ᵥ Pi.single i 1)

/-- Exact constrained minimum of a positive quadratic form, with its actual attaining vector.
Article: main_krylov, thm:B, the moment-inverse representation.
Proof: the normalized inverse column solves its normal equation; positivity
of the square of the difference supplies the full constrained lower bound. -/
theorem normalizedInverseColumn_minimum {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (hG : G.PosDef) (i : n) :
    let v := normalizedInverseColumn G i
    v i = 1 ∧ v ⬝ᵥ (G *ᵥ v) = (G⁻¹ i i)⁻¹ ∧
      ∀ a : n → ℝ, a i = 1 → (G⁻¹ i i)⁻¹ ≤ a ⬝ᵥ (G *ᵥ a) := by
  let k := G⁻¹ i i
  have hk : 0 < k := hG.inv.diag_pos
  let v := normalizedInverseColumn G i
  have hGe : G *ᵥ (G⁻¹ *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, G.mul_nonsing_inv (G.isUnit_iff_isUnit_det.mp hG.isUnit),
      Matrix.one_mulVec]
  have hGv : G *ᵥ v = k⁻¹ • Pi.single i 1 := by
    dsimp [v, normalizedInverseColumn]
    rw [Matrix.mulVec_smul, hGe]
  have hvi : v i = 1 := by
    dsimp [v, normalizedInverseColumn]
    rw [Matrix.mulVec_single_one]
    change k⁻¹ * k = 1
    exact inv_mul_cancel₀ hk.ne'
  have hvv : v ⬝ᵥ (G *ᵥ v) = k⁻¹ := by
    rw [hGv, dotProduct_smul, dotProduct_single, hvi]
    simp
  refine ⟨hvi, hvv, ?_⟩
  intro a hai
  have hcross : a ⬝ᵥ (G *ᵥ v) = k⁻¹ := by
    rw [hGv, dotProduct_smul, dotProduct_single, hai]
    simp
  have hsym : v ⬝ᵥ (G *ᵥ a) = a ⬝ᵥ (G *ᵥ v) := by
    have hGt : Gᵀ = G := Matrix.isHermitian_iff_isSymm.mp hG.isHermitian
    simpa only [hGt] using Matrix.dotProduct_transpose_mulVec G v a
  have hn := hG.posSemidef.dotProduct_mulVec_nonneg (a - v)
  rw [star_trivial, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, hsym, hcross, hvv] at hn
  linarith

/-- The actual moment minimizer polynomial, expressed by its normalized inverse-moment column.
Article: main_krylov, thm:B, p_m. -/
def momentPolynomial (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) : ℝ[X] :=
  Polynomial.ofFn (m + 1) (normalizedInverseColumn (momentGram I m ν) 0)

/-- The constructed inverse-moment polynomial is admissible in the original extrapolation problem.
Article: main_krylov, thm:B. -/
theorem momentPolynomial_admissible (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) (hG : (momentGram I m ν).PosDef) :
    (momentPolynomial I m ν).natDegree ≤ m ∧ (momentPolynomial I m ν).eval 0 = 1 := by
  constructor
  · exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
  · rw [momentPolynomial, ← coeff_zero_eq_eval_zero,
      Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.succ_pos m)]
    exact (normalizedInverseColumn_minimum (momentGram I m ν) hG 0).1

/-- The actual inverse-moment minimizer has the reciprocal diagonal energy.
Article: main_krylov, thm:B. -/
theorem polynomialEnergy_momentPolynomial (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) (hG : (momentGram I m ν).PosDef) :
    polynomialEnergy (spectralCoordinate I) ν (momentPolynomial I m ν) =
      ((momentGram I m ν)⁻¹ 0 0)⁻¹ := by
  rw [momentPolynomial, polynomialEnergy_eq_momentGram]
  exact (normalizedInverseColumn_minimum (momentGram I m ν) hG 0).2.1

/-- The actual Christoffel variational criterion is the reciprocal inverse-moment diagonal.
Article: main_krylov, thm:B, lambda_m=(c^T M_m^-1 c)^-1.
Proof: the explicit admissible polynomial gives the upper bound; every genuine
competitor is recovered from its finite coefficients and obeys the constrained quadratic lower bound. -/
theorem christoffel_eq_moment_inverse (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) (hG : (momentGram I m ν).PosDef) :
    christoffel m 0 (spectralCoordinate I) ν = ((momentGram I m ν)⁻¹ 0 0)⁻¹ := by
  apply le_antisymm
  · let p : Competitor m 0 := ⟨momentPolynomial I m ν, momentPolynomial_admissible I m ν hG⟩
    exact (christoffel_le m 0 (spectralCoordinate I) ν p).trans_eq
      (polynomialEnergy_momentPolynomial I m ν hG)
  · apply le_ciInf
    intro p
    let a := Polynomial.toFn (m + 1) p.val
    have he : Polynomial.ofFn (m + 1) a = p.val :=
      Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le p.property.1)
    have ha : a 0 = 1 := by
      change p.val.coeff 0 = 1
      simpa only [coeff_zero_eq_eval_zero] using p.property.2
    rw [← he, polynomialEnergy_eq_momentGram]
    exact (normalizedInverseColumn_minimum (momentGram I m ν) hG 0).2.2 a ha

/-- The genuine minimizing polynomial attains the original variational information.
Article: main_krylov, thm:B, existence of the sensitivity polynomials on the nonsingular domain. -/
theorem momentPolynomial_attains (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) (hG : (momentGram I m ν).PosDef) :
    polynomialEnergy (spectralCoordinate I) ν (momentPolynomial I m ν) =
      christoffel m 0 (spectralCoordinate I) ν := by
  rw [polynomialEnergy_momentPolynomial I m ν hG, christoffel_eq_moment_inverse I m ν hG]

end
end krylov.Design
