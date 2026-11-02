import krylov.Design.Equivalence

/-!
Article: main_krylov, thm:B, atomic optimizer support.
Use: show that the actual sensitivity certificate confines every nonsingular
optimizer to finitely many actual roots, with no assumed atomic representation.
Source: the classical polynomial equivalence-theorem support argument.
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory Matrix Set
open scoped BigOperators

/-- Every positive-degree physical Christoffel criterion is strictly smaller than one.
Article: main_krylov, thm:B.
Proof: degree monotonicity and the strictly contracting first Chebyshev residual. -/
theorem interval_christoffel_lt_one (I : chebyshev1.SpectralInterval) {m : ℕ} (hm : 1 ≤ m)
    (ν : ProbabilityMeasure (Spectrum I)) : christoffel m 0 (spectralCoordinate I) ν < 1 := by
  have hepos := chebyshev_scale_pos I 1
  have helt : I.epsilon 1 < 1 := by
    rw [chebyshev1.SpectralInterval.epsilon, I.den_one]
    exact (div_lt_one (lt_trans zero_lt_one I.eta_gt_one)).mpr I.eta_gt_one
  have hb := (christoffel_antitone_degree hm 0 (spectralCoordinate I) ν).trans
    (christoffel_le_chebyshev I 1 ν)
  nlinarith

/-- The actual sensitivity as a polynomial in the physical spectral coordinate.
Article: main_krylov, thm:B. -/
def sensitivityPolynomial (I : chebyshev1.SpectralInterval) (M : ℕ) (w : Fin M → ℝ)
    (γ : ℝ) (ν : ProbabilityMeasure (Spectrum I)) (p : ∀ i : Fin M, Competitor (i.val + 1) 0) : ℝ[X] :=
  ∑ i, C (w i * (christoffel (i.val + 1) 0 (spectralCoordinate I) ν) ^ (γ - 1)) * (p i).val ^ 2

/-- Polynomial evaluation gives exactly the actual sensitivity function.
Article: main_krylov, thm:B. -/
theorem eval_sensitivityPolynomial (I : chebyshev1.SpectralInterval) (M : ℕ) (w : Fin M → ℝ)
    (γ : ℝ) (ν : ProbabilityMeasure (Spectrum I)) (p : ∀ i : Fin M, Competitor (i.val + 1) 0)
    (t : Spectrum I) :
    (sensitivityPolynomial I M w γ ν p).eval t.val = sensitivity M w γ 0 (spectralCoordinate I) ν p t := by
  simp only [sensitivityPolynomial, sensitivity, eval_finsetSum, eval_mul, eval_C, eval_pow]
  rfl

/-- Positive weight makes the mixed objective strictly smaller than the sum of its weights.
Article: main_krylov, thm:B. -/
theorem intervalObjective_lt_weight_sum (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ : 0 < γ)
    (ν : ProbabilityMeasure (Spectrum I)) (j : Fin M) (hj : 0 < w j) :
    intervalObjective I M w γ ν < ∑ i, w i := by
  have hi (i : Fin M) : (christoffel (i.val + 1) 0 (spectralCoordinate I) ν) ^ γ < 1 :=
    Real.rpow_lt_one (christoffel_nonneg _ _ _ _) (interval_christoffel_lt_one I (by omega) ν) hγ
  unfold intervalObjective mixedObjective
  apply Finset.sum_lt_sum
  · intro i _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hi i).le (hw i)
  · exact ⟨j, Finset.mem_univ j, by simpa only [mul_one] using mul_lt_mul_of_pos_left (hi j) hj⟩

/-- The certificate gap polynomial is genuinely nonzero, as witnessed at the original exterior point.
Article: main_krylov, thm:B.
Proof: its value at zero dominates the weight sum, which strictly exceeds the actual objective. -/
theorem sensitivity_gapPolynomial_ne_zero (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (ν : ProbabilityMeasure (Spectrum I)) (p : ∀ i : Fin M, Competitor (i.val + 1) 0)
    (hpos : ∀ i : Fin M, 0 < christoffel (i.val + 1) 0 (spectralCoordinate I) ν)
    (j : Fin M) (hj : 0 < w j) :
    sensitivityPolynomial I M w γ ν p - C (intervalObjective I M w γ ν) ≠ 0 := by
  have hb : (∑ i, w i) ≤ (sensitivityPolynomial I M w γ ν p).eval 0 := by
    simp only [sensitivityPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow]
    apply Finset.sum_le_sum
    intro i _
    rw [(p i).property.2, one_pow, mul_one]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hpos i) (christoffel_le_one _ _ _ _) (by linarith)) (hw i)
  have hlt := intervalObjective_lt_weight_sum I M w hw hγ₀ ν j hj
  intro hz
  have he := congrArg (fun P : ℝ[X] => P.eval 0) hz
  simp only [eval_sub, eval_C, eval_zero] at he
  linarith

/-- Every nonsingular optimizer has finite actual topological support.
Article: main_krylov, thm:B, atomic support without an assumed atomic model.
Proof: the necessary tight certificate puts the actual support inside the roots
of a nonzero real polynomial, hence inside a finite set. -/
theorem optimal_interval_support_finite (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (ν : ProbabilityMeasure (Spectrum I))
    (hG : ∀ i : Fin M, (momentGram I (i.val + 1) ν).PosDef)
    (hopt : ∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν)
    (j : Fin M) (hj : 0 < w j) : (ν : Measure (Spectrum I)).support.Finite := by
  let p := momentCompetitors I M ν hG
  have hpos (i : Fin M) : 0 < christoffel (i.val + 1) 0 (spectralCoordinate I) ν := by
    rw [christoffel_eq_moment_inverse I _ ν (hG i)]
    exact inv_pos.mpr (hG i).inv.diag_pos
  let P := sensitivityPolynomial I M w γ ν p - C (intervalObjective I M w γ ν)
  have hP : P ≠ 0 := sensitivity_gapPolynomial_ne_zero I M w hw hγ₀ hγ₁ ν p hpos j hj
  have hf : {t : Spectrum I | P.IsRoot t.val}.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn (Polynomial.finite_setOfPred_isRoot hP)
  apply hf.subset
  intro t ht
  have hs := sensitivity_eq_on_support_of_certificate M w hw γ 0 (spectralCoordinate I) ν p hpos
    (sensitivity_le_of_optimal_interval I M w hγ₀ ν hG hopt) t ht
  change P.eval t.val = 0
  simp only [P, eval_sub, eval_C, eval_sensitivityPolynomial]
  exact sub_eq_zero.mpr hs

end
end krylov.Design
