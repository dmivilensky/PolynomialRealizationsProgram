import krylov.Design.Concavity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
Article: main_krylov, thm:B, quantitative mixed extrapolation certificate.
Use: certify an upper bound on the actual objective for every probability measure
from concrete normalized polynomial competitors and their pointwise sensitivity.
Source: KieferWolfowitz60, Kiefer74 and Pukelsheim93, the concave tangent argument.
-/

namespace krylov.Design
noncomputable section
open Set MeasureTheory Polynomial

/-- The scalar concave power lies below its exact tangent at each positive point.
Article: main_krylov, thm:B, including gamma=1.
Proof: import real Bernoulli's inequality and rescale by the positive tangent point. -/
theorem power_tangent {t c γ : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) :
    t ^ γ ≤ (1 - γ) * c ^ γ + γ * c ^ (γ - 1) * t := by
  have hratio : -1 ≤ t / c - 1 := by linarith [div_nonneg ht hc.le]
  have hb := rpow_one_add_le_one_add_mul_self hratio hγ₀ hγ₁
  rw [add_sub_cancel] at hb
  calc
    t ^ γ = c ^ γ * (t / c) ^ γ := by
      rw [Real.div_rpow ht hc.le]
      exact (mul_div_cancel₀ _ (Real.rpow_pos_of_pos hc γ).ne').symm
    _ ≤ c ^ γ * (1 + γ * (t / c - 1)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hc.le γ)
    _ = _ := by rw [Real.rpow_sub_one hc.ne']; field_simp; ring

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]

/-- The concrete sensitivity polynomial, evaluated on the actual spectral space.
Article: main_krylov, thm:B, psi_nu. -/
def sensitivity (M : ℕ) (w : Fin M → ℝ) (γ a : ℝ) (x : C(X, ℝ))
    (ν : ProbabilityMeasure X) (p : ∀ i : Fin M, Competitor (i.val + 1) a) (t : X) : ℝ :=
  ∑ i, w i * (christoffel (i.val + 1) a x ν) ^ (γ - 1) * (p i).val.eval (x t) ^ 2

/-- Integrate the actual sensitivity polynomial term by term.
Article: main_krylov, thm:B. Proof: compact polynomial integrability and finite linearity. -/
theorem integral_sensitivity (M : ℕ) (w : Fin M → ℝ) (γ a : ℝ) (x : C(X, ℝ))
    (ν η : ProbabilityMeasure X) (p : ∀ i : Fin M, Competitor (i.val + 1) a) :
    ∫ t, sensitivity M w γ a x ν p t ∂η =
      ∑ i, w i * (christoffel (i.val + 1) a x ν) ^ (γ - 1) * polynomialEnergy x η (p i).val := by
  unfold sensitivity
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_const_mul _ _
  · intro i _
    exact (continuous_const.mul (((p i).val.continuous.comp x.continuous).pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A pointwise sensitivity bound gives a rigorous global mixed-design certificate.
Article: main_krylov, thm:B, the quantitative upper certificate.
Proof: bound each actual Christoffel infimum by its competitor, apply the real
power tangent, and integrate the sensitivity bound against any competing measure. -/
theorem mixedObjective_certificate (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i)
    {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (a : ℝ) (x : C(X, ℝ))
    (ν : ProbabilityMeasure X) (p : ∀ i : Fin M, Competitor (i.val + 1) a)
    (hpos : ∀ i : Fin M, 0 < christoffel (i.val + 1) a x ν)
    (B : ℝ) (hB : ∀ t, sensitivity M w γ a x ν p t ≤ B)
    (η : ProbabilityMeasure X) :
    mixedObjective M w γ a x η ≤
      mixedObjective M w γ a x ν + γ * (B - mixedObjective M w γ a x ν) := by
  have hterm (i : Fin M) :
      w i * (christoffel (i.val + 1) a x η) ^ γ ≤
        (1 - γ) * (w i * (christoffel (i.val + 1) a x ν) ^ γ) +
        γ * (w i * (christoffel (i.val + 1) a x ν) ^ (γ - 1) *
          polynomialEnergy x η (p i).val) := by
    have ht := power_tangent (christoffel_nonneg (i.val + 1) a x η) (hpos i) hγ₀ hγ₁
    have hc := christoffel_le (i.val + 1) a x η (p i)
    have hcoeff : 0 ≤ γ * (christoffel (i.val + 1) a x ν) ^ (γ - 1) :=
      mul_nonneg hγ₀ (Real.rpow_nonneg (hpos i).le _)
    have hh := mul_le_mul_of_nonneg_left
      (ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc hcoeff))) (hw i)
    convert hh using 1
    ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← integral_sensitivity] at hsum
  have hcont : Continuous (sensitivity M w γ a x ν p) := by
    unfold sensitivity
    fun_prop
  have hint := hcont.integrable_of_hasCompactSupport (μ := (η : Measure X)) (HasCompactSupport.of_compactSpace _)
  have hbound : (∫ t, sensitivity M w γ a x ν p t ∂η) ≤ B := by
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono hint (integrable_const B) hB
  have hh := hsum.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbound hγ₀))
  change mixedObjective M w γ a x η ≤ (1 - γ) * mixedObjective M w γ a x ν + γ * B at hh
  nlinarith only [hh]

/-- The sensitivity inequality is sufficient for global optimality.
Article: main_krylov, thm:B, sufficiency direction of the equivalence criterion.
Proof: set the certified sensitivity bound equal to the candidate objective. -/
theorem mixedObjective_optimal_of_sensitivity (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i)
    {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (a : ℝ) (x : C(X, ℝ))
    (ν : ProbabilityMeasure X) (p : ∀ i : Fin M, Competitor (i.val + 1) a)
    (hpos : ∀ i : Fin M, 0 < christoffel (i.val + 1) a x ν)
    (hB : ∀ t, sensitivity M w γ a x ν p t ≤ mixedObjective M w γ a x ν) :
    ∀ η, mixedObjective M w γ a x η ≤ mixedObjective M w γ a x ν := by
  intro η
  simpa using mixedObjective_certificate M w hw hγ₀ hγ₁ a x ν p hpos _ hB η

end
end krylov.Design
