import krylov.Asymptotics.StringUpperBound
import krylov.Asymptotics.FeedbackGraphs
import krylov.Strings.DiscreteAffine
import krylov.Design.InfinitePowers
import krylov.Design.DegenerateWeights

/-!
Article: main_krylov, thm:limit, sharp finite-kappa design upper bound.
Use: transfer the actual finite-string bound to the original all-measures
finite and infinite design optima. The reverse spectral dictionary and
prescribed-atom supremum equality are proved inputs, not certificates.
Source: positive affine spectral normalization, the full constructive
Stieltjes dictionary and the proved consecutive-step cancellation.
-/

namespace krylov.Asymptotics
noncomputable section
open Real Set MeasureTheory Finset
open krylov.Design krylov.Strings krylov.ContinuumControl jacobi.Finite
open scoped BigOperators

/-- The literal four-term upper bound from the article. -/
def finiteDesignUpper (I : chebyshev1.SpectralInterval) (γ B : ℝ) (σ : ℝ → ℝ) : ℝ :=
  sqrt (I.kappa - 1) * feedbackValue γ σ 1 / 2 + (1 + B) / 4 * log I.kappa +
    1 / 2 + (1 + 2 * B) / (4 * γ)

/-- An arbitrary actual prescribed finite design has an actual positive
string in the source spectral coordinate and exactly the same objective. -/
theorem atomic_design_upper (I : chebyshev1.SpectralInterval) (M : ℕ)
    {γ B : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hlog : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B)
    (Q : AtomicIntervalDesign I (M + 1)) :
    atomicDesignObjective I M (fun _ ↦ 1) γ Q ≤ finiteDesignUpper I γ B σ := by
  let T := DiscreteInverse.normalizedMeasure Q.val I.mu I.mu_pos
  have hnodes (i : Fin (M + 1)) : 0 ≤ T.node i ∧ T.node i ≤ I.kappa - 1 := by
    rw [show T.node i = Q.val.node i / I.mu - 1 from
      DiscreteInverse.normalizedMeasure_node Q.val I.mu I.mu_pos i]
    constructor
    · have hh : 1 ≤ Q.val.node i / I.mu := (le_div_iff₀ I.mu_pos).2
        (by simpa only [one_mul] using (Q.property i).1)
      linarith
    · exact sub_le_sub_right ((div_le_div_iff_of_pos_right I.mu_pos).2 (Q.property i).2) 1
  obtain ⟨S, hnorm, hkernel, _⟩ := DiscreteInverse.exists_string T (fun i ↦ (hnodes i).1)
  have hR : S.spectralRadius ≤ I.kappa - 1 := by
    obtain ⟨i, hi⟩ := hnorm.1
    rw [← hi]
    exact (hnodes i).2
  have hb := DiscreteString.sharp_upper_of_spectralRadius_le S hγ hB hR hgraph hlog
  have he : atomicDesignObjective I M (fun _ ↦ 1) γ Q =
      ∑ j ∈ range M, S.K (j + 1) ^ (-γ) := by
    unfold atomicDesignObjective intervalObjective mixedObjective
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    rw [one_mul, interval_christoffel_atomic I Q.val Q.property (by omega),
      ← DiscreteInverse.christoffelKernel_normalized Q.val I.mu I.mu_pos,
      hkernel (i.val + 1) (by omega), ← Real.rpow_neg_eq_inv_rpow]
  rw [he]
  simpa only [finiteDesignUpper, add_sub_cancel] using hb

/-- The exact source upper bound holds for every original finite
all-probability-measures optimum and every source exponent. -/
theorem optimalValue_sharp_upper (I : chebyshev1.SpectralInterval) (M : ℕ)
    {γ B : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hB : 0 ≤ B)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hlog : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B) :
    optimalValue I M (fun _ ↦ 1) γ ≤ finiteDesignUpper I γ B σ := by
  rw [← atomicDesignValue_eq_optimalValue_all I M (M + 1) le_rfl
    (fun _ ↦ 1) (fun _ ↦ zero_le_one) hγ hγ₁]
  let ⟨Q⟩ := exists_atomicIntervalDesign I (M + 1) (Nat.succ_pos M)
  apply csSup_le (show (Set.range (atomicDesignObjective I M (fun _ ↦ 1) γ (N := M + 1))).Nonempty from
    ⟨_, Q, rfl⟩)
  rintro _ ⟨Q', rfl⟩
  exact atomic_design_upper I M hγ hB hgraph hlog Q'

/-- The very same bound holds for the genuine optimized infinite
criterion, by its proved equality with the supremum of finite optima. -/
theorem infinitePowerValue_sharp_upper (I : chebyshev1.SpectralInterval)
    {γ B : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hB : 0 ≤ B)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hlog : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B) :
    infinitePowerValue I γ ≤ finiteDesignUpper I γ B σ := by
  rw [infinitePowerValue_eq_finite_supremum I hγ]
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨M, rfl⟩
  exact optimalValue_sharp_upper I M hγ hγ₁ hB hgraph hlog

end
end krylov.Asymptotics
