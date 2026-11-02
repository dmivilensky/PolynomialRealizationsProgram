import krylov.OneGradient.TrialAmplitudes
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
/-!
Article: main_krylov, prop:hb(b), uniform chronological forgetting.
Use: control every original trial-error product simultaneously, including
arbitrary finitely many early trials, before transferring to actual amplitudes.
Source: finite interval-product splitting and the standard geometric limit.
-/

namespace krylov.OneGradient
noncomputable section
open Filter Topology
open scoped BigOperators

/-- A fixed old chronological product tends to zero when its later factors
tend to zero, without any bound on finitely many initial factors.
Use: remove every fixed early lagged-trial defect.
Article: main_krylov, prop:hb(b).
Proof: split at a genuine eventual half-contraction index; the remaining
finite product is bounded by the corresponding geometric power. -/
theorem trial_tail_product_tendsto (theta : ℕ → ℝ)
    (htheta : Tendsto theta atTop (𝓝 0)) (l : ℕ) :
    Tendsto (fun N => |∏ i∈Finset.Ico (l+1) N,theta i|) atTop (𝓝 0) := by
  have hthetaAbs : Tendsto (fun k => |theta k|) atTop (𝓝 (0:ℝ)) := by simpa using htheta.abs
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (hthetaAbs.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)))
  let M := max K (l+1)
  have hM : l+1≤M := le_max_right _ _
  have hbound (N : ℕ) (hN : M≤N) :
      |∏ i∈Finset.Ico (l+1) N,theta i|≤
        |∏ i∈Finset.Ico (l+1) M,theta i| *(1/2:ℝ)^(N-M) := by
    rw [← Finset.prod_Ico_consecutive theta hM hN,abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i∈Finset.Ico M N,(1/2:ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro i hi
        exact (hK i ((le_max_left K (l+1)).trans (Finset.mem_Ico.mp hi).1)).le
      _ = (1/2:ℝ)^(N-M) := by simp
  have hgeom : Tendsto (fun N => |∏ i∈Finset.Ico (l+1) M,theta i| *(1/2:ℝ)^(N-M))
      atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ)≤1/2 by norm_num)
      (show (1/2:ℝ)<1 by norm_num)).comp (tendsto_sub_atTop_nat M)).const_mul
        |∏ i∈Finset.Ico (l+1) M,theta i|
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
    (eventually_atTop.mpr ⟨M,hbound⟩) hgeom

/-- Vanishing chronological defects and vanishing correction ratios give
one uniform bound for all original full-horizon defect products.
Use: the maximum over every actual step tends to zero, not only each fixed
old step; this is the uniform quantifier needed in the lagged theorem.
Article: main_krylov, prop:hb(b).
Proof: the late defects are small and their genuine products are at most one.
There are finitely many earlier defects, whose full later products tend to zero. -/
theorem trial_products_uniform_small (epsilon theta : ℕ → ℝ)
    (hepsilon : Tendsto epsilon atTop (𝓝 0)) (htheta : Tendsto theta atTop (𝓝 0))
    (delta : ℝ) (hdelta : 0<delta) :
    ∀ᶠ N in atTop,∀ l<N,
      |epsilon l| *(∏ i∈Finset.Ico (l+1) N,|theta i|)<delta := by
  have hthetaAbs : Tendsto (fun k => |theta k|) atTop (𝓝 (0:ℝ)) := by simpa using htheta.abs
  have hepsilonAbs : Tendsto (fun k => |epsilon k|) atTop (𝓝 (0:ℝ)) := by simpa using hepsilon.abs
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    ((hepsilonAbs.eventually (gt_mem_nhds hdelta)).and
      (hthetaAbs.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))))
  have hearly (l : Fin K) : ∀ᶠ N in atTop,
      |epsilon l.val| *(∏ i∈Finset.Ico (l.val+1) N,|theta i|)<delta := by
    have h := (trial_tail_product_tendsto theta htheta l.val).const_mul |epsilon l.val|
    simp only [mul_zero,Finset.abs_prod] at h
    exact h.eventually (gt_mem_nhds hdelta)
  filter_upwards [Filter.eventually_all.mpr hearly] with N hN
  intro l hl
  by_cases hlate : K≤l
  · have hprod : (∏ i∈Finset.Ico (l+1) N,|theta i|)≤1 := by
      apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      intro i hi
      exact (hK i (by have := (Finset.mem_Ico.mp hi).1;omega)).2.le
    exact (mul_le_of_le_one_right (abs_nonneg _) hprod).trans_lt (hK l hlate).1
  · exact hN ⟨l,by omega⟩

end
end krylov.OneGradient
