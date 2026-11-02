import krylov.Correction.ObservedGateAcceptance
import krylov.Methods.ProjectedSearch

/-!
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform finite-cycle step.
Use: Close the actual Gram, angle, gate and projected-residual induction
before the first small line displacement, using one fixed quantitative allowance.
Source: proved real observed conjugacy and spectral gates, true normalized
model solves, actual recorded-step transfer and elementary scalar inequalities.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- The actual normalized augmented Gram has a dimension-times-angle bound from the real old angles and genuine measured-image conjugacy.
Use: Assemble the actual uniform gated-RFC cutoff induction from original measured data.
Article: main_krylov, thm:UCq and thm:UCg, genuine finite-cycle cutoff step.
Proof: Normalize only proved nonzero true columns. Actual relative old-image errors and real conjugacy bound each new-direction angle, while the existing old-angle hypothesis controls old pairs. Apply the genuine spectral unit-Gram estimate.
-/
theorem unit_augmented_observed_gram (s y : Fin p → E) (d : E)
    (hs : ∀ i, s i≠0) (hd : d≠0) {a η : ℝ} (ha : 0≤a) (hηa : η≤a)
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖) (ho : ∀ i, inner ℝ (y i) d=0)
    (hangle : ∀ i j, i≠j → |inner ℝ (unitWindow s i) (unitWindow s j)|≤a) :
    ‖crossGram (unitWindow (Fin.cons d s)) (unitWindow (Fin.cons d s))-1‖≤((p+1 : ℕ) : ℝ)*a := by
  have hu (i : Fin (p+1)) : (Fin.cons d s : Fin (p+1) → E) i≠0 := Fin.cases hd hs i
  have hnew (j : Fin p) : |inner ℝ (unitWindow s j) (NormedSpace.normalize d)|≤a := by
    have horth : inner ℝ (rescaleWindow y (fun i => ‖s i‖⁻¹) j) (NormedSpace.normalize d)=0 := by
      simp only [rescaleWindow,NormedSpace.normalize,real_inner_smul_left,real_inner_smul_right,ho,mul_zero]
    have h := approximate_conjugacy_bound (unitWindow s j)
      (rescaleWindow y (fun i => ‖s i‖⁻¹) j) (NormedSpace.normalize d)
      (ContinuousLinearMap.id ℝ E) (unitWindow_norm s hs j) (ε := 0) (by simp)
      (unitWindow_pair_error s y hs hy j) horth
    simp only [ContinuousLinearMap.id_apply,zero_add,NormedSpace.norm_normalize hd,mul_one] at h
    exact h.trans hηa
  apply unitGram_deviation _ (unitWindow_norm _ hu) ha
  intro i j hij
  revert hij
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; exact (hij rfl).elim
    · intro _hij
      change |inner ℝ (NormedSpace.normalize d) (unitWindow s j)|≤a
      rw [real_inner_comm]
      exact hnew j
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro _hij
      change |inner ℝ (unitWindow s i) (NormedSpace.normalize d)|≤a
      exact hnew i
    · intro hij
      change |inner ℝ (unitWindow s i) (unitWindow s j)|≤a
      exact hangle i j (fun h => hij (congrArg Fin.succ h))

end
end krylov.Correction
