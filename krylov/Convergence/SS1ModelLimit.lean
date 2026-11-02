import krylov.Convergence.SS1Execution
import krylov.Convergence.WindowModelLimits

/-!
Article: main_krylov, thm:Ip, genuine SS1 inverse-model limit.
Use: obtain the actual inverse-model factor 1+o(1) needed for the sharp
oldest-pair coefficient directly from genuine moving trajectory secants.
Source: the actual derivative endpoint bound and normalized observed model.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual ambient SS1 model formed from normalized real sliding pairs. -/
def slidingSS1Model
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (x : ℕ → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  inverseCongruence (windowMatrix (unitWindow (windowStep x k)))
    (ss1Model (unitWindow (windowStep x k)) (unitWindowImages (windowStep x k) (windowImage G x k)))

/-- Genuine local derivatives and actual full-window conditioning force the
computed sliding SS1 model and inverse to converge to the limiting Hessian.
No model convergence is a hypothesis. -/
theorem slidingSS1Model_tendsto
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (x : ℕ → EuclideanSpace ℝ (Fin (n+1))) (hconv : Tendsto x atTop (𝓝 0))
    {C : ℝ} (hC : 0≤C)
    (hind : ∀ᶠ k in atTop,IsUnit (windowMatrix (unitWindow (windowStep x k))).det ∧
      ‖(windowMatrix (unitWindow (windowStep x k)))⁻¹‖≤C) :
    Tendsto (slidingSS1Model G x) atTop (𝓝 1) ∧
    Tendsto (fun k=>(slidingSS1Model G x k)⁻¹) atTop (𝓝 1) ∧
    (∀ᶠ k in atTop,IsUnit (slidingSS1Model G x k).det) := by
  let a := fun k (i : Fin (n+1))=>x (k+i.val)
  let b := fun k (i : Fin (n+1))=>x (k+i.val+1)
  let V := fun k=>windowMatrix (unitWindow (windowStep x k))
  let M : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun k=>ss1Model (unitWindow (windowStep x k))
    (unitWindowImages (windowStep x k) (windowImage G x k))
  have ha (i : Fin (n+1)) : Tendsto (fun k=>a k i) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+1)) : Tendsto (fun k=>b k i) atTop (𝓝 0) := by
    simpa only [a,b,Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hm : ∀ᶠ k in atTop,(∀ i,a k i∈S) ∧(∀ i,b k i∈S) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)
  have hs : ∀ᶠ k in atTop,∀ i,windowStep (n:=n+1) x k i≠0 := by
    filter_upwards [hind] with k hk i
    intro hz
    have hh := windowMatrix_step_ne_zero (unitWindow (windowStep x k)) hk.1 i
    apply hh
    simp only [unitWindow,rescaleWindow,hz,smul_zero]
  let ε := fun k=>(L:ℝ)/2*sourceWindowRadius (a k) (b k)
  have hε : Tendsto ε atTop (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun i _=>(ha i).norm.add (hb i).norm)
    have hr : Tendsto (fun k=>sourceWindowRadius (a k) (b k)) atTop (𝓝 0) := by
      simpa only [sourceWindowRadius,norm_zero,add_zero,Finset.sum_const_zero] using hh
    simpa only [mul_zero] using hr.const_mul ((L:ℝ)/2)
  have he : Tendsto (fun k=>M k-(V k)ᵀ*V k) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun k=>((n+1:ℕ):ℝ)*ε k)
    · filter_upwards [hm,hs] with k hk hsk
      rw [←crossGram_windowMatrix]
      exact windowDataError_norm _ _ (unitWindow_norm _ hsk)
        (mul_nonneg (by positivity) (sourceWindowRadius_nonneg _ _))
        (source_unit_window_error G H S hS h₀ hH hH₀ hG _ _ hk.1 hk.2 hsk)
    · simpa only [mul_zero] using hε.const_mul ((n+1:ℕ):ℝ)
  exact square_window_model_tendsto V M hC (hind.mono fun _ h=>h.1) (hind.mono fun _ h=>h.2) he

end
end krylov.Convergence
