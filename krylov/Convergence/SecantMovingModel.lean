import krylov.Convergence.WindowModelLimits
import krylov.Convergence.SecantWindowSource

/-!
Article: main_krylov, apG:mss, genuine moving observed models.
Use: obtain actual model convergence and inverse domains for full secant
frames whose final column can be a current RFC probe. Source: true endpoint
FTC estimates and exact normalization/congruence. Model convergence is
proved from the original derivatives, never postulated.
-/

namespace krylov.Convergence
noncomputable section
open Set Filter Topology Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {p : ℕ} {α : Type*} {l : Filter α}

/-- The full actual moving secant model and its inverse tend to identity;
the genuine observed coefficient inverse is eventually defined. -/
theorem source_moving_model_tendsto
    (G : EuclideanSpace ℝ (Fin (p+1)) → EuclideanSpace ℝ (Fin (p+1)))
    (H : EuclideanSpace ℝ (Fin (p+1)) → EuclideanSpace ℝ (Fin (p+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (p+1)))
    (S : Set (EuclideanSpace ℝ (Fin (p+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (p+1)))∈S) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ _) (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (a b : α → Fin (p+1) → EuclideanSpace ℝ (Fin (p+1)))
    (ha : ∀ i,Tendsto (fun z=>a z i) l (𝓝 0))
    (hb : ∀ i,Tendsto (fun z=>b z i) l (𝓝 0))
    (hm : ∀ᶠ z in l,(∀ i,a z i∈S) ∧(∀ i,b z i∈S))
    {C : ℝ} (hC : 0≤C)
    (hframe : ∀ᶠ z in l,
      IsUnit (windowMatrix (unitWindow (fun i=>b z i-a z i))).det ∧
      ‖(windowMatrix (unitWindow (fun i=>b z i-a z i)))⁻¹‖≤C) :
    let V := fun z=>windowMatrix (unitWindow (fun i=>b z i-a z i))
    let M := fun z=>ss1Model (unitWindow (fun i=>b z i-a z i))
      (unitWindowImages (fun i=>b z i-a z i) (fun i=>G (b z i)-G (a z i)))
    Tendsto (fun z=>inverseCongruence (V z) (M z)) l (𝓝 1) ∧
    Tendsto (fun z=>(inverseCongruence (V z) (M z))⁻¹) l (𝓝 1) ∧
    (∀ᶠ z in l,IsUnit (ss1Model (fun i=>b z i-a z i) (fun i=>G (b z i)-G (a z i))).det) := by
  dsimp only
  let s := fun z i=>b z i-a z i
  let y := fun z i=>G (b z i)-G (a z i)
  let V := fun z=>windowMatrix (unitWindow (s z))
  let M := fun z=>ss1Model (unitWindow (s z)) (unitWindowImages (s z) (y z))
  let ε := fun z=>(L:ℝ)/2*sourceWindowRadius (a z) (b z)
  have hε : Tendsto ε l (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun i _=>(ha i).norm.add (hb i).norm)
    have hr : Tendsto (fun z=>sourceWindowRadius (a z) (b z)) l (𝓝 0) := by
      simpa only [sourceWindowRadius,norm_zero,add_zero,Finset.sum_const_zero] using hh
    simpa only [mul_zero] using hr.const_mul ((L:ℝ)/2)
  have hs : ∀ᶠ z in l,∀ i,s z i≠0 := by
    filter_upwards [hframe] with z hz i
    intro hi
    have hh := windowMatrix_step_ne_zero (unitWindow (s z)) hz.1 i
    apply hh
    simp only [unitWindow,rescaleWindow,hi,smul_zero]
  have herr : Tendsto (fun z=>M z-(V z)ᵀ*V z) l (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun z=>((p+1:ℕ):ℝ)*ε z)
    · filter_upwards [hm,hs] with z hz hsz
      rw [←crossGram_windowMatrix]
      exact windowDataError_norm _ _ (unitWindow_norm _ hsz)
        (mul_nonneg (by positivity) (sourceWindowRadius_nonneg _ _))
        (source_unit_window_error G H S hS h₀ hH hH₀ hG _ _ hz.1 hz.2 hsz)
    · simpa only [mul_zero] using hε.const_mul ((p+1:ℕ):ℝ)
  have hh := square_window_model_tendsto V M hC (hframe.mono fun _ h=>h.1)
    (hframe.mono fun _ h=>h.2) herr
  refine ⟨hh.1,hh.2.1,?_⟩
  filter_upwards [hh.2.2] with z hz
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  apply isUnit_iff_ne_zero.mp hz
  have hmzero : (M z).det=0 := by
    change (ss1Model (rescaleWindow (s z) (fun i=>‖s z i‖⁻¹))
      (rescaleWindow (y z) (fun i=>‖s z i‖⁻¹))).det=0
    rw [ss1Model_rescale,rescaleModel,det_mul,det_mul,hzero,mul_zero,zero_mul]
  rw [inverseCongruence,det_mul,det_mul,hmzero,mul_zero,zero_mul]

end
end krylov.Convergence
