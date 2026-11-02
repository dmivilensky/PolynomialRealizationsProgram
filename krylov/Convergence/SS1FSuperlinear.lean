import krylov.Convergence.SS1Execution
import krylov.Convergence.SS1FSourceLimit

/-!
Article: main_krylov, thm:ss1F, genuine recursive SS1-F superlinearity.
Use: discharge the finite moving-window source theorem on the literal
one-gradient value-corrected execution, with its actual split policy.
Source: the original (S) and uniform independence hypotheses; actual local
third derivatives produce the model limits, not an assumed error recurrence.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual one-gradient SS1-F sequence is superlinear under its original
local source, (S), convergence and normalized independence assumptions. -/
theorem ss1FSequence_superlinear
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (T : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0) {L₂ L₃ : ℝ≥0}
    (hH : LipschitzOnWith L₂ H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    {B₀ : ℝ} (hB₀ : 0≤B₀) (hT₀ : ∀ h,‖h‖=1 → |(T 0).form h h h|≤B₀)
    (split : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+1))) → Fin (n+1) → ℝ)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1FSequence f G split seed) atTop (𝓝 0))
    {Cw σ : ℝ} (hCw : 0≤Cw) (hσ : 0<σ)
    (hw : ∀ᶠ k in atTop,∀ i : Fin (n+1),
      ‖splitRemainder (ss1FSequence f G split seed (k+i.val))
        (windowStep (ss1FSequence f G split seed) k i)
        (ss1FSequence f G split seed (k+n+1))
        (split (fun j=>ss1FSequence f G split seed (k+j.val)) i)‖≤
      Cw*‖ss1FSequence f G split seed (k+n+1)-ss1FSequence f G split seed (k+i.val+1)‖)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k)))) :
    (fun k=>ss1FSequence f G split seed (k+1)) =o[atTop]
      (fun k=>‖ss1FSequence f G split seed k‖) := by
  let x := ss1FSequence f G split seed
  have ha (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val)) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val+1)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc,Function.comp_def,x] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hx : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc,Function.comp_def,x] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hm : ∀ᶠ k in atTop,(∀ i : Fin (n+1),x (k+i.val)∈S) ∧
      (∀ i : Fin (n+1),x (k+i.val+1)∈S) ∧x (k+n+1)∈S :=
    ((Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)).and
      (hx.eventually hnbhd) |>.mono fun _ h=>⟨h.1.1,h.1.2,h.2⟩
  have hi : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep x k))).det ∧
      ‖(windowMatrix (unitWindow (windowStep x k)))⁻¹‖≤σ⁻¹ :=
    hind.mono fun k h=>⟨h.1,Secant.inverse_bound_of_leastGain _ h.1 hσ h.2⟩
  have hh := ss1F_source_superlinear f G H T S hS h₀ hH hH₀ hf hG hG₀ hT hLip hB₀ hT₀
    (fun k i=>x (k+i.val)) (fun k i=>x (k+i.val+1)) (fun k=>x (k+n+1))
    (fun k=>split (fun i=>x (k+i.val))) ha hb hx hCw (inv_nonneg.mpr hσ.le) hm hw hi
  have hs : (fun k=>x (k+n+2)) =o[atTop] (fun k=>‖x (k+n+1)‖) :=
    hh.congr_left fun k=>(ss1FSequence_step f G split seed k).symm
  have hmap : ((fun k=>x (k+1)) ∘ (fun k=>k+(n+1))) =o[atTop]
      ((fun k=>‖x k‖) ∘ (fun k=>k+(n+1))) := by
    simpa only [Function.comp_def,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hs
  have hout := (Asymptotics.isLittleO_map).mpr hmap
  simpa only [Filter.map_add_atTop_eq_nat] using hout

end
end krylov.Convergence
