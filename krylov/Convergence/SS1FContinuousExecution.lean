import krylov.Convergence.SS1Execution
import krylov.Convergence.SS1FContinuousLimit

/-!
Article: main_krylov, thm:ss1F, continuous-D3 actual execution.
Use: specialize the original continuous-source result to the literal
recursive method, deriving all window admission from genuine convergence.
Source: the anchored trapezoid modulus, actual normalized independence,
and the original (S) split condition.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n+1))
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace


/-- The genuine recursive SS1-F execution is superlinear with only
continuous D3. No Lipschitz-third or auxiliary model limit is assumed. -/
theorem ss1FSequence_continuous_superlinear
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (T : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hc : ContinuousOn (fun z=>(T z).form) S)
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
  have hi : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep x k))).det ∧
      ‖(windowMatrix (unitWindow (windowStep x k)))⁻¹‖≤σ⁻¹ :=
    hind.mono fun k h=>⟨h.1,Secant.inverse_bound_of_leastGain _ h.1 hσ h.2⟩
  have hh := ss1F_continuous_source_superlinear f G H T S hS h₀ hnbhd hH₀ hf hG hG₀ hT hc
    (fun k i=>x (k+i.val)) (fun k i=>x (k+i.val+1)) (fun k=>x (k+n+1))
    (fun k=>split (fun i=>x (k+i.val))) ha hb hx hCw (inv_nonneg.mpr hσ.le) hw hi
  have hs : (fun k=>x (k+n+2)) =o[atTop] (fun k=>‖x (k+n+1)‖) :=
    hh.congr_left fun k=>(ss1FSequence_step f G split seed k).symm
  have hmap : ((fun k=>x (k+1)) ∘ (fun k=>k+(n+1))) =o[atTop]
      ((fun k=>‖x k‖) ∘ (fun k=>k+(n+1))) := by
    simpa only [Function.comp_def,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hs
  have hout := (Asymptotics.isLittleO_map).mpr hmap
  simpa only [Filter.map_add_atTop_eq_nat] using hout


end
end krylov.Convergence
