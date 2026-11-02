import krylov.LinearAlgebra.CorrectionAsymptotics
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
Article: main_krylov, thm:C and apD:prefix, adaptive pairing replacement orders.
Use: replace actual old steps and actual line steps by their genuine reference
values only after extracting the small operator difference.
Source: Cauchy--Schwarz, operator norm and exact bilinear difference identities.
-/

namespace krylov.Correction
noncomputable section
open Filter Asymptotics Topology krylov.LinearAlgebra
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {α : Type*} {f : Filter α}

/-- Genuine inner products multiply the two actual scalar asymptotic orders.
Use: retain each factor's perturbation degree in search-residual and model-error expansions.
Article: main_krylov, apD:prefix, finite pairing calculus.
Source: mathlib norm_inner_le_norm, real Cauchy--Schwarz.
Proof: dominate the actual pairing norm by the product of the two vector norms. -/
theorem inner_order (u v : α → E) (s t : α → ℝ) (hu : u =O[f] s) (hv : v =O[f] t) :
    (fun x => inner ℝ (u x) (v x)) =O[f] (fun x => s x*t x) := by
  have hb : (fun x => inner ℝ (u x) (v x)) =O[f] (fun x => ‖u x‖*‖v x‖) :=
    isBigO_of_le _ fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact norm_inner_le_norm _ _
  exact hb.trans (hu.norm_left.mul hv.norm_left)

/-- Replacing the two outer adaptive vectors in a first-order operator pairing costs only second order.
Use: the fresh defect and the model error retain actual operator increments with fixed reference steps.
Article: main_krylov, thm:C and apD:prefix, frozen outer factors.
Proof: split the exact difference into the changed left vector and the changed
right vector; each changed factor multiplies a first-order operator. -/
theorem pairing_reference_order (u v : α → E) (u₀ v₀ : E) (T : α → E →L[ℝ] E)
    (s : α → ℝ) (hs : Tendsto s f (𝓝 0))
    (hu : (fun x => u x-u₀) =O[f] s) (hv : (fun x => v x-v₀) =O[f] s)
    (hT : T =O[f] s) :
    (fun x => inner ℝ (u x) (T x (v x))-inner ℝ u₀ (T x v₀)) =O[f] (fun x => s x^2) := by
  -- The real varying right vector is bounded near its proved reference value.
  have hvt : Tendsto v f (𝓝 v₀) := by
    simpa only [sub_add_cancel,zero_add] using (hv.trans_tendsto hs).add_const v₀
  have ha := inner_order (fun x => u x-u₀) (fun x => T x (v x)) s s hu
    (by simpa only [mul_one] using operator_action_order T v s (fun _ => 1) hT (hvt.isBigO_one ℝ))
  have hb := inner_order (fun _ : α => u₀) (fun x => T x (v x-v₀)) (fun _ => 1)
    (fun x => s x^2) (tendsto_const_nhds.isBigO_one ℝ)
    (by simpa only [← pow_two] using operator_action_order T (fun x => v x-v₀) s s hT hv)
  have ha' : (fun x => inner ℝ (u x-u₀) (T x (v x))) =O[f] (fun x => s x^2) := by
    simpa only [← pow_two] using ha
  have hb' : (fun x => inner ℝ u₀ (T x (v x-v₀))) =O[f] (fun x => s x^2) := by
    simpa only [one_mul] using hb
  exact (ha'.add hb').congr_left fun x => by
    simp only [inner_sub_left,map_sub,inner_sub_right]
    abel

/-- Analytic actual vectors differ from their actual reference values by first order in parameter norm.
Use: discharge adaptive outer-factor replacement premises from genuine trajectory regularity.
Article: main_krylov, apD:prefix, genuine first-order trajectory differences.
Proof: differentiability bounds the actual function difference by the input difference. -/
theorem analytic_reference_order {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : X → V) (hu : AnalyticAt ℝ u 0) :
    (fun x => u x-u 0) =O[𝓝 (0 : X)] (fun x => ‖x‖) := by
  simpa only [sub_zero] using hu.differentiableAt.isBigO_sub.norm_right

end
end krylov.Correction
