import krylov.Envelope.Continuation
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), genuine compact continuation limit from true coefficient limits.
Use: derive convergence in the actual compact-function norm for a fixed real continuation length from genuine shifted line and recurrence coefficient limits.
Source: the original polynomial state recurrence, actual finite coefficient shifts and continuous operations in the genuine compact continuous-function algebra.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial Filter
open scoped Topology
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Genuine asymptotic line and recurrence coefficients give actual compact-function norm convergence of both true fixed-length continuation polynomials.
Use: Genuine asymptotic line and recurrence coefficients give actual compact-function norm convergence of both true fixed-length continuation polynomials.
Article: main_krylov, prop:phi(c), genuine compact continuation limit from true coefficient limits.
Proof: Induct through the original measured polynomial state in the actual compact-function algebra; every true shifted scalar coefficient has the same genuine limit. -/
theorem compact_continuation_limit (α β : ℕ → ℝ) (a b : ℝ)
    (hα : Tendsto α atTop (𝓝 a)) (hβ : Tendsto β atTop (𝓝 b)) (x : C(K,ℝ)) (r : ℕ) :
    Tendsto (fun j => aeval x (phi α β j r)) atTop
      (𝓝 (aeval x (phi (fun _ => a) (fun _ => b) 0 r))) ∧
    Tendsto (fun j => aeval x (psi α β j r)) atTop
      (𝓝 (aeval x (psi (fun _ => a) (fun _ => b) 0 r))) := by
  -- Only finitely many genuine shifted coefficients enter each actual fixed-length continuation state.
  induction r with
  | zero =>
    simp only [phi_zero,psi_zero]
    exact ⟨tendsto_const_nhds,tendsto_const_nhds⟩
  | succ r ih =>
    have ha := (continuous_algebraMap ℝ C(K,ℝ)).tendsto a |>.comp (hα.comp (tendsto_add_atTop_nat r))
    have hb := (continuous_algebraMap ℝ C(K,ℝ)).tendsto b |>.comp (hβ.comp (tendsto_add_atTop_nat r))
    have hx : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
    have hp := ih.1.add ((ha.mul hx).mul ih.2)
    have hq := hp.neg.add (hb.mul ih.2)
    simp only [phi_succ,psi_succ,map_add,map_mul,map_neg,aeval_C,aeval_X] at ⊢
    exact ⟨hp,hq⟩
end
end krylov.Envelope
