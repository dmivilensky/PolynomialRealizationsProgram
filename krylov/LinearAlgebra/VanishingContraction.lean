import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), actual asymptotic Jacobi pivot contraction.
Use: turn a genuine eventually contracting pivot error recurrence with actual vanishing coefficient defects into a true zero error limit.
Source: elementary finite geometric iteration and the standard real geometric power limit.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Filter
open scoped Topology

/-- A genuine bounded nonnegative error with an actual strict eventual contraction and true vanishing forcing converges to zero.
Use: A genuine bounded nonnegative error with an actual strict eventual contraction and true vanishing forcing converges to zero.
Article: main_krylov, prop:phi(c), actual asymptotic Jacobi pivot contraction.
Proof: Choose a true forcing threshold, iterate the actual contraction over a fixed geometric block and bound every sufficiently late original error. -/
theorem bounded_vanishing_contraction (e f : ℕ → ℝ) (C r : ℝ)
    (he : ∀ n,0≤e n) (hC : ∀ n,e n≤C) (hr : 0≤r) (hr1 : r<1)
    (hf : Tendsto f atTop (𝓝 0)) (N0 : ℕ)
    (hstep : ∀ n,N0≤n → e (n+1)≤r*e n+f n) : Tendsto e atTop (𝓝 0) := by
  -- Fix an actual error tolerance and a genuine tail where forcing fits below the strict contraction gap.
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  have hgap : 0 < eps*(1-r)/2 := by positivity
  obtain ⟨Nf,hNf⟩ := eventually_atTop.mp ((tendsto_order.mp hf).2 (eps*(1-r)/2) hgap)
  let N := max N0 Nf
  -- Iterate the actual recurrence from every original tail index, retaining its true common error bound.
  have hbound (k : ℕ) : ∀ n,N≤n → e (n+k)≤r^k*C+eps/2 := by
    induction k with
    | zero =>
      intro n _
      simp only [Nat.add_zero,pow_zero,one_mul]
      exact (hC n).trans (le_add_of_nonneg_right (by positivity))
    | succ k ih =>
      intro n hn
      have hrec := hstep (n+k) (by dsimp only [N] at hn;omega)
      have hforce := hNf (n+k) (by dsimp only [N] at hn;omega)
      have hmul := mul_le_mul_of_nonneg_left (ih n hn) hr
      rw [show n+(k+1)=n+k+1 by omega,pow_succ]
      nlinarith
  -- A fixed genuine geometric block reduces the remaining actual initial error below the chosen tolerance.
  have hpow : Tendsto (fun k : ℕ => r^k*C) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((tendsto_order.mp hpow).2 (eps/2) (by positivity))
  refine ⟨N+M,?_⟩
  intro n hn
  have hb := hbound M (n-M) (by omega)
  rw [Nat.sub_add_cancel (by omega : M≤n)] at hb
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (he n)]
  have hm := hM M le_rfl
  linarith
end
end krylov.LinearAlgebra
