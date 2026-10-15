import «2610.05164v2».LocalObstruction.JostTail

/-!
Article: 2610.05164v2, Theorem 6.1.
Lemma 26(iv): the actual two-sided Green diagonal at the sine density has a constant plus
exponential expansion with an o(n) remainder.
Use: `«2610.05164v2».LocalObstruction.sine_green_diagonal_tail` feeds
`«2610.05164v2».LocalObstruction.theorem_6_1` (theorem 6 1).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set Real Filter MeasureTheory Asymptotics «2610.05164v2».SineContinuum «2610.05164v2».Filters
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
The stated quantitative bound `(fun x => greenKernel s m x x-1/2- (sineJostCoefficient
s/(2*transmission s m))*exp (-2*x)) =o[atTop] n`.

Use: `«2610.05164v2».LocalObstruction.greenDiagonalGradient` uses this identity in the
displayed construction of `greenDiagonalGradient`. Its inputs and component formulas are fixed
by that definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem sine_green_diagonal_tail {s : ℝ} (hs : 0≤s) :
    (fun x => greenKernel s m x x-1/2-
      (sineJostCoefficient s/(2*transmission s m))*exp (-2*x)) =o[atTop] n := by
  -- Record the convergence hR with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hR : Tendsto (fun x => jost s m (-x)) atTop (𝓝 1) :=
    (jost_left_limit m_integrable (fun x => (m_positive x).le) hs).comp tendsto_neg_atTop_atBot
  -- Record the convergence hex with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hex : Tendsto (fun x : ℝ => exp (-2*x)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (by norm_num : (-2:ℝ)<0) tendsto_id)
  -- Record the convergence hL with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hL : Tendsto (fun x => transmission s m+sineJostCoefficient s*exp (-2*x))
      atTop (𝓝 (transmission s m)) := by
    simpa using tendsto_const_nhds.add (hex.const_mul (sineJostCoefficient s))
  have h₀ := (sineJost_tail hs).mul_isBigO (hR.isBigO_one ℝ)
  have h₁ := (hL.isBigO_one ℝ).mul_isLittleO (sineJost_reflected_tail hs)
  simp only [mul_one] at h₀
  simp only [one_mul] at h₁
  have hsum := h₀.add h₁
  have hproduct : (fun x => jost s m x*jost s m (-x)-transmission s m-
      sineJostCoefficient s*exp (-2*x)) =o[atTop] n := by
    convert! hsum using 1
    funext x
    ring
  have hT : 0<transmission s m :=
    zero_lt_one.trans_le (transmission_ge_one m_integrable (fun x => (m_positive x).le) hs)
  have he : (fun x => greenKernel s m x x-1/2-
      (sineJostCoefficient s/(2*transmission s m))*exp (-2*x))=
      fun x => (1/(2*transmission s m))*(jost s m x*jost s m (-x)-transmission s m-
        sineJostCoefficient s*exp (-2*x)) := by
    funext x
    rw [greenKernel_diagonal_jost m_integrable (fun x => (m_positive x).le) m_continuous hs m_even]
    field_simp [hT.ne']
  rw [he]
  exact hproduct.const_mul_left _

end
end «2610.05164v2».LocalObstruction
