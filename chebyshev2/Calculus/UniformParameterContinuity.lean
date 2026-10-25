import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
Article: chebyshev2, Proposition 13.
Joint continuity from a uniform parameter modulus and continuous slices.
Use: `chebyshev2.Calculus.continuous_of_uniform_parameter_modulus` feeds
`chebyshev2.Primal.familyNonlinearFilter_joint_continuous` (family Nonlinear Filter joint
continuous).
Proof chain: `chebyshev2.Primal.familyConstraintMap_c1` — chebyshev2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
open Filter
open scoped Topology
set_option autoImplicit false
variable {H : Type*} [TopologicalSpace H]

/--
Continuity of the displayed function: `Continuous f.uncurry`.

Use: `chebyshev2.Primal.familyLinearFilter_joint_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (familyLinearFilter hψ hθ κ
reflected).uncurry`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem continuous_of_uniform_parameter_modulus {f : H → ℝ → ℝ}
    (ht : ∀ a,Continuous (f a))
    (hmod : ∀ b,∃ D : H → ℝ,ContinuousAt D b ∧ D b=0 ∧
      ∀ a t,|f a t-f b t|≤D a) : Continuous f.uncurry := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨D,hD,hDz,hbound⟩ := hmod p.1
  -- Record the convergence hb with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hb : Tendsto (fun q : H × ℝ => D q.1+|f p.1 q.2-f p.1 p.2|)
      (𝓝 p) (𝓝 0) := by
    have h1 := hD.comp (continuous_fst.continuousAt (x:=p))
    have h2 := ((ht p.1).continuousAt.comp (continuous_snd.continuousAt (x:=p))).tendsto.sub_const (f p.1 p.2)
    simpa only [Function.comp_def,hDz,sub_self,abs_zero,add_zero] using h1.tendsto.add h2.abs
  have h := squeeze_zero_norm' (f:=fun q : H × ℝ => f q.1 q.2-f p.1 p.2)
    (Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs]
      exact (abs_sub_le _ _ _).trans (add_le_add (hbound q.1 q.2) le_rfl))) hb
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa only [norm_zero,Function.uncurry] using h.norm)

end chebyshev2.Calculus
