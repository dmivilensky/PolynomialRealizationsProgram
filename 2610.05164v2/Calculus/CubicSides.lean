import «2610.05164v2».DualCertificate.Coordinate
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Piecewise

/-!
Article: 2610.05164v2, Lemma 16.
Gluing two continuous cubic endpoint charts on [0,2].
Use: `«2610.05164v2».Calculus.cubicSides_two` feeds
`«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope_two` (curve Slope two).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Set Real
set_option autoImplicit false

/--
Defines `cubeRoot` of type `ℝ` by `q^((3:ℝ)⁻¹)`.

Use: `«2610.05164v2».Calculus.cubeRoot_one` rewrites with this definition to establish exact
identity `cubeRoot 1=1`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.
-/
def cubeRoot (q : ℝ) : ℝ := q^((3:ℝ)⁻¹)

/--
Continuity of the displayed function: `Continuous cubeRoot`.

Use: `«2610.05164v2».Calculus.cubicSides_continuous` uses this continuity result to establish
continuity on the stated domain: `ContinuousOn (cubicSides f g) (Icc 0 2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem cubeRoot_continuous : Continuous cubeRoot :=
  Real.continuous_rpow_const (by positivity)

/--
Exact identity `(cubeRoot q)^3=q`.

Use: `«2610.05164v2».Calculus.cubeRoot_mem` uses this identity to establish membership in the
specified domain/enclosure: `cubeRoot q∈Icc (0:ℝ) 1`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem cubeRoot_cube {q : ℝ} (hq : 0≤q) : (cubeRoot q)^3=q :=
  Real.rpow_inv_natCast_pow hq (by decide : 3≠0)

/--
Membership in the specified domain/enclosure: `cubeRoot q∈Icc (0:ℝ) 1`.

Use: `«2610.05164v2».Calculus.cubicSides_continuous` uses this assertion to establish
continuity on the stated domain: `ContinuousOn (cubicSides f g) (Icc 0 2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.cubeRoot_cube` with the arguments
shown in the proof.
-/
theorem cubeRoot_mem {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : cubeRoot q∈Icc (0:ℝ) 1 := by
  refine ⟨Real.rpow_nonneg hq.1 _,?_⟩
  apply le_of_pow_le_pow_left₀ (by decide : 3≠0) (by norm_num : (0:ℝ)≤1)
  simpa only [cubeRoot_cube hq.1,one_pow] using hq.2

/--
The stated quantitative bound `0<cubeRoot q`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_analytic` uses this bound to establish the
precise assertion is `D.analytic.Admissible hκ`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem cubeRoot_pos {q : ℝ} (hq : 0<q) : 0<cubeRoot q := Real.rpow_pos_of_pos hq _

/--
Exact identity `cubeRoot 0=0`.

Use: `«2610.05164v2».Calculus.cubicSides_two` rewrites with this identity to establish exact
identity `cubicSides f g 2=g 0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem cubeRoot_zero : cubeRoot 0=0 := by norm_num [cubeRoot]
/--
Exact identity `cubeRoot 1=1`.

Use: `«2610.05164v2».Calculus.cubicSides_continuous` uses this identity to establish continuity
on the stated domain: `ContinuousOn (cubicSides f g) (Icc 0 2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem cubeRoot_one : cubeRoot 1=1 := by simp [cubeRoot]

/--
Defines `cubicSides` of type `ℝ` by `if q≤1 then f (cubeRoot q) else g (cubeRoot (2-q))`.

Use: `«2610.05164v2».Calculus.cubicSides_two` rewrites with this definition to establish exact
identity `cubicSides f g 2=g 0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.
-/
def cubicSides (f g : ℝ → ℝ) (q : ℝ) : ℝ :=
  if q≤1 then f (cubeRoot q) else g (cubeRoot (2-q))

/--
Continuity on the stated domain: `ContinuousOn (cubicSides f g) (Icc 0 2)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope_continuous` uses this
continuity result to establish continuity on the stated domain: `ContinuousOn (P.curveSlope N
hκ) (Icc 0 2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.cubeRoot_continuous`,
`«2610.05164v2».Calculus.cubeRoot_mem`, `«2610.05164v2».Calculus.cubeRoot_one` with the
arguments shown in the proof.
-/
theorem cubicSides_continuous {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0:ℝ) 1)) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hm : f 1=g 1) : ContinuousOn (cubicSides f g) (Icc 0 2) := by
  -- Use the identities/estimates `«2610.05164v2».Calculus.cubeRoot_continuous`,
  -- `«2610.05164v2».Calculus.cubeRoot_mem`, `«2610.05164v2».Calculus.cubeRoot_one` with the
  -- arguments shown in the proof.
  classical
  let : ∀ x : ℝ, Decidable (x∈Iic (1:ℝ)) := Classical.decPred _
  -- Establish continuity hl before using the function at limits or in calculus arguments.
  have hl : ContinuousOn (fun q => f (cubeRoot q)) (Icc (0:ℝ) 2 ∩ closure (Iic (1:ℝ))) := by
    apply hf.comp cubeRoot_continuous.continuousOn
    intro q hq
    rw [isClosed_Iic.closure_eq] at hq
    exact cubeRoot_mem ⟨hq.1.1,hq.2⟩
  -- Establish continuity hr before using the function at limits or in calculus arguments.
  have hr : ContinuousOn (fun q => g (cubeRoot (2-q))) (Icc (0:ℝ) 2 ∩ closure (Iic (1:ℝ))ᶜ) := by
    apply hg.comp (cubeRoot_continuous.comp (continuous_const.sub continuous_id)).continuousOn
    intro q hq
    rw [compl_Iic,closure_Ioi] at hq
    change (0≤q ∧ q≤2) ∧ 1≤q at hq
    change cubeRoot (2-q)∈Icc (0:ℝ) 1
    exact cubeRoot_mem ⟨by linarith [hq.1.2],by linarith [hq.2]⟩
  exact ContinuousOn.piecewise (t := Iic (1:ℝ))
    (fun q hq => by
      rw [frontier_Iic] at hq
      have he : q=1 := hq.2
      subst q
      simpa only [show (2:ℝ)-1=1 by norm_num,cubeRoot_one] using hm
      ) hl hr

/--
Exact identity `cubicSides f g 0=f 0`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope_zero` rewrites with this
identity to establish the identity `P.curveSlope N hκ 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.cubeRoot_zero` with the arguments
shown in the proof.
-/
theorem cubicSides_zero (f g : ℝ → ℝ) : cubicSides f g 0=f 0 := by simp [cubicSides,cubeRoot_zero]

/--
Exact identity `cubicSides f g 2=g 0`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope_two` rewrites with this
identity to establish the identity `P.curveSlope N hκ 2=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.cubeRoot_zero` with the arguments
shown in the proof.
-/
theorem cubicSides_two (f g : ℝ → ℝ) : cubicSides f g 2=g 0 := by simp [cubicSides,cubeRoot_zero]

end
end «2610.05164v2».Calculus
