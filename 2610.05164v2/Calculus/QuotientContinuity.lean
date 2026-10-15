import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: 2610.05164v2, Theorem 3.6.
Joint continuity of a removable cubic quotient, with a locally uniform seventh-order bound.
Use: `«2610.05164v2».Calculus.cube_rpow_seven_thirds` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_joint_bound` (defect joint bound).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Set Filter
open scoped Topology
set_option autoImplicit false

 /--
Continuity of the displayed function: `Continuous (fun p => if (p.2:ℝ)=0 then 0 else f
p/(p.2:ℝ)^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defectQuotient_joint_continuous`
uses this continuity result to establish continuity of the displayed function: `Continuous (fun
p : ParameterDomain => N.defectQuotient p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Separate `(p.2:ℝ)=0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Pass the established inequalities to the limit using the displayed filter
convergence. Intersect the eventual or almost-everywhere hypotheses, then prove the asserted
relation at an arbitrary point in that intersection.
-/
theorem continuous_cubic_quotient {X : Type*} [TopologicalSpace X]
    (f : X × Icc (0:ℝ) 1 → ℝ) (B : X → ℝ)
    (hf : Continuous f) (hB : Continuous B)
    (hb : ∀ p, 0≤f p ∧ f p≤B p.1*(p.2:ℝ)^7) :
    Continuous (fun p => if (p.2:ℝ)=0 then 0 else f p/(p.2:ℝ)^3) := by
  -- Establish continuity ht before using the function at limits or in calculus arguments.
  have ht : Continuous (fun p : X × Icc (0:ℝ) 1 => (p.2:ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : (p.2:ℝ)=0
  · change Tendsto _ (𝓝 p) (𝓝 (if (p.2:ℝ)=0 then 0 else f p/(p.2:ℝ)^3))
    simp only [hp,ite_true]
    apply squeeze_zero' (Eventually.of_forall (fun z => ?_))
      (Eventually.of_forall (fun z => ?_))
      (show Tendsto (fun z : X × Icc (0:ℝ) 1 => B z.1*(z.2:ℝ)^4) (𝓝 p) (𝓝 0) by
        have hc : Continuous (fun z : X × Icc (0:ℝ) 1 => B z.1*(z.2:ℝ)^4) := by
          convert! (hB.comp continuous_fst).mul (ht.pow 4) using 1
        simpa only [hp,zero_pow (by norm_num : 4≠0),mul_zero] using
          hc.continuousAt (x := p) |>.tendsto)
    · split_ifs
      · exact le_rfl
      · exact div_nonneg (hb z).1 (pow_nonneg z.2.property.1 _)
    · split_ifs with he
      · simp [he]
      · apply (div_le_iff₀ (pow_pos (lt_of_le_of_ne z.2.property.1 (Ne.symm he)) 3)).mpr
        calc
          _ ≤ B z.1*(z.2:ℝ)^7 := (hb z).2
          _ = _ := by ring
  · have hnear : ∀ᶠ z : X × Icc (0:ℝ) 1 in 𝓝 p, (z.2:ℝ)≠0 :=
      ht.continuousAt.eventually_ne hp
    apply ContinuousAt.congr_of_eventuallyEq
      (hf.continuousAt.div (ht.pow 3).continuousAt (pow_ne_zero _ hp))
    filter_upwards [hnear] with z hz
    exact ite_eq_right hz

 /--
Exact identity `(t^3)^(7/3:ℝ)=t^7`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_joint_bound` rewrites with
this identity to prove the bound `0≤N.defect p.1.property s p.2 ∧
N.defect p.1.property s p.2≤N.calibration.defectConstant p.1 s*(p.2:ℝ)^7`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem cube_rpow_seven_thirds {t : ℝ} (ht : 0≤t) : (t^3)^(7/3:ℝ)=t^7 := by
  rw [← Real.rpow_natCast t 3,← Real.rpow_mul ht]
  norm_num

end
end «2610.05164v2».Calculus
