import chebyshev2.Calculus.ClosedInterval
import Mathlib.Topology.Piecewise

/-!
Article: chebyshev2, Lemma 16.
C1 extension by zero for a closed-interval function with vanishing value and derivative at both
endpoints.
Use: `chebyshev2.Calculus.zeroExtension_c1` feeds
`chebyshev2.DualCertificate.PolynomialPotential.centering_c1` (centering c1).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_analytic` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
noncomputable section
open Set Filter
open scoped Topology
set_option autoImplicit false

/--
Defines `zeroExtension` of type `ℝ → ℝ` by `(Icc a b).indicator f`.

Use: `chebyshev2.Calculus.zeroExtension_c1` rewrites with this definition to establish
smoothness to the stated order: `ContDiff ℝ 1 (zeroExtension a b f)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.
-/
def zeroExtension (a b : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := (Icc a b).indicator f

/--
Continuity of the displayed function: `Continuous (zeroExtension a b f)`.

Use: `chebyshev2.Calculus.zeroExtension_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (zeroExtension a b f)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem zeroExtension_continuous {a b : ℝ} (hab : a<b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : f a=0) (hb : f b=0) :
    Continuous (zeroExtension a b f) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  classical
  let : ∀ x : ℝ, Decidable (x∈Icc a b) := Classical.decPred _
  apply continuous_piecewise _ (by simpa only [isClosed_Icc.closure_eq] using hf) continuousOn_const
  intro x hx
  rw [frontier_Icc hab.le] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

/--
The actual derivative at the stated point: `HasDerivAt (zeroExtension a b f) (zeroExtension a b
g x) x`.

Use: `chebyshev2.Calculus.zeroExtension_c1` uses this derivative formula to establish
smoothness to the stated order: `ContDiff ℝ 1 (zeroExtension a b f)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Separate `x∈Icc a b` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem zeroExtension_hasDerivAt {a b : ℝ} (hab : a<b) {f g : ℝ → ℝ}
    (hd : ∀ x∈Icc a b, HasDerivWithinAt f (g x) (Icc a b) x)
    (ha : f a=0) (hb : f b=0) (hga : g a=0) (hgb : g b=0) (x : ℝ) :
    HasDerivAt (zeroExtension a b f) (zeroExtension a b g x) x := by
  -- Separate `x∈Icc a b` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hin : x∈Icc a b
  · have hvalue : zeroExtension a b f x=f x := indicator_of_mem hin f
    have hderiv : zeroExtension a b g x=g x := indicator_of_mem hin g
    rw [hderiv]
    have hinside := (hd x hin).congr (fun z hz => indicator_of_mem hz f) hvalue
    by_cases he : x=a ∨ x=b
    · have hfzero : f x=0 := by rcases he with rfl | rfl <;> assumption
      have hgzero : g x=0 := by rcases he with rfl | rfl <;> assumption
      have hout : HasDerivWithinAt (zeroExtension a b f) 0 (Icc a b)ᶜ x :=
        (hasDerivWithinAt_const x (Icc a b)ᶜ (0:ℝ)).congr
          (fun z hz => indicator_of_notMem hz f) (hvalue.trans hfzero)
      rw [hgzero] at hinside ⊢
      have hu : HasDerivWithinAt (zeroExtension a b f) 0 univ x := by
        have huni := hinside.union hout
        rw [union_compl_self] at huni
        convert! huni using 1
      convert! hu.hasDerivAt Filter.univ_mem using 1
    · exact hinside.hasDerivAt (Icc_mem_nhds
        (lt_of_le_of_ne hin.1 (Ne.symm (fun heq => he (Or.inl heq))))
        (lt_of_le_of_ne hin.2 (fun heq => he (Or.inr heq))))
  · rw [show zeroExtension a b g x=0 from indicator_of_notMem hin g]
    apply (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hin] with z hz
    exact indicator_of_notMem hz f

/--
Smoothness to the stated order: `ContDiff ℝ 1 (zeroExtension a b f)`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.centering_c1` uses this assertion to
establish smoothness to the stated order: `ContDiff ℝ 1 (P.centering N hκ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem zeroExtension_c1 {a b : ℝ} (hab : a<b) {f g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x∈Icc a b, HasDerivWithinAt f (g x) (Icc a b) x)
    (ha : f a=0) (hb : f b=0) (hga : g a=0) (hgb : g b=0) :
    ContDiff ℝ 1 (zeroExtension a b f) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have h := zeroExtension_hasDerivAt hab hd ha hb hga hgb
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (h x).differentiableAt,?_⟩
  rw [show deriv (zeroExtension a b f)=zeroExtension a b g from funext (fun x => (h x).deriv)]
  exact zeroExtension_continuous hab hg hga hgb

end
end chebyshev2.Calculus
