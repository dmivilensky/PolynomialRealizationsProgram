import jacobi.Bessel.Differential
import Mathlib.Analysis.Analytic.Order

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The actual normalized entire function is not locally zero anywhere.
Its zeros are isolated and finite in every compact set. The differential
equation and analytic orders prove that every actual complex zero is simple.
Source: the identity theorem and the standard ordinary-point uniqueness
argument for a second-order analytic differential equation.
Use: excludes infinite vanishing order and accumulation of its genuine zeros.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The normalized Bessel function cannot vanish identically in any complex neighborhood.
Use: excludes infinite vanishing order and accumulation of its genuine zeros.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: local vanishing would extend to the connected complex plane by
the identity theorem, contradicting its actual central value one. -/
theorem normalized_not_locally_zero {a : ℂ} (ha : -1<a.re) (z : ℂ) :
    ¬∀ᶠ w in 𝓝 z,normalized a w=0 := by
  -- Nontriviality is established for the actual globally defined function.
  intro hz
  have h : AnalyticOnNhd ℂ (normalized a) univ := fun w _ => normalized_analytic a w
  have hh := h.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) hz
  have h0 := hh (mem_univ (0:ℂ))
  rw [normalized_zero ha] at h0
  exact one_ne_zero h0

/-- The actual normalized Bessel function has finite analytic vanishing order at every point.
Use: the Bessel equation can compare the orders of its genuine first and second derivatives.
Article: jacobi, Theorem 2.1.
Proof: infinite analytic order is equivalent to local vanishing, already excluded by normalization. -/
theorem normalized_order_ne_top {a : ℂ} (ha : -1<a.re) (z : ℂ) :
    analyticOrderAt (normalized a) z≠⊤ := by
  intro h
  exact normalized_not_locally_zero ha z (analyticOrderAt_eq_top.mp h)

/-- Every point has a punctured complex neighborhood free of actual normalized Bessel zeros.
Use: establishes local discreteness before enumeration of positive spectral zeros.
Article: jacobi, Theorem 2.1.
Proof: the analytic isolated-zero dichotomy has no identically zero
alternative because the entire function takes value one at zero. -/
theorem normalized_isolated {a : ℂ} (ha : -1<a.re) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z,normalized a w≠0 :=
  (normalized_analytic a z).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (normalized_not_locally_zero ha z)

/-- There are only finitely many actual normalized Bessel zeros in every complex compact set.
Use: permits spectral zero enumeration without hidden finite-accumulation assumptions.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: each point has a zero-free punctured neighborhood. The complement
of the zero set is therefore codiscrete within the compact set, whose
omitted subset is finite by compactness. -/
theorem normalized_zeros_finite {a : ℂ} (ha : -1<a.re) {K : Set ℂ} (hK : IsCompact K) :
    (K∩{z | normalized a z=0}).Finite := by
  -- This conclusion applies to the actual complex zero set, not an assumed zero sequence.
  have h : {z | normalized a z≠0}∈codiscreteWithin K := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro z _
    exact mem_of_superset (normalized_isolated ha z) (fun _ hw => Or.inl hw)
  simpa only [sdiff_eq,compl_ofPred,not_not] using hK.finite_sdiff_of_mem_codiscreteWithin h

/-- Every zero of the actual normalized Bessel function is simple in the complex spectral variable.
Use: supplies genuine simple zeros for later enumeration, perturbation and spectral identification.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the origin is not a zero. At any other zero the Bessel equation
expresses F'' as an analytic combination of F' and F. If F' also vanished,
finite analytic orders and differentiation would force order(F')+1
to be at most order(F'), a contradiction. -/
theorem normalized_zero_simple {a z : ℂ} (ha : -1<a.re) (hz : normalized a z=0) :
    deriv (normalized a) z≠0 := by
  -- The nonzero leading differential coefficient makes every zero an ordinary point.
  have hz0 : z≠0 := by intro h; rw [h,normalized_zero ha] at hz; exact one_ne_zero hz
  have hF := normalized_analytic a z
  have hF1 := hF.deriv
  intro hzero
  let A := fun w : ℂ => -(a+1)/w
  let B := fun w : ℂ => -1/(4*w)
  have hA : AnalyticAt ℂ A z := by dsimp [A]; fun_prop (disch := exact hz0)
  have hB : AnalyticAt ℂ B z := by
    have h4z : (4:ℂ)*z≠0 := mul_ne_zero (by norm_num) hz0
    dsimp [B]
    fun_prop (disch := assumption)
  have he : deriv (deriv (normalized a))=ᶠ[𝓝 z]
      A*deriv (normalized a)+B*normalized a := by
    filter_upwards [(continuousAt_id : ContinuousAt (fun w : ℂ => w) z).eventually_ne hz0] with w hw
    change w≠0 at hw
    have h := normalized_equation ha w
    dsimp only [A,B,Pi.add_apply,Pi.mul_apply]
    field_simp [hw]
    linear_combination h
  have h1 : analyticOrderAt (deriv (normalized a)) z+1=analyticOrderAt (normalized a) z := by
    simpa only [hz,sub_zero] using hF.analyticOrderAt_deriv_add_one
  have h2 : analyticOrderAt (deriv (deriv (normalized a))) z+1=
      analyticOrderAt (deriv (normalized a)) z := by
    simpa only [hzero,sub_zero] using hF1.analyticOrderAt_deriv_add_one
  have hle1 : analyticOrderAt (deriv (normalized a)) z≤
      analyticOrderAt (A*deriv (normalized a)) z := by
    rw [analyticOrderAt_mul hA hF1]
    exact le_add_of_nonneg_left zero_le
  have hle2 : analyticOrderAt (normalized a) z≤analyticOrderAt (B*normalized a) z := by
    rw [analyticOrderAt_mul hB hF]
    exact le_add_of_nonneg_left zero_le
  have hle := (min_le_min hle1 hle2).trans
    (le_analyticOrderAt_add (f := A*deriv (normalized a)) (g := B*normalized a))
  rw [← analyticOrderAt_congr he,← h1] at hle
  have hm : analyticOrderAt (deriv (normalized a)) z≤analyticOrderAt (deriv (normalized a)) z+1 := le_self_add
  rw [min_eq_left hm] at hle
  have hbad : analyticOrderAt (deriv (normalized a)) z+1≤
      analyticOrderAt (deriv (deriv (normalized a))) z+1 := by
    simpa only [add_comm] using add_le_add_right hle 1
  rw [h2] at hbad
  cases hq : analyticOrderAt (deriv (normalized a)) z with
  | top =>
    have htop : analyticOrderAt (normalized a) z=⊤ := by simpa only [hq,top_add] using h1.symm
    exact normalized_order_ne_top ha z htop
  | coe n =>
    rw [hq] at hbad
    have hh : ¬((n:ℕ∞)+1≤n) := by exact_mod_cast Nat.not_succ_le_self n
    exact hh hbad

end
end jacobi.Bessel
