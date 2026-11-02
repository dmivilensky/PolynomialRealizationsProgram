import jacobi.Variational.Semicontinuity
import jacobi.Variational.SpectralOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
Article: jacobi, Lemma D.1.
A common energy bound provides the integrable |x|^(-2/3) majorant on compact
intervals. Thus any already extracted almost-everywhere convergent sequence
of symmetric decreasing densities converges locally in L1. The subsequence
extraction is proved in Compactness; this module supplies its local L1 step.
Source: Lebesgue dominated convergence and integrability of subcritical powers.
Use: rewrites the article's majorant as a constant times |x|^(-2/3).
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The energy-tail majorant in a form suitable for local integration.
Use: rewrites the article's majorant as a constant times |x|^(-2/3).
Article: jacobi, Lemma D.1.
Proof: distribute positive real powers over division and use the negative-exponent identity. -/
theorem energy_majorant_eq {E : ℝ} (hE : 0 ≤ E) (x : ℝ) :
    (E/(2*|x|))^(2/3 : ℝ) = (E/2)^(2/3 : ℝ)*|x|^(-(2/3 : ℝ)) := by
  rw [← div_div,Real.div_rpow (by positivity) (abs_nonneg x),Real.rpow_neg (abs_nonneg x),div_eq_mul_inv]

/-- The universal energy majorant is integrable on every compact centered interval.
Use: licenses dominated convergence near the possible density singularity at zero.
Article: jacobi, Lemma D.1.
Proof: the exponent 2/3 is smaller than the dimension one, so use mathlib's
proved local integrability theorem for power singularities. -/
theorem energy_majorant_integrableOn {E : ℝ} (hE : 0 ≤ E) (R : ℝ) :
    IntegrableOn (fun x : ℝ => (E/(2*|x|))^(2/3 : ℝ)) (Icc (-R) R) := by
  -- The value at zero is harmless: real powers give a finite representative on a null set.
  simp_rw [energy_majorant_eq hE]
  have hm : Measurable (fun x : ℝ => (E/2)^(2/3 : ℝ)*|x|^(-(2/3 : ℝ))) := by fun_prop
  have hi : LocallyIntegrable (fun x : ℝ => (E/2)^(2/3 : ℝ)*|x|^(-(2/3 : ℝ))) := by
    apply locallyIntegrable_of_norm_le_rpow (C := (E/2)^(2/3 : ℝ))
      (α := (2/3 : ℝ)) (by norm_num) (by norm_num) _ hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact hi.integrableOn_isCompact isCompact_Icc

/-- Uniformly energy-bounded symmetric decreasing densities converge locally in L1
whenever they converge almost everywhere.
Use: the analytic convergence step in Compactness before the spectral tails are restored.
Article: jacobi, Lemma D.1.
Proof: dominate the absolute difference by twice the common energy majorant
and apply dominated convergence on the restricted interval measure. -/
theorem local_l1_limit (m : ℕ → Density) (q : Density)
    (hs : ∀ n, SymmetricDecreasing (m n).value) (hqs : SymmetricDecreasing q.value)
    {E : ℝ} (hE : ∀ n, (m n).energy ≤ E) (hqE : q.energy ≤ E)
    (hlim : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x))) (R : ℝ) :
    Tendsto (fun n => ∫ x in Icc (-R) R, |(m n).value x-q.value x|) atTop (𝓝 0) := by
  -- Ignore the singleton zero when applying the pointwise radial bound.
  have hE0 : 0 ≤ E := (m 0).energy_nonneg.trans (hE 0)
  have hzero : ∀ᵐ x : ℝ ∂volume.restrict (Icc (-R) R), x ≠ 0 :=
    ae_restrict_of_ae (by simp [ae_iff])
  have hi := (energy_majorant_integrableOn hE0 R).const_mul 2
  have h := tendsto_integral_of_dominated_convergence
    (F := fun n x => |(m n).value x-q.value x|) (f := fun _ => (0 : ℝ))
    (μ := volume.restrict (Icc (-R) R)) (fun x => 2*(E/(2*|x|))^(2/3 : ℝ))
    (fun n => by simpa only [Real.norm_eq_abs,Pi.sub_apply] using
      ((m n).measurable.sub q.measurable).norm.aestronglyMeasurable) hi
    (fun n => by
      filter_upwards [hzero] with x hx
      rw [Real.norm_eq_abs,abs_abs]
      have h1 := energy_tail (m n) (hs n) (hE n) hx
      have h2 := energy_tail q hqs hqE hx
      exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg ((m n).nonneg x),abs_of_nonneg (q.nonneg x)]
        linarith))
    (by
      filter_upwards [ae_restrict_of_ae hlim] with x hx
      simpa using (hx.sub (tendsto_const_nhds (x := q.value x))).abs)
  simpa only [integral_zero] using h

end
end jacobi.Variational
