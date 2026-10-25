import LeanCert.Core.IntervalRat.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: Appendix B, certified residual bounds on a whole parameter slab.
Use: enclose f(s) by its rational-center enclosure and an interval derivative bound.
Proof: the ordinary real mean value theorem, for both orders of the endpoints.
-/

namespace polyak.Numerics.Parametric
noncomputable section
open Set LeanCert.Core

/-- Article: an interval enclosure of the parameter derivative bounds the whole residual.
The center is rational, but every parameter and mean-value point is a real number. -/
theorem meanValue_enclosure {f : ℝ → ℝ} {I A J : IntervalRat} {a : ℚ}
    (ha : (a : ℝ)∈I) (hfa : f a∈A)
    (hf : DifferentiableOn ℝ f (Icc (I.lo : ℝ) I.hi))
    (hderiv : ∀ r : ℝ, r∈I → deriv f r∈J) {s : ℝ} (hs : s∈I) :
    f s∈IntervalRat.add A (IntervalRat.mul (IntervalRat.sub I (IntervalRat.singleton a)) J) := by
  have hsub := IntervalRat.mem_sub hs (IntervalRat.mem_singleton a)
  by_cases he : s=(a : ℝ)
  · have hzero : (0 : ℝ)∈IntervalRat.sub I (IntervalRat.singleton a) := by
      simpa only [sub_self] using IntervalRat.mem_sub ha (IntervalRat.mem_singleton a)
    have hj := hderiv a ha
    have hh := IntervalRat.mem_add hfa (IntervalRat.mem_mul hzero hj)
    simpa only [he,zero_mul,add_zero] using hh
  have hseg : Icc (min (a : ℝ) s) (max (a : ℝ) s) ⊆ Icc (I.lo : ℝ) I.hi := by
    intro r hr
    exact ⟨le_trans (le_min ha.1 hs.1) hr.1,le_trans hr.2 (max_le ha.2 hs.2)⟩
  have hc : ∃ r : ℝ, r∈I ∧ f s=f a+(s-a)*deriv f r := by
    rcases lt_or_gt_of_ne he with hlt | hgt
    · obtain ⟨r,hr,heq⟩ := exists_deriv_eq_slope f hlt
        (hf.continuousOn.mono (by simpa only [min_eq_right hlt.le,max_eq_left hlt.le] using hseg))
        (hf.mono (Ioo_subset_Icc_self.trans (by
          simpa only [min_eq_right hlt.le,max_eq_left hlt.le] using hseg)))
      refine ⟨r,⟨le_trans hs.1 hr.1.le,le_trans hr.2.le ha.2⟩,?_⟩
      have hne : (a : ℝ)-s≠0 := sub_ne_zero.mpr (ne_of_gt hlt)
      have hh := (eq_div_iff hne).mp heq
      nlinarith
    · obtain ⟨r,hr,heq⟩ := exists_deriv_eq_slope f hgt
        (hf.continuousOn.mono (by simpa only [min_eq_left hgt.le,max_eq_right hgt.le] using hseg))
        (hf.mono (Ioo_subset_Icc_self.trans (by
          simpa only [min_eq_left hgt.le,max_eq_right hgt.le] using hseg)))
      refine ⟨r,⟨le_trans ha.1 hr.1.le,le_trans hr.2.le hs.2⟩,?_⟩
      have hne : s-(a : ℝ)≠0 := sub_ne_zero.mpr (ne_of_gt hgt)
      have hh := (eq_div_iff hne).mp heq
      nlinarith
  obtain ⟨r,hr,heq⟩ := hc
  rw [heq]
  exact IntervalRat.mem_add hfa (IntervalRat.mem_mul hsub (hderiv r hr))

end
end polyak.Numerics.Parametric
