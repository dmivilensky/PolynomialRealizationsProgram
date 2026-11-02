import jacobi.Variational.MultiplierRule
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
The actual positive-part multiplier equation with a positive continuous
even strictly decreasing gradient determines the density's positive set.
With zero mass multiplier it is the full line. With a positive multiplier
it is a finite centered open interval. The common argument serves both
actual moment gradients and does not add any assumed profile regularity.
Source: the intermediate value theorem and strict half-line monotonicity.
Use: turns the proved a.e. multiplier equation into the interval support asserted for the original measurable optimizer.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual density's positive set is exactly the positive superlevel set of its KKT coefficient, modulo null sets.
Use: turns the proved a.e. multiplier equation into the interval support asserted for the original measurable optimizer.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the square root is positive exactly when the nonnegative density is
positive, and the positive scalar times max(c,0) is positive exactly when c>0. -/
theorem kkt_positive_set (m : Density) (c : ℝ → ℝ)
    (he : (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (c x) 0) :
    ∀ᵐ x : ℝ,0<m.value x ↔ 0<c x := by
  -- The assertion concerns the original measurable density at every retained a.e. point.
  filter_upwards [he] with x hx
  rw [← sqrt_pos, hx]
  constructor
  · intro hp
    have hh : 0<max (c x) 0 := (mul_pos_iff_of_pos_left (by norm_num : (0:ℝ)<2/3)).mp hp
    exact (lt_max_iff.mp hh).resolve_right (lt_irrefl 0)
  · intro hp
    rw [max_eq_left hp.le]
    positivity

/-- A nonzero actual KKT density has a strictly positive coefficient at the center of its radial profile.
Use: supplies the positive endpoint required to locate a finite free boundary.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: if the even nonincreasing coefficient were nonpositive at zero, it
would be nonpositive everywhere, making the original density zero a.e. and contradicting positive mass. -/
theorem kkt_center_pos (m : Density) (hm : 0<m.mass) (c : ℝ → ℝ)
    (heven : ∀ x,c (-x)=c x) (hanti : AntitoneOn c (Ici 0))
    (he : (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (c x) 0) : 0<c 0 := by
  -- Evenness compares every actual point with its nonnegative radius.
  by_contra! hn
  have hnon (x : ℝ) : c x≤0 := by
    have habs : c |x|=c x := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx,heven]
    rw [← habs]
    exact (hanti (by simp) (abs_nonneg x) (abs_nonneg x)).trans hn
  have hz : m.value=ᵐ[volume] 0 := by
    filter_upwards [he] with x hx
    rw [max_eq_right (hnon x),mul_zero] at hx
    exact le_antisymm (sqrt_eq_zero'.mp hx) (m.nonneg x)
  have hmass : m.mass=0 := by simpa only [Density.mass,Pi.zero_apply,integral_zero] using integral_congr_ae hz
  exact hm.ne' hmass

/-- The complete interval-support conclusion of the actual positive-part multiplier equation.
Use: gives both single-moment optimizer supports once their actual gradients' strict radial shape is proved.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the zero mass multiplier leaves the positive gradient everywhere.
Otherwise the coefficient starts positive, strictly decreases, and tends
to a negative limit. Its unique zero gives the finite centered positive interval. -/
theorem kkt_radial_support (m : Density) (hm : 0<m.mass) (γ : ℝ → ℝ)
    (hγc : Continuous γ) (hγp : ∀ x,0<γ x) (hγe : ∀ x,γ (-x)=γ x)
    (hγanti : StrictAntiOn γ (Ici 0)) (hlim : Tendsto γ atTop (𝓝 0))
    {μ l : ℝ} (hμ : 0<μ) (hl : 0≤l)
    (he : (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (μ*γ x-l) 0) :
    (l=0 ∧ ∀ᵐ x : ℝ,0<m.value x) ∨
      (0<l ∧ ∃ a : ℝ,0<a ∧ ∀ᵐ x : ℝ,(0<m.value x ↔ |x|<a)) := by
  -- The two mass-multiplier branches cover every actual constrained minimizer.
  have hset := kkt_positive_set m (fun x => μ*γ x-l) he
  by_cases hl0 : l=0
  · left
    refine ⟨hl0,hset.mono fun x hx => hx.mpr ?_⟩
    rw [hl0,sub_zero]
    exact mul_pos hμ (hγp x)
  · right
    have hlp : 0<l := lt_of_le_of_ne hl (Ne.symm hl0)
    let c (x : ℝ) := μ*γ x-l
    have hc : Continuous c := (hγc.const_mul μ).sub continuous_const
    have hanti : StrictAntiOn c (Ici 0) := by
      intro x hx y hy hxy
      dsimp only [c]
      exact sub_lt_sub_right (mul_lt_mul_of_pos_left (hγanti hx hy hxy) hμ) l
    have heven (x : ℝ) : c (-x)=c x := by dsimp only [c]; rw [hγe]
    have h0 : 0<c 0 := kkt_center_pos m hm c heven hanti.antitoneOn he
    have ht : Tendsto c atTop (𝓝 (-l)) := by simpa only [mul_zero,zero_sub] using (hlim.const_mul μ).sub_const l
    have hneg := ht.eventually (Iio_mem_nhds (neg_neg_of_pos hlp))
    obtain ⟨R,hR,hcR⟩ := ((eventually_gt_atTop (0:ℝ)).and hneg).exists
    obtain ⟨a,ha,hzero⟩ := (intermediate_value_Icc' hR.le hc.continuousOn) ⟨hcR.le,h0.le⟩
    have hap : 0<a := lt_of_le_of_ne ha.1 (by intro hz; rw [← hz] at hzero; exact h0.ne' hzero)
    have hshape (x : ℝ) : 0<c x ↔ |x|<a := by
      have habs : c |x|=c x := by
        rcases le_total 0 x with hx | hx
        · rw [abs_of_nonneg hx]
        · rw [abs_of_nonpos hx,heven]
      rw [← habs]
      constructor
      · intro hp
        by_contra! hx
        have hh := hanti.antitoneOn hap.le (abs_nonneg x) hx
        rw [hzero] at hh
        linarith
      · intro hx
        have hh := hanti (abs_nonneg x) hap.le hx
        rwa [hzero] at hh
    exact ⟨hlp,a,hap,hset.mono fun x hx => hx.trans (hshape x)⟩

end
end jacobi.Variational
