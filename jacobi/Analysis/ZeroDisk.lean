import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
Article: jacobi, Lemma E.1.
Use: the complex Bessel frequency disks use this quantitative construction in place of a separate formalization of Rouche's theorem.
-/
namespace jacobi.Analysis
noncomputable section
open Set Metric Function
set_option backward.isDefEq.respectTransparency false

/-- An actual complex function whose derivative stays within one half of one has a unique simple zero in a closed disk, provided its center value is sufficiently small.
Use: the complex Bessel frequency disks use this quantitative construction in place of a separate formalization of Rouche's theorem.
Article: jacobi, Lemma E.1.
Source: Banach's fixed-point theorem and the convex mean-value inequality.
Proof: the true map z-f(z) contracts the complete disk by one half and maps it into itself. Its unique fixed point is the required zero; its distance from zero is at most twice the center residual. The derivative bound excludes a vanishing derivative. -/
theorem unique_simple_zero_disk {f f' : ℂ → ℂ} {r : ℝ} (hr : 0≤r)
    (hd : ∀ z∈closedBall (0:ℂ) r,HasDerivAt f (f' z) z)
    (hb : ∀ z∈closedBall (0:ℂ) r,‖1-f' z‖≤1/2)
    (h0 : ‖f 0‖≤r/2) :
    ∃ z : ℂ,‖z‖≤r ∧ f z=0 ∧ ‖z‖≤2*‖f 0‖ ∧ f' z≠0 ∧
      ∀ w : ℂ,‖w‖≤r → f w=0 → w=z := by
  -- The complete disk and actual derivative inequality give a genuine contraction, not an assumed root certificate.
  let G (z : ℂ) := z-f z
  let s : Set ℂ := closedBall 0 r
  have hder (z : ℂ) (hz : z∈s) : HasDerivWithinAt G (1-f' z) s z :=
    ((hasDerivAt_id z).sub (hd z hz)).hasDerivWithinAt
  have hLip : LipschitzOnWith (1/2:NNReal) G s :=
    (convex_closedBall (0:ℂ) r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hder
      (fun z hz => by exact_mod_cast hb z hz)
  have hcenter : (0:ℂ)∈s := by simpa only [s,mem_closedBall,dist_self] using hr
  have hmaps : MapsTo G s s := by
    intro z hz
    have hh := hLip.norm_sub_le hz hcenter
    have hG0 : ‖G 0‖=‖f 0‖ := by simp [G]
    have hnorm : ‖z‖≤r := by simpa only [s,mem_closedBall,dist_zero_right] using hz
    have htriangle := norm_le_norm_sub_add (G z) (G 0)
    rw [hG0] at htriangle
    simp only [sub_zero,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hh
    change dist (G z) 0≤r
    rw [dist_zero_right]
    linarith
  let g : s → s := hmaps.restrict G s s
  have hcontract : ContractingWith (1/2:NNReal) g := ⟨by norm_num,hLip.mapsToRestrict hmaps⟩
  let : CompleteSpace s := isClosed_closedBall.completeSpace_coe
  let : Nonempty s := ⟨⟨0,hcenter⟩⟩
  let z : s := hcontract.fixedPoint g
  have hfixed : G z=z := congrArg Subtype.val hcontract.fixedPoint_isFixedPt
  have hzero : f z=0 := by dsimp [G] at hfixed; linear_combination -hfixed
  have hz : ‖(z:ℂ)‖≤r := by simpa only [s,mem_closedBall,dist_zero_right] using z.property
  have hsize := hcontract.dist_fixedPoint_le (⟨0,hcenter⟩:s)
  have hsmall : ‖(z:ℂ)‖≤2*‖f 0‖ := by
    change dist (0:ℂ) (z:ℂ)≤dist (0:ℂ) (G 0)/(1-((1/2:NNReal):ℝ)) at hsize
    norm_num [G,dist_eq_norm,norm_neg] at hsize
    linarith
  have hsimple : f' z≠0 := by
    intro he
    have hh := hb z z.property
    rw [he,sub_zero,norm_one] at hh
    norm_num at hh
  refine ⟨z,hz,hzero,hsmall,hsimple,fun w hw he => ?_⟩
  have hwmem : w∈s := by simpa only [s,mem_closedBall,dist_zero_right] using hw
  have hwfix : IsFixedPt g (⟨w,hwmem⟩:s) := by apply Subtype.ext; change w-f w=w; rw [he,sub_zero]
  exact congrArg Subtype.val (hcontract.fixedPoint_unique hwfix)

end
end jacobi.Analysis
