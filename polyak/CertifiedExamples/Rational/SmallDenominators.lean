import polyak.CertifiedExamples.Rational.Gaps
import polyak.Farey.Examples.SingleHarmonic
import polyak.General.Regions.TongueCriteria

/-! Exact exclusion of all four primitive frequencies below denominator six.
The phase floor then excludes every remaining finite or irrational harmonic. -/
noncomputable section
namespace polyak.CertifiedExamples.Rational
open polyak.Farey.Examples polyak.Levels

private theorem thirteen_Xi_negative_left {c:ℝ} (hc:c≤-(1:ℝ)/2) :
    thirteenTuning.Xi c<0 := by
  rw [←thirteen_Xi_source_exact]
  norm_num [thirteenXiSource]
  have hsq : (1:ℝ)/4≤c^2 := by nlinarith
  nlinarith

private theorem angle_gt_half_pi_of_Xi_negative (q:General.Tuning) {ω:ℝ}
    (hω:ω∈Set.Ioo 0 Real.pi) (hXi:q.Xi (Real.cos ω)<0) : Real.pi/2<q.angle ω := by
  have ht:=General.Regions.angle_le_iff_Xi q hω
    (show Real.pi/2∈Set.Ioo (0:ℝ) Real.pi from ⟨by positivity,by linarith [Real.pi_pos]⟩)
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,zero_div,zero_mul] at ht
  exact lt_of_not_ge (fun hn=>not_le_of_gt hXi (ht.mp hn))

private theorem thirteen_small_three : Real.pi/3<thirteenTuning.angle (2*Real.pi/3) := by
  have hω : 2*Real.pi/3∈Set.Ioo (0:ℝ) Real.pi := ⟨by positivity,by linarith [Real.pi_pos]⟩
  have hx : thirteenTuning.Xi (Real.cos (2*Real.pi/3))<0 := by
    apply thirteen_Xi_negative_left
    rw [show Real.cos (2*Real.pi/3)=-(1:ℝ)/2 by
      rw [show 2*Real.pi/3=2*(Real.pi/3) by ring,Real.cos_two_mul,Real.cos_pi_div_three]; norm_num]
  have hh:=angle_gt_half_pi_of_Xi_negative thirteenTuning hω hx
  linarith [Real.pi_pos]

private theorem thirteen_small_four : Real.pi/4<thirteenTuning.angle (2*Real.pi/4) :=
  thirteen_in_gap_four.2.2.2.1

private theorem thirteen_small_five_one : Real.pi/5<thirteenTuning.angle (2*Real.pi/5) := by
  convert thirteen_in_gap_four.2.2.2.2 using 1 <;> norm_num

private theorem thirteen_small_five_two : Real.pi/5<thirteenTuning.angle (2*Real.pi*2/5) := by
  have hω : 2*Real.pi*2/5∈Set.Ioo (0:ℝ) Real.pi := ⟨by positivity,by linarith [Real.pi_pos]⟩
  have hx : thirteenTuning.Xi (Real.cos (2*Real.pi*2/5))<0 := by
    apply thirteen_Xi_negative_left
    have h:=Real.strictAntiOn_cos
      (show 2*Real.pi/3∈Set.Icc (0:ℝ) Real.pi from ⟨by positivity,by linarith [Real.pi_pos]⟩)
      (show 2*Real.pi*2/5∈Set.Icc (0:ℝ) Real.pi from ⟨hω.1.le,hω.2.le⟩)
      (show 2*Real.pi/3<2*Real.pi*2/5 by linarith [Real.pi_pos])
    rw [show Real.cos (2*Real.pi/3)=-(1:ℝ)/2 by
      rw [show 2*Real.pi/3=2*(Real.pi/3) by ring,Real.cos_two_mul,Real.cos_pi_div_three]; norm_num] at h
    exact h.le
  have hh:=angle_gt_half_pi_of_Xi_negative thirteenTuning hω hx
  linarith [Real.pi_pos]

theorem thirteen_small_denominators : SmallDenominatorChecks (tuningCurve thirteenTuning) := by
  intro j k hj hjk ω hω
  have hcases : (j.val=1 ∧ k.val=3) ∨ (j.val=1 ∧ k.val=4) ∨
      (j.val=1 ∧ k.val=5) ∨ (j.val=2 ∧ k.val=5) := by omega
  change Real.pi/(k.val:ℝ)<thirteenTuning.angle (ω:ℝ)
  rw [hω]
  rcases hcases with h|h|h|h
  · simpa only [h.1,h.2,Nat.cast_one,Nat.cast_ofNat,mul_one] using thirteen_small_three
  · simpa only [h.1,h.2,Nat.cast_one,Nat.cast_ofNat,mul_one] using thirteen_small_four
  · simpa only [h.1,h.2,Nat.cast_one,Nat.cast_ofNat,mul_one] using thirteen_small_five_one
  · simpa only [h.1,h.2,Nat.cast_ofNat] using thirteen_small_five_two

end polyak.CertifiedExamples.Rational
