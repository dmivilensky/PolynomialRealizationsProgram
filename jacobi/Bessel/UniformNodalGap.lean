import jacobi.Bessel.OrdinaryPhase
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: jacobi, Lemma E.1.
Use: positiveZero_twoStep_gap excludes an additional real Bessel zero between the actual adjacent complex-frequency disks.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The genuine original Bessel phase speed has a uniform norm bound after its explicit restoring threshold.
Use: positiveZero_twoStep_gap excludes an additional real Bessel zero between the actual adjacent complex-frequency disks.
Article: jacobi, Lemma E.1.
Proof: the actual inverse-square coefficient has absolute value at most one half beyond 2*(alpha^2+1), and the true sine square is at most one. Apply the real triangle inequality to the original phase derivative. -/
theorem ordinaryPhase_speed_bound (a theta : ℝ) {x : ℝ} (hx : 2*(a^2+1)≤x) :
    |1+(1/4-a^2)/x^2*sin theta^2|≤3/2 := by
  -- The threshold bounds the genuine source coefficient independently of the original nodal index.
  have hxp : 0<x := by nlinarith [sq_nonneg a]
  have hx1 : 1≤x := by nlinarith [sq_nonneg a]
  have hab : |1/4-a^2|≤a^2+1 := abs_le.mpr ⟨by nlinarith [sq_nonneg a],by nlinarith [sq_nonneg a]⟩
  have hsq : 2*(a^2+1)≤x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx1) hxp.le]
  have hc : |(1/4-a^2)/x^2|≤1/2 := by
    rw [abs_div,abs_of_pos (sq_pos_of_pos hxp)]
    exact (div_le_iff₀ (sq_pos_of_pos hxp)).mpr (by linarith)
  have hh := abs_add_le (1:ℝ) ((1/4-a^2)/x^2*sin theta^2)
  rw [abs_one,abs_mul,abs_sq] at hh
  have hs : sin theta^2≤1 := Real.sin_sq_le_one theta
  nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg ((1/4-a^2)/x^2))]

/-- Two original consecutive Bessel nodal intervals have a uniform lower total length beyond the genuine restoring threshold.
Use: the original roots in adjacent radius-one-quarter phase disks must have consecutive canonical indices, since their total separation is less than pi+one half.
Article: jacobi, Lemma E.1.
Proof: the true ordinary phase advances by exactly two pi between the original kth and (k+2)nd zeros. Its actual derivative has norm at most three halves throughout this interval, so the community mean-value inequality gives the stated nodal length bound. -/
theorem positiveZero_twoStep_gap {a : ℝ} (ha : -1<a) (k : ℕ)
    (hk : 2*(a^2+1)≤positiveZero a ha k) :
    4*Real.pi/3≤positiveZero a ha (k+2)-positiveZero a ha k := by
  -- Exact original phase increments retain the genuine zero indices in the mean-value estimate.
  let x := positiveZero a ha k
  let y := positiveZero a ha (k+2)
  have hx : 0<x := (positiveZero_properties ha k).1
  have hxy : x≤y := (positiveZero_strictMono ha).monotone (by omega)
  have hz := wave_positiveZero_zero ha k
  have hd (t : ℝ) (ht : t∈Icc x y) := ordinaryPhase_hasDerivAt ha hx (hx.trans_le ht.1) hz
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (C := (3/2:ℝ))
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using
      (ordinaryPhase_speed_bound a (ordinaryPhase a ha x t) (hk.trans ht.1)))
    (convex_Icc x y) (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  have hstart : ordinaryPhase a ha x x=0 := (restoringState a ha).phase_self x
  have hfinish := ordinaryPhase_numbered_zero ha k hk 2
  change ordinaryPhase a ha x y=(2:ℝ)*Real.pi at hfinish
  rw [hfinish,hstart,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy),
    abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)] at hh
  change 4*Real.pi/3≤y-x
  linarith

end
end jacobi.Bessel
