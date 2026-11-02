import jacobi.Hankel.SineDiskBounds

/-!
Article: jacobi, Lemma E.1.
These estimates turn the actual zero-disk equation into the
uniform refined cubic frequency displacement.
Use: the refined Bessel zero displacement retains the cubic error in replacing sin(zeta) by zeta.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The original small complex sine increment has a cubic bound throughout the genuine radius-one-quarter disk.
Use: the refined Bessel zero displacement retains the cubic error in replacing sin(zeta) by zeta.
Article: jacobi, Lemma E.1.
Source: Mathlib Complex.sin_bound, the Taylor remainder through degree three.
Proof: the actual degree-five remainder and the true cubic Taylor term sum to at most one times the displacement cubed on the original disk. -/
theorem sine_quarter_cubic {ζ : ℂ} (hζ : ‖ζ‖≤1/4) :
    ‖Complex.sin ζ-ζ‖≤‖ζ‖^3 := by
  -- The actual community Taylor bound is used at the same original complex displacement.
  have hh := Complex.sin_bound (hζ.trans (by norm_num : (1/4:ℝ)≤1))
  have he : Complex.sin ζ-ζ=(Complex.sin ζ-(ζ-ζ^3/6))-ζ^3/6 := by ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have hn : ‖ζ^3/(6:ℂ)‖=‖ζ‖^3/6 := by rw [norm_div,norm_pow]; norm_num
  rw [hn]
  have hsq : ‖ζ‖^2≤1 := (pow_le_pow_left₀ (norm_nonneg _) (hζ.trans (by norm_num : (1/4:ℝ)≤1)) 2).trans_eq (by norm_num)
  have hpow : ‖ζ‖^5≤‖ζ‖^3 := by nlinarith [mul_le_mul_of_nonneg_right hsq (pow_nonneg (norm_nonneg ζ) 3)]
  nlinarith [pow_nonneg (norm_nonneg ζ) 3]

/-- The original small complex cosine increment has a quadratic bound with constant one throughout the genuine radius-one-quarter disk.
Use: the true first inverse-frequency cosine correction contributes only cubically to the refined Bessel zero displacement.
Article: jacobi, Lemma E.1.
Source: Mathlib Complex.cos_bound.
Proof: sum the genuine quadratic Taylor term and the community fourth-order remainder; the actual displacement norm is at most one. -/
theorem cosine_quarter_quadratic {ζ : ℂ} (hζ : ‖ζ‖≤1/4) :
    ‖Complex.cos ζ-1‖≤‖ζ‖^2 := by
  -- The genuine quadratic rate, rather than only a uniform disk bound, is retained here.
  have hh := Complex.cos_bound (hζ.trans (by norm_num : (1/4:ℝ)≤1))
  have he : Complex.cos ζ-1=(Complex.cos ζ-(1-ζ^2/2))-ζ^2/2 := by ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have hn : ‖ζ^2/(2:ℂ)‖=‖ζ‖^2/2 := by rw [norm_div,norm_pow]; norm_num
  rw [hn]
  have hsq : ‖ζ‖^2≤1 := (pow_le_pow_left₀ (norm_nonneg _) (hζ.trans (by norm_num : (1/4:ℝ)≤1)) 2).trans_eq (by norm_num)
  have hpow : ‖ζ‖^4≤‖ζ‖^2 := by nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖ζ‖)]
  nlinarith [sq_nonneg ‖ζ‖]

/-- The genuine small complex sine is bounded above by twice its actual displacement and below by half that displacement on the original zero disk.
Use: the actual Bessel zero equation first gives an inverse-index displacement, before its cubic correction is estimated.
Article: jacobi, Lemma E.1.
Proof: the cubic Taylor bound is at most one half times the actual displacement on the radius-one-quarter disk. The two complex norm triangle inequalities give the stated upper and lower bounds. -/
theorem sine_quarter_linear {ζ : ℂ} (hζ : ‖ζ‖≤1/4) :
    ‖ζ‖≤2*‖Complex.sin ζ‖ ∧ ‖Complex.sin ζ‖≤2*‖ζ‖ := by
  -- The actual cubic sine error is absorbed by half the original displacement.
  have hh := sine_quarter_cubic hζ
  have hsq : ‖ζ‖^2≤1/2 := (pow_le_pow_left₀ (norm_nonneg _) hζ 2).trans (by norm_num)
  have h3 : ‖ζ‖^3≤‖ζ‖/2 := by nlinarith [mul_le_mul_of_nonneg_right hsq (norm_nonneg ζ)]
  have ht := norm_le_norm_sub_add (Complex.sin ζ) ζ
  have ht' := norm_le_norm_sub_add ζ (Complex.sin ζ)
  rw [norm_sub_rev ζ (Complex.sin ζ)] at ht'
  constructor <;> linarith

end
end jacobi.Hankel
