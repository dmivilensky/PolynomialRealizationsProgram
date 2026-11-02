import jacobi.Reference.GammaTail
import jacobi.Reference.HalfIntegerCharacteristics

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Euler reflection expresses the actual Delta_tau as its reflected
sine times a genuine Gamma quotient. The large-frequency estimate
applies throughout the full original alpha>-1 parameter range.
Use: characteristicGamma_reflected_lower combines the proved actual Gamma lower bound with the original sine factor on the genuine contours.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- Euler reflection rewrites the original reference frequency characteristic as its literal sine and Gamma quotient whenever the reflected Gamma factor is nonzero.
Use: characteristicGamma_reflected_lower combines the proved actual Gamma lower bound with the original sine factor on the genuine contours.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's Gamma reflection formula.
Proof: multiply the globally valid reciprocal reflection formula by the nonzero reflected Gamma value and retain the original denominator Gamma factor. -/
theorem characteristicGamma_reflected (a : ℝ) (x : ℂ)
    (hG : Complex.Gamma (x+((1-gamma a:ℝ):ℂ))≠0) :
    characteristicGamma a x=
      (Complex.sin ((Real.pi:ℂ)*((gamma a:ℂ)-x))/(Real.pi:ℂ))*
        (Complex.Gamma (x+((1-gamma a:ℝ):ℂ))/Complex.Gamma (x+(gamma a:ℂ))) := by
  -- Reflection is first used in reciprocal form, valid even at zeros of the original characteristic.
  have h := reciprocalGamma_reflection ((gamma a:ℂ)-x)
  have he : (1:ℂ)-((gamma a:ℂ)-x)=x+((1-gamma a:ℝ):ℂ) := by push_cast; ring
  rw [he] at h
  have hh := congrArg (fun v : ℂ => v*Complex.Gamma (x+((1-gamma a:ℝ):ℂ))) h
  rw [mul_assoc,inv_mul_cancel₀ hG,mul_one] at hh
  rw [characteristicGamma,hh,show (gamma a:ℂ)+x=x+(gamma a:ℂ) by ring]
  ring

/-- The original reference characteristic has its uniform reflected Gamma lower bound at large frequencies in the closed right half-plane.
Use: contour_characteristicTau_lower inserts the proved exponential sine lower bound on the original frequency circles; this theorem bounds Delta_tau itself, not its relative spectral quotient.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: use the full-range finite-shift Gamma estimate with shifts 1-gamma and gamma, apply the exact reflection identity, and take norms with the original nonzero pi normalization. -/
theorem characteristicGamma_reflected_lower (a : ℝ) :
    ∃ c R : ℝ,0<c ∧ 1≤R ∧ ∀ x : ℂ,0≤x.re → R≤‖x‖ →
      c*‖(1:ℂ)+x‖^(1-2*gamma a)*
        ‖Complex.sin ((Real.pi:ℂ)*((gamma a:ℂ)-x))‖≤‖characteristicGamma a x‖ := by
  -- Both Gamma arguments are actual arguments of Euler reflection; their nonvanishing is proved by the finite shifts.
  obtain ⟨c,C,R,hc,_,hR,hbound⟩ := gamma_tail_power_bounds (1-gamma a) (gamma a)
  refine ⟨c/Real.pi,R,div_pos hc Real.pi_pos,hR,fun x hx hxR => ?_⟩
  obtain ⟨hG,_,hl,_⟩ := hbound x hx hxR
  rw [show 1-gamma a-gamma a=1-2*gamma a by ring] at hl
  rw [characteristicGamma_reflected a x hG,norm_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ = (‖Complex.sin ((Real.pi:ℂ)*((gamma a:ℂ)-x))‖/Real.pi)*
        (c*‖(1:ℂ)+x‖^(1-2*gamma a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

/-- A fixed real power of the shifted frequency norm has a positive lower comparison with the unshifted frequency power outside the disk of radius two.
Use: contour_characteristicTau_lower replaces the harmless Gamma normalization base 1+x by the original contour radius.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the two triangle inequalities put norm(1+x) between norm(x)/2 and 2*norm(x); monotonicity or antitonicity of the real power handles its two possible signs. -/
theorem shifted_frequency_power_lower (p : ℝ) :
    ∃ c : ℝ,0<c ∧ ∀ x : ℂ,2≤‖x‖ → c*‖x‖^p≤‖(1:ℂ)+x‖^p := by
  -- The minimum of the two endpoint constants treats every real exponent uniformly.
  refine ⟨min ((2:ℝ)^(-p)) ((2:ℝ)^p),by positivity,fun x hx => ?_⟩
  have hl : ‖x‖/2≤‖(1:ℂ)+x‖ := by
    have h := norm_sub_norm_le x (-1:ℂ)
    simp only [norm_neg,norm_one,sub_neg_eq_add] at h
    rw [add_comm x 1] at h
    linarith
  have hu : ‖(1:ℂ)+x‖≤2*‖x‖ := by have h := norm_add_le (1:ℂ) x; simp only [norm_one] at h; linarith
  have hpos : 0<‖x‖ := by linarith
  rcases le_or_gt 0 p with hp | hp
  · calc
      _ ≤ (2:ℝ)^(-p)*‖x‖^p := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = (‖x‖/2)^p := by rw [Real.div_rpow hpos.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2)]; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hl hp
  · calc
      _ ≤ (2:ℝ)^p*‖x‖^p := mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = (2*‖x‖)^p := (Real.mul_rpow (by norm_num) hpos.le).symm
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le (by positivity : 0<‖x‖/2) hl) hu hp.le

end
end jacobi.Reference
