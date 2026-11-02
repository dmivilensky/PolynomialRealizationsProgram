import jacobi.Reference.GammaHalfPlane
import jacobi.Complex.GammaShift

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Use: characteristicGamma_reflected_lower applies the actual Gamma reflection formula with shifts 1-gamma and gamma, throughout the article's full alpha>-1 range.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- Arbitrary fixed real Gamma shifts have matching power bounds at large frequencies in the closed right half-plane, with both actual Gamma factors nonzero.
Use: characteristicGamma_reflected_lower applies the actual Gamma reflection formula with shifts 1-gamma and gamma, throughout the article's full alpha>-1 range.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's Gamma recurrence and the Phragmen--Lindelof principle.
Proof: shift both arguments by one common integer into the proved positive-shift range. Each finite recurrence factor lies between half and twice the frequency, so their product quotient stays between two positive constants. -/
theorem gamma_tail_power_bounds (a b : ℝ) :
    ∃ c C R : ℝ,0<c ∧ 0<C ∧ 1≤R ∧ ∀ z : ℂ,0≤z.re → R≤‖z‖ →
      Complex.Gamma (z+(a:ℂ))≠0 ∧ Complex.Gamma (z+(b:ℂ))≠0 ∧
      c*‖(1:ℂ)+z‖^(a-b)≤‖Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))‖ ∧
      ‖Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))‖≤C*‖(1:ℂ)+z‖^(a-b) := by
  -- The finite shift and the frequency threshold are chosen once, before the original frequency is varied.
  obtain ⟨n,hn⟩ := exists_nat_gt (max (1/4-a) (1/4-b))
  have hna : 1/4<a+(n:ℝ) := by linarith [le_max_left (1/4-a) (1/4-b)]
  have hnb : 1/4<b+(n:ℝ) := by linarith [le_max_right (1/4-a) (1/4-b)]
  obtain ⟨c,C,hc,hC,hbound⟩ := gamma_halfPlane_power_bounds hna hnb
  let R : ℝ := 2*(|a|+|b|+(n:ℝ)+1)
  refine ⟨c*(1/4)^n,C*4^n,R,by positivity,by positivity,
    by dsimp [R]; linarith [abs_nonneg a,abs_nonneg b,Nat.cast_nonneg (α := ℝ) n],fun z hz hzR => ?_⟩
  have hzr : 0<‖z‖ := by
    have hR : 0<R := by dsimp [R]; positivity
    exact hR.trans_le hzR
  have hzA : 2*(|a|+(n:ℝ)+1)≤‖z‖ := by dsimp [R] at hzR; linarith [abs_nonneg b]
  have hzB : 2*(|b|+(n:ℝ)+1)≤‖z‖ := by dsimp [R] at hzR; linarith [abs_nonneg a]
  let P : ℂ := ∏ j∈Finset.range n,(z+(a:ℂ)+(j:ℂ))
  let Q : ℂ := ∏ j∈Finset.range n,(z+(b:ℂ)+(j:ℂ))
  have hP := jacobi.Complex.rising_product_bounds a n z hzA
  have hQ := jacobi.Complex.rising_product_bounds b n z hzB
  change (‖z‖/2)^n≤‖P‖ ∧ ‖P‖≤(2*‖z‖)^n at hP
  change (‖z‖/2)^n≤‖Q‖ ∧ ‖Q‖≤(2*‖z‖)^n at hQ
  have hPpos : 0<‖P‖ := lt_of_lt_of_le (by positivity) hP.1
  have hQpos : 0<‖Q‖ := lt_of_lt_of_le (by positivity) hQ.1
  have hrecA : Complex.Gamma (z+((a+(n:ℝ):ℝ):ℂ))=Complex.Gamma (z+(a:ℂ))*P := by
    simpa only [P,Complex.ofReal_add,Complex.ofReal_natCast,add_assoc] using
      jacobi.Complex.gamma_rising_product (z+(a:ℂ)) n (fun j hj =>
        norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (jacobi.Complex.rising_factor_bounds a n z hzA hj).1))
  have hrecB : Complex.Gamma (z+((b+(n:ℝ):ℝ):ℂ))=Complex.Gamma (z+(b:ℂ))*Q := by
    simpa only [Q,Complex.ofReal_add,Complex.ofReal_natCast,add_assoc] using
      jacobi.Complex.gamma_rising_product (z+(b:ℂ)) n (fun j hj =>
        norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (jacobi.Complex.rising_factor_bounds b n z hzB hj).1))
  have hGA : Complex.Gamma (z+((a+(n:ℝ):ℝ):ℂ))≠0 :=
    Gamma_ne_zero_of_re_pos (by simp only [add_re,ofReal_re]; linarith)
  have hGB : Complex.Gamma (z+((b+(n:ℝ):ℝ):ℂ))≠0 :=
    Gamma_ne_zero_of_re_pos (by simp only [add_re,ofReal_re]; linarith)
  have hGa : Complex.Gamma (z+(a:ℂ))≠0 := by intro h; exact hGA (by rw [hrecA,h,zero_mul])
  have hGb : Complex.Gamma (z+(b:ℂ))≠0 := by intro h; exact hGB (by rw [hrecB,h,zero_mul])
  have he : Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))=
      (Complex.Gamma (z+((a+(n:ℝ):ℝ):ℂ))/Complex.Gamma (z+((b+(n:ℝ):ℝ):ℂ)))*(Q/P) := by
    rw [hrecA,hrecB]
    field_simp [hGa,hGb,norm_pos_iff.mp hPpos,norm_pos_iff.mp hQpos]
  have hratio := jacobi.Complex.shift_ratio_bounds hzr hPpos hQpos n hP.1 hP.2 hQ.1 hQ.2
  have hs := hbound z hz
  rw [show a+(n:ℝ)-(b+(n:ℝ))=a-b by ring] at hs
  refine ⟨hGa,hGb,?_,?_⟩
  · rw [he,norm_mul]
    simpa only [norm_div,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul hs.1 hratio.1 (by positivity) (norm_nonneg _)
  · rw [he,norm_mul]
    simpa only [norm_div,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul hs.2 hratio.2 (by positivity) (by positivity)

end
end jacobi.Reference
