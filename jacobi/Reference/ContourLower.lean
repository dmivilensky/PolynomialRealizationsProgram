import jacobi.Reference.ReflectedCharacteristic
import jacobi.Reference.ContourSine

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The original reference characteristic itself has the full lower
bound c*R_m^(1-2*gamma)*exp(abs(Im omega)) on every sufficiently
large original energy circle. The proof uses actual Gamma reflection,
the proved sharp half-plane Gamma bound and the half-integer sine
separation, throughout alpha>-1.
Use: contour_characteristicTau_lower transfers this estimate, with the correct pi normalization, to the original energy characteristic Delta_tau.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual reference Gamma characteristic has its uniform exponential and sharp power lower bound on every sufficiently large original right frequency semicircle.
Use: contour_characteristicTau_lower transfers this estimate, with the correct pi normalization, to the original energy characteristic Delta_tau.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: multiply the genuine reflected Gamma lower bound, the power comparison with the original frequency radius, and the proved half-integer sine lower bound. -/
theorem contour_characteristicGamma_lower {a : ℝ} (ha : -1<a) :
    ∃ c : ℝ,0<c ∧ ∃ M : ℕ,∀ m : ℕ,M≤m → ∀ x : ℂ,
      ‖x‖=(m:ℝ)+gamma a+1/2 → 0≤x.re →
      c*((m:ℝ)+gamma a+1/2)^(1-2*gamma a)*Real.exp (Real.pi*|x.im|)≤
        ‖characteristicGamma a x‖ := by
  -- The threshold comes solely from the proved finite Gamma shifts and is uniform around each original circle.
  obtain ⟨cG,R,hcG,hR,hGamma⟩ := characteristicGamma_reflected_lower a
  obtain ⟨cP,hcP,hpower⟩ := shifted_frequency_power_lower (1-2*gamma a)
  obtain ⟨cS,hcS,hsine⟩ := contour_sine_lower
  obtain ⟨M,hM⟩ := exists_nat_gt (max 2 R)
  refine ⟨cG*cP*cS,by positivity,M,fun m hm x hx hxr => ?_⟩
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hMm : (M:ℝ)≤m := by exact_mod_cast hm
  have hx2 : 2≤‖x‖ := by rw [hx]; linarith [le_max_left (2:ℝ) R]
  have hxR : R≤‖x‖ := by rw [hx]; linarith [le_max_right (2:ℝ) R]
  have hp := hpower x hx2
  rw [hx] at hp
  have hs := hsine (gamma a) m x (by linarith [hx2,hx]) hx hxr
  calc
    _ = (cG*(cP*((m:ℝ)+gamma a+1/2)^(1-2*gamma a)))*
        (cS*Real.exp (Real.pi*|x.im|)) := by ring
    _ ≤ (cG*‖(1:ℂ)+x‖^(1-2*gamma a))*
        ‖Complex.sin ((Real.pi:ℂ)*((gamma a:ℂ)-x))‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hcG.le) hs (by positivity) (by positivity)
    _ ≤ _ := hGamma x hxr hxR

/-- The actual Delta_tau itself has the article's full lower bound on the original parity circles, for every choice of their frequency square root.
Use: together with contour_characteristic_bound and the original wave upper bound, this proves decay of the genuine meromorphic parity integrand and enables the residue passage.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: choose the sign of the original frequency so its real part is nonnegative, divide by pi to use contour_characteristicGamma_lower, and cancel the fixed pi power. The characteristic is even in frequency, so the bound holds for either original root. -/
theorem contour_characteristicTau_lower {a : ℝ} (ha : -1<a) :
    ∃ c : ℝ,0<c ∧ ∃ M : ℕ,∀ m : ℕ,M≤m → ∀ omega : ℂ,
      ‖omega‖=contourRadius a m →
      c*(contourRadius a m)^(1-2*gamma a)*Real.exp |omega.im|≤
        ‖characteristicTau a ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖ := by
  -- Evenness handles both semicircles without differentiating or selecting a square-root branch.
  obtain ⟨c,hc,M,hbound⟩ := contour_characteristicGamma_lower ha
  have hpi : 0<Real.pi^(1-2*gamma a) := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨c/Real.pi^(1-2*gamma a),div_pos hc hpi,M,fun m hm omega homega => ?_⟩
  let x : ℂ := omega/(Real.pi:ℂ)
  have hx : ‖x‖=(m:ℝ)+gamma a+1/2 := by
    dsimp [x]
    rw [norm_div,homega,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    dsimp [contourRadius]
    field_simp
  have hs : c*((m:ℝ)+gamma a+1/2)^(1-2*gamma a)*Real.exp (Real.pi*|x.im|)≤
      ‖characteristicGamma a x‖ := by
    by_cases hr : 0≤x.re
    · exact hbound m hm x hx hr
    · have hh := hbound m hm (-x) (by simpa using hx) (by simp only [neg_re]; linarith)
      simpa only [neg_im,abs_neg,characteristicGamma_even] using hh
  have him : Real.pi*|x.im|=|omega.im| := by
    dsimp [x]
    rw [Complex.div_ofReal_im,abs_div,abs_of_pos Real.pi_pos]
    field_simp
  have hrad : (m:ℝ)+gamma a+1/2=contourRadius a m/Real.pi := by
    dsimp [contourRadius]
    field_simp
  rw [him,hrad,Real.div_rpow (contourRadius_pos ha m).le Real.pi_pos.le] at hs
  have he : omega^2=((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)-
      (jacobi.Jacobi.endpointCorrection a:ℂ) := by ring
  rw [characteristicTau_eq a he]
  exact (show (c/Real.pi^(1-2*gamma a))*(contourRadius a m)^(1-2*gamma a)*Real.exp |omega.im|=
      c*((contourRadius a m)^(1-2*gamma a)/Real.pi^(1-2*gamma a))*Real.exp |omega.im| by ring).trans_le hs

end
end jacobi.Reference
