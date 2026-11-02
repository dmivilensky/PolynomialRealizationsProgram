import jacobi.Reference.ContourGeometry
import jacobi.Complex.SineModulus
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Use: contour_sine_real_lower compares the genuine reflected sine with its half-integer midpoint value.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- Near the real axis, the right semicircle lies within one sixteenth of its positive real endpoint.
Use: contour_sine_real_lower compares the genuine reflected sine with its half-integer midpoint value.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the radial deficit e satisfies e*(r+Re x)=(Im x)^2; with r>=1 and abs(Im x)<=1/4 this is at most 1/16. -/
theorem contour_radial_deficit {r : ℝ} (hr : 1≤r) {x : ℂ}
    (hx : ‖x‖=r) (hxr : 0≤x.re) (hxi : |x.im|≤1/4) :
    0≤r-x.re ∧ r-x.re≤1/16 := by
  -- The exact circle identity gives a quadratic, rather than linear, real-part deficit.
  have he : 0≤r-x.re := by linarith [Complex.re_le_norm x]
  have hs : x.re^2+x.im^2=r^2 := by
    have h := Complex.normSq_eq_norm_sq x
    simpa only [Complex.normSq_apply,hx,pow_two] using h
  have hi : x.im^2≤1/16 := by nlinarith [sq_abs x.im,abs_nonneg x.im]
  exact ⟨he,by nlinarith [mul_nonneg he (show 0≤r+x.re-1 by linarith)]⟩

/-- The real part of the genuine reflected sine is bounded away from its zeros on the near-real part of every original large frequency semicircle.
Use: contour_sine_lower supplies the missing bounded-imaginary-frequency portion of the uniform exponential sine lower bound.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the phase is an integer multiple of pi plus pi/2, up to pi times the proved radial deficit. The cosine remainder is smaller than one half by the elementary quadratic cosine bound. -/
theorem contour_sine_real_lower {g : ℝ} (m : ℕ) {x : ℂ}
    (hr : 1≤(m:ℝ)+g+1/2) (hx : ‖x‖=(m:ℝ)+g+1/2)
    (hxr : 0≤x.re) (hxi : |x.im|≤1/4) :
    1/2≤|Real.sin (Real.pi*(g-x.re))| := by
  -- The radius is exactly the original half-integer radius, so the trigonometric phase is exact.
  let e : ℝ := (m:ℝ)+g+1/2-x.re
  have he := contour_radial_deficit hr hx hxr hxi
  change 0≤e ∧ e≤1/16 at he
  have hp : 0≤Real.pi*e ∧ Real.pi*e≤1/4 := by
    refine ⟨mul_nonneg Real.pi_pos.le he.1,?_⟩
    calc
      _ ≤ (4:ℝ)*(1/16) := mul_le_mul Real.pi_lt_four.le he.2 he.1 (by norm_num)
      _ = _ := by norm_num
  have hcos : 1/2≤Real.cos (Real.pi*e) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi*e)
    nlinarith
  have hphase : Real.pi*(g-x.re)= -((Real.pi/2-Real.pi*e)+(m:ℝ)*Real.pi) := by dsimp [e]; ring
  rw [hphase,Real.sin_neg,abs_neg,Real.sin_add_nat_mul_pi,abs_mul,abs_neg_one_pow,
    one_mul,Real.sin_pi_div_two_sub]
  exact hcos.trans (le_abs_self _)

/-- The sine factor of the actual reflected reference characteristic has its full uniform positive exponential lower bound on the original right frequency semicircles.
Use: contour_characteristicTau_lower combines this result with the actual Gamma quotient estimate to prove the missing absolute lower bound for Delta_tau itself.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: near the real axis use exact half-integer phase separation and absorb the bounded exponential. Away from it, the imaginary hyperbolic sine gives a fixed positive multiple of the full exponential. -/
theorem contour_sine_lower :
    ∃ c : ℝ,0<c ∧ ∀ g : ℝ,∀ m : ℕ,∀ x : ℂ,
      1≤(m:ℝ)+g+1/2 → ‖x‖=(m:ℝ)+g+1/2 → 0≤x.re →
      c*Real.exp (Real.pi*|x.im|)≤‖Complex.sin ((Real.pi:ℂ)*((g:ℂ)-x))‖ := by
  -- The same constant covers both portions of every original semicircle.
  let c₁ : ℝ := Real.exp (-Real.pi/4)/2
  let c₂ : ℝ := (1-Real.exp (-2*(Real.pi/4)))/2
  have hc₁ : 0<c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0<c₂ := by
    have h := Real.exp_lt_one_iff.mpr (show -2*(Real.pi/4)<0 by linarith [Real.pi_pos])
    dsimp [c₂]
    positivity
  refine ⟨min c₁ c₂,lt_min hc₁ hc₂,fun g m x hr hx hxr => ?_⟩
  let z : ℂ := (Real.pi:ℂ)*((g:ℂ)-x)
  have hzr : z.re=Real.pi*(g-x.re) := by simp [z,mul_re]
  have hzi : |z.im|=Real.pi*|x.im| := by simp [z,mul_im,abs_mul,abs_of_pos Real.pi_pos]
  by_cases hi : |x.im|≤1/4
  · have hsin := (jacobi.Complex.sine_modulus_lower z).1
    rw [hzr] at hsin
    have he : Real.exp (-Real.pi/4)*Real.exp (Real.pi*|x.im|)≤1 := by
      rw [← Real.exp_add]
      exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    calc
      _ ≤ c₁*Real.exp (Real.pi*|x.im|) := mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le
      _ ≤ (1/2:ℝ) := by dsimp [c₁]; nlinarith
      _ ≤ _ := (contour_sine_real_lower m hr hx hxr hi).trans hsin
  · have hi' : Real.pi/4≤|z.im| := by rw [hzi]; nlinarith [Real.pi_pos,lt_of_not_ge hi]
    have h := (jacobi.Complex.sinh_exponential_lower (by positivity : 0<Real.pi/4) hi').2
    rw [hzi] at h
    calc
      _ ≤ c₂*Real.exp (Real.pi*|x.im|) := mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
      _ ≤ |Real.sinh z.im| := h
      _ ≤ _ := (jacobi.Complex.sine_modulus_lower z).2

end
end jacobi.Reference
