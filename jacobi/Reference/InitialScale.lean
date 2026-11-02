import jacobi.Reference.ScaledCore
import jacobi.Reference.PotentialBounds
import jacobi.Reference.EndpointUniform

/-!
Article: jacobi, Lemma C.1.
The original reference wave and its actual slope are bounded uniformly
on pi*|omega| *t<=1/4. These estimates supply actual initial data for the
high-frequency ODE energy; no asymptotic state or independent comparison
solution is substituted for the source function.
Use: applies both genuine scaled-core estimates to the actual physical reference argument.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original cosine coordinate lies in the proved shrinking core disk at the actual small frequency scale.
Use: applies both genuine scaled-core estimates to the actual physical reference argument.
Article: jacobi, Lemma C.1.
Proof: square the genuine scaled-angle bound and combine it with the already proved explicit quadratic cosine-coordinate bound. -/
theorem small_scale_coordinate {omega : ℂ} {t : ℝ} (ht : 0<t)
    (hsmall : Real.pi*‖omega‖*t≤1/4) : ‖omega‖^2*‖(coordinate t:ℂ)‖≤1/8 := by
  have hnn : 0≤Real.pi*‖omega‖*t := by positivity
  have hsq := (sq_le_sq₀ hnn (by norm_num : (0:ℝ)≤1/4)).mpr hsmall
  have hh := mul_le_mul_of_nonneg_left (coordinate_quadratic t) (sq_nonneg ‖omega‖)
  nlinarith

/-- The actual physical coordinate slope is bounded by its explicit linear small-angle scale.
Use: bounds the true chain-rule term in the original reference slope at high frequency.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the actual half-interval sine is positive and at most its original angle. -/
theorem coordinateSlope_half_bound {t : ℝ} (ht : t∈Ioc 0 (1/2)) :
    |coordinateSlope t|≤Real.pi^2*t/2 := by
  have hs := sine_pos (show t∈Ioo 0 1 by constructor; exact ht.1; linarith [ht.2])
  have hh := Real.sin_le (x := Real.pi*t) (mul_nonneg Real.pi_pos.le ht.1.le)
  rw [coordinateSlope,abs_of_nonneg (by positivity : 0≤Real.pi*Real.sin (Real.pi*t)/2)]
  nlinarith [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]

/-- The genuine original reference wave and its actual slope have uniform selected-branch bounds on the true small-frequency-scale interval.
Use: gives both actual components of the initial high-frequency state, and controls the small-t region of the full reference strip bound.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the true cosine argument lies in the scaled Cauchy disk. Bound
the original prefactor by t^gamma, its true logarithmic slope by B/t,
and its true coordinate derivative by pi^2*t/2. The squared scaled
frequency is bounded by one, so the differentiated core term also has
exactly the endpoint derivative scale. -/
theorem wave_small_scale {a : ℝ} (ha : -1<a) :
    ∃ C D : ℝ,0<C ∧ 0<D ∧ ∀ omega:ℂ,1≤‖omega‖ →
      ∀ t∈Ioc (0:ℝ) (1/2),Real.pi*‖omega‖*t≤1/4 →
        ‖wave a omega t‖≤C*t^(gamma a) ∧
          ‖waveSlope a omega t‖≤D*t^(gamma a)/t := by
  -- Every estimate concerns the actual source function and its independently proved genuine derivative.
  obtain ⟨C,hC,hcore⟩ := waveCore_scaled_bound a
  obtain ⟨D,hD,hderiv⟩ := waveCore_scaled_deriv_bound a
  obtain ⟨B,hB,hlog⟩ := weightLogSlope_bound a
  refine ⟨C,B*C+Real.pi^2*D/2,hC,by positivity,fun omega homega t ht hsmall => ?_⟩
  have ht0 : 0<t := ht.1
  have hti : t∈Ioo 0 1 := ⟨ht0,by linarith [ht.2]⟩
  have hx := small_scale_coordinate ht0 hsmall
  have hH := hcore omega homega (coordinate t:ℂ) (by linarith)
  have hH' := hderiv omega homega (coordinate t:ℂ) hx
  have hw := weight_half_bound ha ht
  have hwp := weight_pos a hti
  have htgp := Real.rpow_pos_of_pos ht0 (gamma a)
  constructor
  · rw [wave,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hwp]
    exact (mul_le_mul hw hH (norm_nonneg _) htgp.le).trans_eq (by ring)
  · have hs : ‖waveSlope a omega t‖≤weight a t*
        (|weightLogSlope a t| * ‖waveCore a omega (coordinate t:ℂ)‖+
          |coordinateSlope t| * ‖deriv (waveCore a omega) (coordinate t:ℂ)‖) := by
      rw [waveSlope,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hwp]
      have hh := norm_add_le ((weightLogSlope a t:ℂ)*waveCore a omega (coordinate t:ℂ))
        ((coordinateSlope t:ℂ)*deriv (waveCore a omega) (coordinate t:ℂ))
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs] at hh
      exact mul_le_mul_of_nonneg_left hh hwp.le
    have hs' : ‖waveSlope a omega t‖≤t^(gamma a)*
        ((B/t)*C+(Real.pi^2*t/2)*(D*‖omega‖^2)) := by
      apply hs.trans
      apply mul_le_mul hw ?_ (by positivity) htgp.le
      exact add_le_add
        (mul_le_mul (hlog t ht) hH (norm_nonneg _) (by positivity))
        (mul_le_mul (coordinateSlope_half_bound ht) hH' (norm_nonneg _) (by positivity))
    have hrt : ‖omega‖*t≤1 := by
      nlinarith [Real.two_le_pi,mul_nonneg (norm_nonneg omega) ht0.le]
    have hrtsq : (‖omega‖*t)^2≤1 := by
      nlinarith [mul_nonneg (norm_nonneg omega) ht0.le]
    have hbracket : (B/t)*C+(Real.pi^2*t/2)*(D*‖omega‖^2)≤(B*C+Real.pi^2*D/2)/t := by
      apply (le_div_iff₀ ht0).mpr
      have he : ((B/t)*C+(Real.pi^2*t/2)*(D*‖omega‖^2))*t=
          B*C+(Real.pi^2*D/2)*(‖omega‖*t)^2 := by field_simp [ht0.ne']
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left hrtsq (show 0≤Real.pi^2*D/2 by positivity)]
    exact hs'.trans ((mul_le_mul_of_nonneg_left hbracket htgp.le).trans_eq (by ring))

/-- The actual reference energy propagation starts at the original positive physical time 1/(4*pi*|omega|).
Use: fixes one genuine point where the source small-scale state bounds are uniform in high frequency.
Article: jacobi, Lemma C.1.
-/
def initialTime (omega : ℂ) : ℝ := 1/(4*Real.pi*‖omega‖)

/-- The genuine high-frequency initial time belongs to the source half interval and has exactly its prescribed scaled angle.
Use: discharges all original spatial and scaling premises of the actual initial-state estimate.
Article: jacobi, Lemma C.1.
Proof: norm(omega)>=1 and pi>1 give the physical interval; ordinary nonzero-frequency division gives the exact scaled-angle identity. -/
theorem initialTime_properties {omega : ℂ} (homega : 1≤‖omega‖) :
    initialTime omega∈Ioc (0:ℝ) (1/2) ∧ Real.pi*‖omega‖*initialTime omega=1/4 := by
  -- The chosen initial point stays in the actual source domain at every genuine high frequency.
  have hRp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have ht0 : 0 < initialTime omega := by dsimp [initialTime]; positivity
  have hscale : Real.pi*‖omega‖*initialTime omega=1/4 := by
    dsimp [initialTime]
    field_simp
  refine ⟨⟨ht0,?_⟩,hscale⟩
  have hh := mul_le_mul_of_nonneg_left homega Real.pi_pos.le
  nlinarith [Real.two_le_pi,mul_le_mul_of_nonneg_right hh ht0.le]

end
end jacobi.Reference
