import jacobi.Oscillation.CosineTaylor

/-!
Article: jacobi, Proposition B.1.
Affine images preserve interval bounds. A positive quadratic endpoint
distance and a fixed opposite-endpoint margin control the sine on the
physical angular interval [0,pi]. These elementary facts are applied to
the original corrected Jacobi nodes in Jacobi.Interpolation.
Use: preserves the actual corrected endpoint margins along the entire node interpolation interval.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set

/-- An affine function bounded at both endpoints has the same bounds throughout their unordered interval.
Use: preserves the actual corrected endpoint margins along the entire node interpolation interval.
Article: jacobi, Proposition B.1.
Proof: order the two endpoints and use the sign of the affine slope. -/
theorem affine_interval_bounds {A B u v x l r : ℝ} (hu : A*u+B ∈ Icc l r)
    (hv : A*v+B ∈ Icc l r) (hx : x ∈ uIcc u v) : A*x+B ∈ Icc l r := by
  -- Both endpoint orders are retained because the true and model nodes need not be ordered relative to each other.
  rcases hu with ⟨hlu,hur⟩
  rcases hv with ⟨hlv,hvr⟩
  rcases mem_uIcc.mp hx with hx | hx
  · by_cases hA : 0≤A
    · constructor <;> nlinarith [mul_nonneg hA (sub_nonneg.mpr hx.1),mul_nonneg hA (sub_nonneg.mpr hx.2)]
    · constructor <;> nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hA) (sub_nonneg.mpr hx.1),mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hA) (sub_nonneg.mpr hx.2)]
  · by_cases hA : 0≤A
    · constructor <;> nlinarith [mul_nonneg hA (sub_nonneg.mpr hx.1),mul_nonneg hA (sub_nonneg.mpr hx.2)]
    · constructor <;> nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hA) (sub_nonneg.mpr hx.1),mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hA) (sub_nonneg.mpr hx.2)]

/-- Every physical angle at most three quarters of pi has cosine at least minus three quarters.
Use: supplies a fixed opposite-endpoint margin for the true and model first-half Jacobi angles.
Article: jacobi, Proposition B.1.
Proof: cosine decreases on [0,pi], and cos(3*pi/4)=-sqrt(2)/2>=-3/4. -/
theorem cosine_cap_lower {x : ℝ} (hx : x ∈ Icc 0 (3*Real.pi/4)) : -(3/4:ℝ)≤cos x := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx.1
    (show 3*Real.pi/4≤Real.pi by linarith [Real.pi_pos]) hx.2
  have he : cos (3*Real.pi/4)= -Real.sqrt 2/2 := by
    rw [show 3*Real.pi/4=Real.pi-Real.pi/4 by ring,Real.cos_pi_sub,Real.cos_pi_div_four]
    ring
  rw [he] at hc
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]

/-- Positive corrected endpoint distance and a fixed opposite-endpoint margin imply the sharp sine scale on the physical angle interval.
Use: converts the actual interpolated quadratic margins to Proposition B.1 (d), before replacing frequency by degree.
Article: jacobi, Proposition B.1.
Proof: multiply 1-cos(theta) by 1+cos(theta), bounded between 1/16 and 2,
and use sin^2+cos^2=1. Positivity on [0,pi] permits taking square roots. -/
theorem sine_of_endpoint_margins {d D N t x : ℝ} (hd : 0<d) (hD : 0<D)
    (hN : 0<N) (ht : 0<t) (hx : x ∈ Icc 0 Real.pi)
    (hc : -(15/16:ℝ)≤cos x)
    (hlo : d*t^2≤N^2*(1-cos x)) (hhi : N^2*(1-cos x)≤D*t^2) :
    (Real.sqrt d/4)*t/N≤sin x ∧ sin x≤Real.sqrt (2*D)*t/N := by
  -- The lower margin ensures strict physical separation from the corrected endpoint; the opposite factor has its own independent uniform bound.
  have hs := Real.sin_nonneg_of_mem_Icc hx
  have hcos := Real.cos_le_one x
  have hid : N^2*(sin x)^2=(N^2*(1-cos x))*(1+cos x) := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hlower : d*t^2/16≤N^2*(sin x)^2 := by
    have hh := mul_le_mul_of_nonneg_left (show (1/16:ℝ)≤1+cos x by linarith)
      (show 0≤N^2*(1-cos x) by positivity)
    nlinarith
  have hupper : N^2*(sin x)^2≤2*D*t^2 := by
    have hh := mul_le_mul_of_nonneg_left (show 1+cos x≤2 by linarith)
      (show 0≤N^2*(1-cos x) by positivity)
    nlinarith
  have hsd := Real.sq_sqrt hd.le
  have hsD := Real.sq_sqrt (show 0≤2*D by positivity)
  have hloSq : ((Real.sqrt d/4)*t)^2≤(N*sin x)^2 := by nlinarith
  have hhiSq : (N*sin x)^2≤(Real.sqrt (2*D)*t)^2 := by nlinarith
  constructor
  · apply (div_le_iff₀ hN).mpr
    have hh := (sq_le_sq₀ (by positivity : 0≤(Real.sqrt d/4)*t) (mul_nonneg hN.le hs)).mp hloSq
    nlinarith
  · apply (le_div_iff₀ hN).mpr
    have hh := (sq_le_sq₀ (mul_nonneg hN.le hs) (by positivity : 0≤Real.sqrt (2*D)*t)).mp hhiSq
    nlinarith

end
end jacobi.Oscillation
