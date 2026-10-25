import polyak.ModeLocking.TwoLag.TrigProduct

/-! Exact opposite-sign conditions at a two-lag tangency, for every K. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels Set

theorem lag_one_factor (q : Tuning) (ω : Frequency)
    (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi) :
    (tuningCurve q).lag 1 ω =
      (Real.sin (q.angle ω)/Real.sin (ω : ℝ))*(1-Real.cos (ω : ℝ))*
        (q.Xi (Real.cos (ω : ℝ))-(1+Real.cos (ω : ℝ))) := by
  rw [Farey.Certificates.lag_polynomial_factor q 1 (by norm_num) ω hω]
  norm_num [Farey.Certificates.signedLagPolynomial, Spectral.chebT, Spectral.chebU]
  ring

theorem Psi_difference {K : ℕ} {r c : ℝ} (hr : 0≤r)
    (hc : c∈Icc (-1 : ℝ) 1) :
    Psi K r c-(1+c)=
      -r*(1+c)*(Spectral.chebU (K-1) c+W K c)/(1+r*W K c) := by
  unfold Psi
  field_simp [(Psi_den_pos K hr hc).ne']
  ring

/-- A strictly positive multiplier times the negative sign product. -/
theorem lag_one_contact_product (q : Tuning) {K : ℕ} (hK : 1≤K) {r : ℝ}
    (hr : 0<r) (ω : Frequency) (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi)
    (hcontact : q.Xi (Real.cos (ω : ℝ))=Psi K r (Real.cos (ω : ℝ))) :
    ∃ C : ℝ, 0<C ∧ (tuningCurve q).lag 1 ω = -C*signProduct K ω := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hcos : -1<Real.cos (ω : ℝ) ∧ Real.cos (ω : ℝ)<1 := by
    have hsq := Real.sin_sq_add_cos_sq (ω : ℝ)
    constructor <;> nlinarith [Real.neg_one_le_cos (ω : ℝ), Real.cos_le_one (ω : ℝ), sq_pos_of_pos hsin]
  let f := (Real.sin (q.angle ω)/Real.sin (ω : ℝ))*(1-Real.cos (ω : ℝ))
  let d := 1+r*W K (Real.cos (ω : ℝ))
  let h := Real.sin ((ω : ℝ)/2)^2*Real.cos ((ω : ℝ)/2)
  have hf : 0<f := mul_pos
    (div_pos (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hω).1 (q.angle_mem hω).2) hsin)
    (sub_pos.mpr hcos.2)
  have hd : 0<d := Psi_den_pos K hr.le ⟨hcos.1.le,hcos.2.le⟩
  have hh : 0<h := half_den_pos hω
  have hcpos : 0<1+Real.cos (ω : ℝ) := by linarith [hcos.1]
  refine ⟨f*r*(1+Real.cos (ω : ℝ))/(d*h), by positivity, ?_⟩
  rw [lag_one_factor q ω hω, hcontact,
    Psi_difference hr.le ⟨hcos.1.le,hcos.2.le⟩]
  have hUW : Spectral.chebU (K-1) (Real.cos (ω : ℝ))+W K (Real.cos (ω : ℝ))=
      signProduct K ω/h := (eq_div_iff hh.ne').mpr (U_add_W_product hK (ω : ℝ))
  rw [hUW]
  change f*(-r*(1+Real.cos (ω : ℝ))*(signProduct K ω/h)/d)=_
  field_simp

theorem contact_lag_signs (q : Tuning) {K : ℕ} (hK : 1≤K) {a b : ℝ}
    (ha : 0<a) (hb : 0<b) (ω : Frequency)
    (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi)
    (hcontact : q.Xi (Real.cos (ω : ℝ))=Psi K (b/a) (Real.cos (ω : ℝ))) :
    ((0<(tuningCurve q).lag 1 ω ∧ (tuningCurve q).lag (-(K : ℤ)) ω<0) ↔
      signProduct K ω<0) ∧
    ((0<(tuningCurve q).lag (-(K : ℤ)) ω ∧ (tuningCurve q).lag 1 ω<0) ↔
      0<signProduct K ω) := by
  obtain ⟨C,hC,hval⟩ := lag_one_contact_product q hK (div_pos hb ha) ω hω hcontact
  have hz := (symbol_zero_iff q (by omega : 0<K) ha hb.le ω hω).mpr hcontact
  unfold symbol at hz
  constructor
  · constructor
    · intro h
      rw [hval] at h
      nlinarith [h.1]
    · intro h
      have hv : 0<(tuningCurve q).lag 1 ω := by rw [hval]; nlinarith
      refine ⟨hv, ?_⟩
      nlinarith [mul_pos ha hv]
  · constructor
    · intro h
      rw [hval] at h
      nlinarith [h.2]
    · intro h
      have hv : (tuningCurve q).lag 1 ω<0 := by rw [hval]; nlinarith
      refine ⟨?_, hv⟩
      nlinarith [mul_neg_of_pos_of_neg ha hv]

end polyak.ModeLocking.TwoLag
