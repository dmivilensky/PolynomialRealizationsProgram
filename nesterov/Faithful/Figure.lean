import nesterov.Faithful.HalfStep

/-! Mathematical content of the half-step figure: the solid curve contacts. -/
namespace nesterov.Faithful
noncomputable section
open Set Polynomial

/-- A negative symbol and a principal phase in [0,π] put the phase strictly
below half a step, with no ambiguity from the sine branch. -/
theorem negative_symbol_phase_contact (A : Trace.DoubleRootData) {ω : ℝ}
    (hω : ω∈Ioc (0:ℝ) Real.pi) (hS : A.symbol ω<0)
    (hangle : 0≤limitAngle A.u A.q ω) : |limitAngle A.u A.q ω|<ω/2 := by
  rw [abs_of_nonneg hangle]
  by_contra hn
  have hl : 0≤limitAngle A.u A.q ω-ω/2 := by linarith [le_of_not_gt hn]
  have hu : limitAngle A.u A.q ω-ω/2≤Real.pi := by
    have hh := Complex.arg_le_pi (-star (limitProduct A.u A.q ω))
    change limitAngle A.u A.q ω≤Real.pi at hh
    linarith [hω.1]
  have hsin := Real.sin_nonneg_of_mem_Icc ⟨hl,hu⟩
  have hid := Phase.stationary_lag_one_phase_identity A.method (by norm_num : (0:ℝ)<1)
    (show ω∈Icc (0:ℝ) Real.pi from ⟨hω.1.le,hω.2⟩)
  change ((1-circle ω)*A.method.characteristic 0 (circle ω)*star (A.method.characteristic 1 (circle ω))).re=_ at hid
  rw [mul_assoc,←limitProduct_characteristic A.method A.q A.factor] at hid
  have ha := stationary_limit_angle A.method A.q A.factor (Phase.frequency ω)
  rw [Phase.arccos_frequency ⟨hω.1.le,hω.2⟩] at ha
  rw [ha] at hid
  have hm : 0≤Phase.magnitude (Spectral.g (A.method.symbolPair 0 1 0) (Phase.frequency ω))
      (Spectral.skew (A.method.symbolPair 0 1 0) (Phase.frequency ω)) := norm_nonneg _
  have hsinhalf : 0≤Real.sin (ω/2) := Real.sin_nonneg_of_mem_Icc ⟨by linarith [hω.1],by linarith [hω.2,Real.pi_pos]⟩
  have hnonneg : 0≤limitSymbol A.u A.q ω := by
    rw [show limitSymbol A.u A.q ω=_ from hid]
    positivity
  rw [trace_symbol_eq] at hS
  linarith

theorem solid_curve_negative {ω : ℝ} (hω0 : 0<ω) (hω4 : ω≤Real.pi/4) :
    limitSymbol (momentumQuery (1/4)) (C (-1)) ω<0 := by
  have hωpi : ω≤Real.pi := by linarith [Real.pi_pos]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hω0.le (by linarith [Real.pi_pos] : Real.pi/4≤Real.pi) hω4
  rw [Real.cos_pi_div_four] at hcos
  have hsqrt : (2/3:ℝ)<Real.sqrt 2/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have hcos1 : Real.cos ω<1 := by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) hωpi hω0
  have hξ : 0<1-Real.cos ω := sub_pos.mpr hcos1
  have hξ3 : 1-Real.cos ω<1/3 := by linarith
  have hh := momentum_symbol (1/4) 1 ω (by norm_num)
  norm_num only [div_one] at hh
  rw [hh]
  unfold TwoStep.limitSymbol
  norm_num
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos hξ) (by linarith)

/-- The displayed solid curve lies strictly under every rational threshold
with period K≥8, exactly as asserted in the figure caption. -/
theorem solid_curve_contacts {K : ℕ} (hK : 8≤K) :
    |limitAngle (momentumQuery (1/4)) (C (-1)) (2*Real.pi/K)|<Real.pi/K := by
  have hKpos : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  let ω := 2*Real.pi/(K:ℝ)
  have hω0 : 0<ω := div_pos (by positivity) hKpos
  have hω4 : ω≤Real.pi/4 := by
    apply (div_le_iff₀ hKpos).mpr
    have hh : (8:ℝ)≤K := by exact_mod_cast hK
    nlinarith [Real.pi_pos]
  have hωpi : ω≤Real.pi := by linarith [Real.pi_pos]
  let A := TwoStep.limitData (1/4) 1 (by norm_num)
  have hu : A.u=momentumQuery (1/4) := TwoStep.limitData_query _ _ _
  have hq : A.q=C (-1) := by change C (-1/(1:ℝ))=C (-1);norm_num
  have hS : A.symbol ω<0 := by
    rw [trace_symbol_eq,hu,hq]
    exact solid_curve_negative hω0 hω4
  have hangle : 0≤limitAngle A.u A.q ω := by
    rw [hu,hq]
    have he := momentum_angle (1/4) 1 (by norm_num) ⟨hω0,hωpi⟩
    norm_num only [div_one] at he
    rw [he]
    apply Complex.arg_nonneg_iff.mpr
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_im,Complex.I_re,
      Complex.ofReal_re,mul_zero,zero_add,one_mul]
    exact mul_nonneg (by norm_num) (Real.sin_nonneg_of_mem_Icc ⟨hω0.le,hωpi⟩)
  have hh := negative_symbol_phase_contact A ⟨hω0,hωpi⟩ hS hangle
  rw [hu,hq] at hh
  convert hh using 1
  dsimp [ω]
  ring

end
end nesterov.Faithful
