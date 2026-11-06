import nesterov.Faithful.Figure
import Mathlib.Analysis.Real.Pi.Bounds

/-! The exact first resonant integer period of the solid half-step curve. -/
namespace nesterov.Faithful
noncomputable section
open Set Polynomial Spectral

theorem contact_negative_symbol (A : Trace.DoubleRootData) {ω : ℝ}
    (hω : ω∈Ioo (0:ℝ) Real.pi) (hne : limitProduct A.u A.q ω≠0)
    (hcontact : |limitAngle A.u A.q ω|<ω/2) : A.symbol ω<0 := by
  let a := A.method.symbolPair 0 1 0
  have hpair : g a (Phase.frequency ω)≠0 ∨ skew a (Phase.frequency ω)≠0 := by
    by_contra hn
    push Not at hn
    have hf := Phase.stationary_factor A.method (by norm_num : (0:ℝ)<1) 0 (Phase.frequency ω)
    rw [Phase.arccos_frequency ⟨hω.1.le,hω.2.le⟩] at hf
    have hz : polyak.Waves.z 0 ω=circle ω := by simp [polyak.Waves.z,circle]
    rw [hz] at hf
    change (g a (Phase.frequency ω):ℂ)-2*Complex.I*skew a (Phase.frequency ω)=
      -((4/((1:ℝ)-0)^2:ℝ):ℂ)*A.method.characteristic 0 (circle ω)*
        star (A.method.characteristic 1 (circle ω)) at hf
    rw [hn.1,hn.2] at hf
    have hb := limitProduct_characteristic A.method A.q A.factor ω
    have he : -((4/((1:ℝ)-0)^2:ℝ):ℂ)*A.method.characteristic 0 (circle ω)*
        star (A.method.characteristic 1 (circle ω))=(-4:ℂ)*limitProduct A.u A.q ω := by
      rw [hb]
      norm_num
      ring
    rw [he] at hf
    have hz0 : (-4:ℂ)*limitProduct A.u A.q ω=0 := by simpa using hf.symm
    exact hne ((mul_eq_zero.mp hz0).resolve_left (by norm_num))
  obtain ⟨C,hC,hid⟩ := Phase.stationary_lag_one_positive_factor A.method
    (by norm_num : (0:ℝ)<1) ⟨hω.1,hω.2.le⟩ hpair
  change ((1-circle ω)*A.method.characteristic 0 (circle ω)*
    star (A.method.characteristic 1 (circle ω))).re=_ at hid
  rw [mul_assoc,←limitProduct_characteristic A.method A.q A.factor] at hid
  have ha := stationary_limit_angle A.method A.q A.factor (Phase.frequency ω)
  rw [Phase.arccos_frequency ⟨hω.1.le,hω.2.le⟩] at ha
  rw [ha] at hid
  have hsin : Real.sin (limitAngle A.u A.q ω-ω/2)<0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [(abs_lt.mp hcontact).2])
      (by linarith [(abs_lt.mp hcontact).1,hω.2])
  rw [trace_symbol_eq]
  change limitSymbol A.u A.q ω=C*Real.sin (limitAngle A.u A.q ω-ω/2) at hid
  rw [hid]
  exact mul_neg_of_pos_of_neg hC hsin

theorem solid_curve_no_small_contact {K : ℕ} (hK : 3≤K) (hK7 : K≤7) :
    ¬|limitAngle (momentumQuery (1/4)) (C (-1)) (2*Real.pi/K)|<Real.pi/K := by
  let ω := 2*Real.pi/(K:ℝ)
  have hKp : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hω0 : 0<ω := by dsimp [ω];positivity
  have hωpi : ω<Real.pi := by
    apply (div_lt_iff₀ hKp).mpr
    have hk : (2:ℝ)<K := by exact_mod_cast (show 2<K by omega)
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hk)]
  have hω67 : (6/7:ℝ)<ω := by
    apply (lt_div_iff₀ hKp).mpr
    have hk : (K:ℝ)≤7 := by exact_mod_cast hK7
    nlinarith [Real.pi_gt_three]
  have hb := (abs_le.mp (Real.cos_bound (x:=(6/7:ℝ)) (by norm_num))).2
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<6/7)] at hb
  have hcos67 : Real.cos (6/7:ℝ)<2/3 := by nlinarith
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤6/7) hωpi.le hω67.le
  have hξ : 1/3<1-Real.cos ω := by linarith
  let A := TwoStep.limitData (1/4) 1 (by norm_num)
  have hu : A.u=momentumQuery (1/4) := TwoStep.limitData_query _ _ _
  have hq : A.q=C (-1) := by change C (-1/(1:ℝ))=C (-1);norm_num
  have hS : 0<A.symbol ω := by
    rw [trace_symbol_eq,hu,hq]
    have hh := momentum_symbol (1/4) 1 ω (by norm_num)
    norm_num only [div_one] at hh
    rw [hh]
    unfold TwoStep.limitSymbol
    norm_num
    exact mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have hm := congrArg Complex.im (momentum_phase_factor (1/4) 1 ω (by norm_num))
  norm_num only [div_one,one_pow,one_mul,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.add_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,zero_add,add_zero] at hm
  have him : 0<(-star (limitProduct (momentumQuery (1/4)) (C (-1)) ω)).im := by
    rw [hm]
    have hs := Real.sin_pos_of_pos_of_lt_pi hω0 hωpi
    exact mul_pos (mul_pos (by norm_num) (by linarith)) (mul_pos (by norm_num) hs)
  have hp : limitProduct A.u A.q ω≠0 := by
    rw [hu,hq]
    intro hh
    rw [hh,star_zero,neg_zero,Complex.zero_im] at him
    linarith
  intro hcontact
  have hc : |limitAngle A.u A.q ω|<ω/2 := by
    rw [hu,hq]
    convert hcontact using 1
    dsimp [ω]
    ring
  have hn := contact_negative_symbol A ⟨hω0,hωpi⟩ hp hc
  linarith

theorem solid_curve_contact_iff {K : ℕ} (hK : 3≤K) :
    |limitAngle (momentumQuery (1/4)) (C (-1)) (2*Real.pi/K)|<Real.pi/K ↔ 8≤K := by
  constructor
  · intro hc
    by_contra hn
    exact solid_curve_no_small_contact hK (by omega) hc
  · exact solid_curve_contacts

end
end nesterov.Faithful
