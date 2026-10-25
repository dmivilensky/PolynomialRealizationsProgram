import polyak.Boundary.P1.Algebra

/-!
Article: Appendix B, the quantitative one-atom minimizer reserve.
Use: active contact and the certified physical atom bounds give η≥z³/4.
This estimate is analytic and uniform down to the compactified endpoint z=0.
-/
noncomputable section
namespace polyak.Boundary.P1
open Spectral

theorem geometry_bounds {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) :
    0<contactD z a ∧ 0<contactE z a ∧ 0<1+z*a ∧ a^2<1 := by
  have hz2 : z^2≤9/16 := by nlinarith
  have ha2 : a^2≤z^2/4 := by
    have hp := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤a+z/2)
      (by linarith : a-z/2≤0)
    nlinarith
  have hza : -z^2/2≤z*a := by nlinarith [mul_nonneg hz.le (by linarith : 0≤a+z/2)]
  have hprod := mul_nonneg (sq_nonneg z) (sq_nonneg a)
  dsimp [contactD,contactE]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem chargeNumerator_nonneg {z u a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) (hu : 0≤u) : 0≤chargeNumerator z u a := by
  obtain ⟨hD,hE,_,ha2⟩ := geometry_bounds hz hz1 ha
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu)
    (by linarith : 0≤1-a^2)) hE.le) hD.le

theorem charge_ratio_bound {z u a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) (hg : 0≤1-a^2-u^2) (h0 : quartic z u a=0) :
    z*chargeNumerator z u a≤(1-a^2-u^2)*(1-z^2) := by
  obtain ⟨hD,_,hlin,_⟩ := geometry_bounds hz hz1 ha
  have hact := contact_gap_identity h0
  have he : z*chargeNumerator z u a*(1+z*a)=(1-a^2-u^2)*contactE z a := by
    calc
      _=(2*u*z*(1-a^2)*(1+z*a))*contactE z a/contactD z a := by
        unfold chargeNumerator
        ring
      _=((1-a^2-u^2)*contactD z a)*contactE z a/contactD z a := by rw [← hact]
      _=_ := by field_simp [hD.ne']
  have hE : contactE z a≤(1+z*a)*(1-z^2) := by
    have hp := mul_nonpos_of_nonpos_of_nonneg ha.2 (by linarith : 0≤z+2*a)
    have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg z) hp
    unfold contactE
    nlinarith
  apply (mul_le_mul_iff_left₀ hlin).mp
  calc
    _=(1-a^2-u^2)*contactE z a := he
    _≤(1-a^2-u^2)*((1+z*a)*(1-z^2)) := mul_le_mul_of_nonneg_left hE hg
    _=_ := by ring

theorem minimizer_gap {z u a t : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) (hu : 0≤u) (hgz : z/2≤1-a^2-u^2)
    (h0 : quartic z u a=0) (ht : Real.cosh t=1/z) :
    z^3/4≤(1-a^2-u^2)-|chargeNumerator z u a/Real.sinh t| := by
  have hg : 0≤1-a^2-u^2 := by linarith
  have hd := chargeNumerator_nonneg hz hz1 ha hu
  have hzd := charge_ratio_bound hz hz1 ha hg h0
  have hs0 : Real.sinh t≠0 := by
    intro he
    have ht0 : t=0 := Real.sinh_eq_zero.mp he
    rw [ht0,Real.cosh_zero] at ht
    have heq := (eq_div_iff hz.ne').mp ht
    nlinarith
  have hs : 0 < |Real.sinh t| := abs_pos.mpr hs0
  have hsq : z^2*|Real.sinh t|^2=1-z^2 := by
    rw [sq_abs,Real.sinh_sq,ht]
    field_simp [hz.ne']
  have hdb : chargeNumerator z u a≤(1-a^2-u^2)*z*|Real.sinh t|^2 := by
    apply (mul_le_mul_iff_right₀ hz).mp
    calc
      _≤(1-a^2-u^2)*(1-z^2) := hzd
      _=z*((1-a^2-u^2)*z*|Real.sinh t|^2) := by rw [← hsq]; ring
  have hC : |chargeNumerator z u a/Real.sinh t|≤(1-a^2-u^2)*z*|Real.sinh t| := by
    rw [abs_div,abs_of_nonneg hd]
    apply (div_le_iff₀ hs).mpr
    nlinarith [hdb]
  have hz2 : z^2≤9/16 := by nlinarith
  have hb : z*|Real.sinh t|≤1-z^2/2 := by
    have hn := mul_nonneg hz.le (abs_nonneg (Real.sinh t))
    nlinarith [sq_nonneg (z*|Real.sinh t|-(1-z^2/2))]
  have hm := mul_le_mul_of_nonneg_left hb hg
  have hgprod := mul_le_mul_of_nonneg_right hgz (sq_nonneg z)
  nlinarith

end polyak.Boundary.P1
