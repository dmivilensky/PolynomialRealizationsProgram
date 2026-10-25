import polyak.FareyPlateau.Plateau.LocationTuning
import polyak.FareyPlateau.Domain.Source

/-! Identification of the large-curvature constant with the exact
trigonometric constant printed in Proposition location. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels Filter Set Topology

theorem sin_div_one_add_cos (γ : ℝ) (hγ : γ∈Ioo (0:ℝ) Real.pi) :
    Real.sin γ/(1+Real.cos γ)=Real.tan (γ/2) := by
  have hhalf : γ/2∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [hγ.1,hγ.2,Real.pi_pos]
  have hcos : 0<Real.cos (γ/2) := Real.cos_pos_of_mem_Ioo hhalf
  have hcosγ : -1<Real.cos γ := by
    have ht := Real.cos_lt_cos_of_nonneg_of_le_pi hγ.1.le le_rfl hγ.2
    simpa only [Real.cos_pi] using ht
  rw [Real.tan_eq_sin_div_cos]
  apply (div_eq_div_iff (by linarith : 1+Real.cos γ≠0) hcos.ne').mpr
  have hsin := Real.sin_two_mul (γ/2)
  have hdouble := Real.cos_two_mul (γ/2)
  rw [show 2*(γ/2)=γ by ring] at hsin hdouble
  rw [hsin,hdouble]
  ring

theorem edgeRootLimit_trig {ω γ : ℝ} (hω : ω∈Ioo (0:ℝ) Real.pi)
    (hγ : γ∈Ioo (0:ℝ) Real.pi) :
    edgeRootLimit (Real.cos ω) ((Real.cos γ/Real.sin γ)*Real.sin ω)=
      Real.tan (γ/2)/Real.sin ω := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have ht := Real.sin_pos_of_pos_of_lt_pi hγ.1 hγ.2
  have heq : ((Real.cos γ/Real.sin γ)*Real.sin ω)^2+1-(Real.cos ω)^2=
      (Real.sin ω/Real.sin γ)^2 := by
    field_simp [ht.ne']
    nlinarith [Real.sin_sq_add_cos_sq γ, Real.sin_sq_add_cos_sq ω]
  unfold edgeRootLimit
  rw [heq,Real.sqrt_sq (div_pos hs ht).le,←sin_div_one_add_cos γ hγ]
  have hcosγ : -1<Real.cos γ := by
    have hx := Real.cos_lt_cos_of_nonneg_of_le_pi hγ.1.le le_rfl hγ.2
    simpa only [Real.cos_pi] using hx
  field_simp [hs.ne',ht.ne',show 1+Real.cos γ≠0 by linarith]

theorem source_location_constant {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) :
    2*edgeRootLimit (Chart.rationalCosine j k) (Chart.rationalHeight j k)=
      2*Real.tan (Real.pi/(2*k))/Real.sin (Regions.rationalAngle j k) := by
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  have hω := Regions.rationalAngle_mem (show 1≤j by omega) hjk
  have hk : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hγ : Real.pi/k∈Ioo (0:ℝ) Real.pi :=
    ⟨div_pos Real.pi_pos (by linarith),div_lt_self Real.pi_pos hk⟩
  unfold Chart.rationalCosine Chart.rationalHeight
  rw [edgeRootLimit_trig hω hγ]
  rw [show Real.pi/(k:ℝ)/2=Real.pi/(2*k) by ring]
  ring

end polyak.FareyPlateau
