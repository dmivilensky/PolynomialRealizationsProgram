import polyak.GapEdges.Junction.Curve
import polyak.GapEdges.Junction.Interval

/-! Exact curvature and interval bounds at junctions. -/
noncomputable section
namespace polyak.GapEdges.Junction
open General Levels Set

def junctionG (a t₁ t₂ c : ℝ) : ℝ := a*(t₁-t₂)*Real.sin c^2

/-- The exact source expression in Fedge after inserting the junction jets. -/
theorem junction_curvature_formula (q : Tuning) {a t₂ c m : ℝ}
    (hc : c∈Ioo 0 (Real.pi/2)) (hd : Real.cos (2*c)≠t₂)
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*c)) t₂) :
    Real.sin c*deriv^[2] (Geometry.shiftedAngle q 0) (2*c)-
        (m-2*junctionG a (Real.cos (2*c)) t₂ c)*
          junctionG a (Real.cos (2*c)) t₂ c*Real.cos c =
      junctionG a (Real.cos (2*c)) t₂ c*Real.cos c*
        (4*junctionG a (Real.cos (2*c)) t₂ c-(m+2)+
          (2-Real.cos (2*c)^2-Real.cos (2*c)*t₂)/
            ((1+Real.cos (2*c))*(Real.cos (2*c)-t₂))) := by
  obtain ⟨_,hf,hs⟩ := junction_angle_jets q hc hXi
  have hfirst : deriv (Geometry.shiftedAngle q 0) (2*c)=
      1/2-junctionG a (Real.cos (2*c)) t₂ c := by
    dsimp [junctionG]
    linarith
  have hspos : 0<Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hcpos : 0<Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1,Real.pi_pos],hc.2⟩
  rw [hs,hfirst]
  rw [Real.cos_two_mul]
  have hd' : 2*Real.cos c^2-1-t₂≠0 := by rw [← Real.cos_two_mul]; exact sub_ne_zero.mpr hd
  have hc2 : 1+(2*Real.cos c^2-1)=2*Real.cos c^2 := by ring
  rw [hc2]
  unfold junctionG
  field_simp
  ring

/-- Every point of the explicit interval is strictly below half a period
in slope displacement; in particular the tip resonance is not silently removed. -/
theorem junction_interval_g_bounds {m a t₁ t₂ s : ℝ}
    (hm : 4≤m) (ht : 0≤t₁) (ht1 : t₁<1) (ht₂ : t₂<t₁)
    (hs : 0<s) (ha : junctionLower t₁ t₂<a)
    (hau : a<junctionUpper m t₁ t₂ s) :
    0<a*(t₁-t₂)*s^2 ∧ a*(t₁-t₂)*s^2<m/2 := by
  have hlow : 0<junctionLower t₁ t₂ := by
    unfold junctionLower
    apply div_pos (by norm_num)
    exact mul_pos (by linarith) (by linarith)
  have hap : 0<a := hlow.trans ha
  have hg : 0<a*(t₁-t₂)*s^2 := by positivity
  have hden : 0<4*(t₁-t₂)*s^2 := by positivity
  have hh := (lt_div_iff₀ hden).mp hau
  have hterm : 0<2*(1-t₁)/(t₁-t₂) := by positivity
  have htfrac : 0≤t₁/(1+t₁) := by positivity
  constructor
  · exact hg
  · nlinarith

theorem junction_curvature_source_form (q : Tuning) {a t₂ c m : ℝ}
    (hc : c∈Ioo 0 (Real.pi/2)) (hd : Real.cos (2*c)≠t₂)
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*c)) t₂) :
    Real.sin c*deriv^[2] (Geometry.shiftedAngle q 0) (2*c)-
        (m-2*junctionG a (Real.cos (2*c)) t₂ c)*
          junctionG a (Real.cos (2*c)) t₂ c*Real.cos c =
      junctionG a (Real.cos (2*c)) t₂ c*Real.cos c*
        (4*junctionG a (Real.cos (2*c)) t₂ c-(m+2)+
          2*(1-Real.cos (2*c))/(Real.cos (2*c)-t₂)+
          Real.cos (2*c)/(1+Real.cos (2*c))) := by
  rw [junction_curvature_formula q hc hd hXi]
  have hcpos : 0<Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1,Real.pi_pos],hc.2⟩
  have hden : 0<1+Real.cos (2*c) := by rw [Real.cos_two_mul]; nlinarith
  have he : (2-Real.cos (2*c)^2-Real.cos (2*c)*t₂)/
      ((1+Real.cos (2*c))*(Real.cos (2*c)-t₂)) =
      2*(1-Real.cos (2*c))/(Real.cos (2*c)-t₂)+Real.cos (2*c)/(1+Real.cos (2*c)) := by
    field_simp
    ring
  rw [he]
  ring

/-- The negative-curvature interval, before applying the fan theorem. -/
theorem junction_small_curvature_negative_iff (q : Tuning) {a t₂ c m : ℝ}
    (hc : c∈Ioo 0 (Real.pi/2)) (hd : t₂<Real.cos (2*c))
    (ha : junctionLower (Real.cos (2*c)) t₂<a)
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*c)) t₂) :
    (Real.sin c*deriv^[2] (Geometry.shiftedAngle q 0) (2*c)-
        (m-2*junctionG a (Real.cos (2*c)) t₂ c)*
          junctionG a (Real.cos (2*c)) t₂ c*Real.cos c < 0) ↔
      a∈Ioo (junctionLower (Real.cos (2*c)) t₂)
        (junctionUpper m (Real.cos (2*c)) t₂ (Real.sin c)) := by
  have hs : 0<Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hcos : 0<Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1,Real.pi_pos],hc.2⟩
  have ht1 : Real.cos (2*c)<1 := by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (show (0:ℝ)≤0 by rfl) (by linarith [hc.2] : 2*c≤Real.pi) (by linarith [hc.1])
  have hapos : 0<a := lt_trans (show 0<junctionLower (Real.cos (2*c)) t₂ from
    div_pos (by norm_num) (mul_pos (by linarith) (by linarith))) ha
  have hg : 0<junctionG a (Real.cos (2*c)) t₂ c := by unfold junctionG; positivity
  have hp : 0<junctionG a (Real.cos (2*c)) t₂ c*Real.cos c := mul_pos hg hcos
  rw [junction_curvature_source_form q hc (ne_of_gt hd) hXi,
    show (junctionG a (Real.cos (2*c)) t₂ c*Real.cos c*
      (4*junctionG a (Real.cos (2*c)) t₂ c-(m+2)+
          2*(1-Real.cos (2*c))/(Real.cos (2*c)-t₂)+
          Real.cos (2*c)/(1+Real.cos (2*c)))<0) ↔
      (4*junctionG a (Real.cos (2*c)) t₂ c-(m+2)+
          2*(1-Real.cos (2*c))/(Real.cos (2*c)-t₂)+
          Real.cos (2*c)/(1+Real.cos (2*c))<0) from by
        constructor <;> intro h <;> nlinarith only [h,hp]]
  simp only [mem_Ioo,ha,true_and]
  unfold junctionUpper junctionG
  rw [lt_div_iff₀ (show 0<4*(Real.cos (2*c)-t₂)*Real.sin c^2 by positivity)]
  constructor <;> intro hh <;> nlinarith only [hh]

end polyak.GapEdges.Junction
