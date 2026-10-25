import polyak.FareyPlateau.Ray.Slope

/-! The explicit source curve a₂ and the exact edge-curvature identity. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set

def edgeA2 (ω γ k D t : ℝ) : ℝ :=
  (Real.cos γ/Real.sin γ)*(1+(Real.cos ω)^2)/(2*(Real.sin ω)^3)+
    (1+D)*Real.cos ω/(2*(Real.sin ω)^2)-
    Real.sin γ*Real.cos γ*(1+D+(Real.cos γ/Real.sin γ)*(Real.cos ω/Real.sin ω))^2/Real.sin ω+
    Real.cos γ*k^2*t*(1-t)/(4*Real.sin ω*(Real.sin γ)^3)

theorem cotangentSecond_edge (q : Tuning) {ω γ a D : ℝ}
    (_hω : ω∈Ioo (0:ℝ) Real.pi)
    (he : Chart.coefficients q=edgeCoefficients (Real.cos ω)
      ((Real.cos γ/Real.sin γ)*Real.sin ω) a D) :
    Geometry.cotangentSecond q ω=
      (((Real.cos γ/Real.sin γ)*Real.sin ω)*(1+(Real.cos ω)^2)+
        (1+D)*Real.cos ω*(Real.sin ω)^2-2*a*(Real.sin ω)^4)/(Real.sin ω)^3 := by
  unfold Geometry.cotangentSecond Geometry.polyCotangentSecond
  rw [he]
  dsimp [edgeCoefficients]
  have heq :
      ((Real.cos γ/Real.sin γ*Real.sin ω-(1+D)*Real.cos ω-a*Real.cos ω^2)*(1+Real.cos ω^2)+
        2*(1+D+2*a*Real.cos ω)*Real.cos ω-a*(Real.cos ω^4-Real.cos ω^2+2))=
      ((Real.cos γ/Real.sin γ)*Real.sin ω)*(1+(Real.cos ω)^2)+
        (1+D)*Real.cos ω*(1-(Real.cos ω)^2)-2*a*(1-(Real.cos ω)^2)^2 := by ring
  have hid : 1-(Real.cos ω)^2=(Real.sin ω)^2 := by nlinarith [Real.sin_sq_add_cos_sq ω]
  rw [hid] at heq
  congr 1
  linear_combination heq

theorem phaseSecond_edge (q : Tuning) {ω γ a D : ℝ}
    (hω : ω∈Ioo (0:ℝ) Real.pi) (hγ : γ∈Ioo (0:ℝ) Real.pi)
    (he : Chart.coefficients q=edgeCoefficients (Real.cos ω)
      ((Real.cos γ/Real.sin γ)*Real.sin ω) a D) (hphase : q.angle ω=γ) :
    deriv^[2] (Geometry.shiftedAngle q 0) ω=
      (Real.sin γ)^2*(2*a*Real.sin ω-
        (((Real.cos γ/Real.sin γ)*Real.sin ω)*(1+(Real.cos ω)^2)+
          (1+D)*(Real.sin ω)^2*Real.cos ω)/(Real.sin ω)^3)+
      2*(Real.cos γ/Real.sin γ)*(Real.sin γ)^4*
        (1+D+(Real.cos γ/Real.sin γ)*(Real.cos ω/Real.sin ω))^2 := by
  rw [Geometry.deriv2_shiftedAngle q 0 hω]
  unfold Geometry.shiftedSecond
  rw [cotangentFirst_edge q hω hγ he,cotangentSecond_edge q hω he]
  have hc : Geometry.cotangent q ω=Real.cos γ/Real.sin γ := by
    rw [Geometry.cotangent,←q.cot_angle hω,hphase]
  rw [hc,add_zero]
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have ht := Real.sin_pos_of_pos_of_lt_pi hγ.1 hγ.2
  have hid : 1+(Real.cos γ/Real.sin γ)^2=1/(Real.sin γ)^2 := by
    field_simp [ht.ne']
    nlinarith [Real.sin_sq_add_cos_sq γ]
  rw [hid]
  field_simp [hs.ne',ht.ne']
  ring

theorem edge_curvature_a2 (q : Tuning) {ω γ a D k t : ℝ}
    (hω : ω∈Ioo (0:ℝ) Real.pi) (hγ : γ∈Ioo (0:ℝ) Real.pi)
    (he : Chart.coefficients q=edgeCoefficients (Real.cos ω)
      ((Real.cos γ/Real.sin γ)*Real.sin ω) a D) (hphase : q.angle ω=γ) :
    Real.sin γ*deriv^[2] (Geometry.shiftedAngle q 0) ω-
        (1/2:ℝ)*Real.cos γ*k^2*t*(1-t)=
      2*Real.sin ω*(Real.sin γ)^3*(a-edgeA2 ω γ k D t) := by
  rw [phaseSecond_edge q hω hγ he hphase]
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have ht := Real.sin_pos_of_pos_of_lt_pi hγ.1 hγ.2
  unfold edgeA2
  field_simp [hs.ne',ht.ne']
  ring

end polyak.FareyPlateau.Ray
