import polyak.Levels.Geometry.Arccotangent
import Mathlib.Tactic

/-! Exact angle jets at a junction of two tongue edges. These are jets of
an actual tuning's polar angle, determined by its three quadratic coefficients. -/
noncomputable section
namespace polyak.GapEdges.Junction
open General Levels Set

def junctionCoefficients (a t₁ t₂ : ℝ) : Chart.Coefficients :=
  ⟨1-a*t₁*t₂,1+a*(t₁+t₂),-a⟩

theorem junction_cotangent_jets (q : Tuning) {a t₂ c : ℝ}
    (hc : c∈Ioo 0 (Real.pi/2))
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*c)) t₂) :
    Geometry.cotangent q (2*c)=Real.cos c/Real.sin c ∧
    Geometry.cotangentFirst q (2*c)= -1/(2*Real.sin c^2)+a*(Real.cos (2*c)-t₂) ∧
    Geometry.cotangentSecond q (2*c)=Real.cos c/(2*Real.sin c^3)+
      a*(Real.cos (2*c)^2+Real.cos (2*c)*t₂-2)/(2*Real.sin c*Real.cos c) := by
  have hs : 0<Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hcos : 0<Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1,Real.pi_pos],hc.2⟩
  have htr := Real.sin_sq_add_cos_sq c
  have hs2 : Real.sin c^2=1-Real.cos c^2 := by nlinarith
  have hs4 : Real.sin c^4=(1-Real.cos c^2)^2 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,hs2]
  rw [Geometry.cotangent_eq_poly,Geometry.cotangentFirst,Geometry.cotangentSecond,hXi]
  dsimp [junctionCoefficients,Geometry.polyCotangent,Geometry.polyCotangentFirst,
    Geometry.polyCotangentSecond]
  rw [Real.sin_two_mul,Real.cos_two_mul]
  constructor
  · field_simp
    nlinarith [htr]
  constructor
  · field_simp
    ring_nf
    simp only [hs2]
    ring
  · field_simp
    ring_nf
    simp only [hs2]
    ring

/-- Appendix I, lemma junction: the exact angle and both derivatives. -/
theorem junction_angle_jets (q : Tuning) {a t₂ c : ℝ}
    (hc : c∈Ioo 0 (Real.pi/2))
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*c)) t₂) :
    Geometry.shiftedAngle q 0 (2*c)=c ∧
    deriv (Geometry.shiftedAngle q 0) (2*c)-1/2 =
      -a*(Real.cos (2*c)-t₂)*Real.sin c^2 ∧
    deriv^[2] (Geometry.shiftedAngle q 0) (2*c)=
      -(1/2)*(Real.cos c/Real.sin c)+
        (a/2)*(Real.sin c/Real.cos c)*(2-Real.cos (2*c)^2-Real.cos (2*c)*t₂)+
        2*(deriv (Geometry.shiftedAngle q 0) (2*c))^2*(Real.cos c/Real.sin c) := by
  have hω : 2*c∈Ioo 0 Real.pi := ⟨by linarith [hc.1],by linarith [hc.2]⟩
  have hs : 0<Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hcos : 0<Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1,Real.pi_pos],hc.2⟩
  have htr := Real.sin_sq_add_cos_sq c
  obtain ⟨h0,h1,h2⟩ := junction_cotangent_jets q hc hXi
  have hf : deriv (Geometry.shiftedAngle q 0) (2*c)=
      1/2-a*(Real.cos (2*c)-t₂)*Real.sin c^2 := by
    rw [(Geometry.hasDerivAt_shiftedAngle q 0 hω).deriv,Geometry.shiftedFirst,h0,h1]
    simp only [add_zero]
    have he : 1+(Real.cos c/Real.sin c)^2=1/Real.sin c^2 := by
      field_simp
      nlinarith
    rw [he]
    field_simp
    ring
  constructor
  · apply Geometry.angle_eq_of_cot_eq (Geometry.shiftedAngle_mem q 0 hω)
      ⟨hc.1,by linarith [hc.2,Real.pi_pos]⟩
    rw [Geometry.cot_shiftedAngle q 0 hω]
    exact (add_zero _).trans h0
  constructor
  · linarith
  · rw [Geometry.deriv2_shiftedAngle q 0 hω,Geometry.shiftedSecond,h0,h1,h2,hf]
    simp only [add_zero]
    have he : 1+(Real.cos c/Real.sin c)^2=1/Real.sin c^2 := by
      field_simp
      nlinarith
    rw [he]
    field_simp
    ring

end polyak.GapEdges.Junction
