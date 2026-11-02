import jacobi.Jacobi.RestoringState
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: jacobi, Proposition B.1.
The actual Jacobi restoring coefficient is bounded above by a fixed
multiple of N^2 between its genuine extreme zeros. The only geometric
input is their already proved positive endpoint distance scale.
Use: bounds both true endpoint singularities simultaneously on the entire actual nodal interval, including its middle.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set jacobi.Oscillation
set_option backward.isDefEq.respectTransparency false

/-- The original smooth-remainder restoring coefficient equals precisely the original symmetric half-angle singular potential.
Use: bounds both true endpoint singularities simultaneously on the entire actual nodal interval, including its middle.
Article: jacobi, Proposition B.1.
Proof: substitute the proved literal regular remainder and cancel its inverse-square subtraction. -/
theorem restoringState_potential {a b t : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ)
    (ht : t∈Ioo 0 Real.pi) :
    (restoringState a b ha hb n).potential t=frequency a b n^2+
      endpointCorrection a/(4*sin (t/2)^2)+endpointCorrection b/(4*cos (t/2)^2) := by
  change frequency a b n^2+endpointCorrection a/t^2+regularPotential a b t=_
  rw [regularPotential_eq a b ht]
  ring

/-- A positive actual endpoint distance bounds the genuine half-angle inverse-square factor at its finite spectral scale.
Use: controls each endpoint contribution to the original Jacobi restoring coefficient uniformly by N^2.
Article: jacobi, Proposition B.1.
Proof: the community concavity estimate gives sin(t/2)>=t/pi.
Multiply by the positive scale, square the resulting positive lower
bound, and compare the two actual nonzero denominators. -/
theorem half_angle_inverse_bound {t N d : ℝ} (ht : t∈Ioo 0 Real.pi) (hN : 0<N)
    (hd : 0<d) (hscale : d≤N*t) :
    1/(4*sin (t/2)^2)≤Real.pi^2*N^2/d^2 := by
  -- Both endpoint half-angles lie in the elementary concavity interval, so no uniform asymptotic estimate for sine is assumed.
  have hs : 0<sin (t/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2,Real.pi_pos])
  have hlo := Real.mul_le_sin (x := t/2) (by linarith [ht.1]) (by linarith [ht.2])
  have hm : t≤Real.pi*sin (t/2) := by
    have hh := mul_le_mul_of_nonneg_left hlo Real.pi_pos.le
    field_simp [Real.pi_ne_zero] at hh
    nlinarith
  have hd0 : d≤N*Real.pi*sin (t/2) := by nlinarith [mul_le_mul_of_nonneg_left hm hN.le]
  have hsq := (sq_le_sq₀ hd.le (by positivity : 0≤N*Real.pi*sin (t/2))).mpr hd0
  apply (div_le_div_iff₀ (by positivity : 0<4*sin (t/2)^2) (sq_pos_of_pos hd)).mpr
  nlinarith [sq_nonneg (N*Real.pi*sin (t/2))]

/-- One parameter-dependent positive coefficient bounds the original Jacobi restoring frequency on the entire region with the actual endpoint distance scale.
Use: the true nodal interval lies in this region, so ordinary Sturm comparison yields every original angular gap with no middle-index exception.
Article: jacobi, Proposition B.1.
Proof: bound the actual half-angle inverse-square factors using both
endpoint distances. Replace each signed endpoint coefficient by its
absolute value and enlarge the positive resulting scalar coefficient to
a strict square. -/
theorem restoring_potential_bound (a b : ℝ) {d : ℝ} (hd : 0<d) :
    ∃ L : ℝ,0<L ∧ ∀ N : ℝ,0<N → ∀ t∈Ioo 0 Real.pi,
      d≤N*t → d≤N*(Real.pi-t) →
      N^2+endpointCorrection a/(4*sin (t/2)^2)+endpointCorrection b/(4*cos (t/2)^2)<(L*N)^2 := by
  -- A single literal constant works throughout the whole actual interval, independently of its finite index or degree.
  let Q := 1+(|endpointCorrection a|+|endpointCorrection b|)*Real.pi^2/d^2
  have hQ : 1≤Q := by
    have hh : 0≤(|endpointCorrection a|+|endpointCorrection b|)*Real.pi^2/d^2 := by positivity
    dsimp [Q]
    linarith
  refine ⟨Q+1,by linarith,?_⟩
  intro N hN t ht hleft hright
  have hS := half_angle_inverse_bound ht hN hd hleft
  have hC := half_angle_inverse_bound (t := Real.pi-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩ hN hd hright
  have he : sin ((Real.pi-t)/2)=cos (t/2) := by
    rw [show (Real.pi-t)/2=Real.pi/2-t/2 by ring,Real.sin_pi_div_two_sub]
  rw [he] at hC
  have hsa : endpointCorrection a/(4*sin (t/2)^2)≤|endpointCorrection a| *(Real.pi^2*N^2/d^2) := by
    calc
      _ ≤ |endpointCorrection a|/(4*sin (t/2)^2) := div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ = |endpointCorrection a| *(1/(4*sin (t/2)^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS (abs_nonneg _)
  have hcb : endpointCorrection b/(4*cos (t/2)^2)≤|endpointCorrection b| *(Real.pi^2*N^2/d^2) := by
    calc
      _ ≤ |endpointCorrection b|/(4*cos (t/2)^2) := div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ = |endpointCorrection b| *(1/(4*cos (t/2)^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hC (abs_nonneg _)
  have hsum : N^2+endpointCorrection a/(4*sin (t/2)^2)+endpointCorrection b/(4*cos (t/2)^2)≤Q*N^2 := by
    calc
      _ ≤ N^2+|endpointCorrection a| * (Real.pi^2*N^2/d^2)+|endpointCorrection b| * (Real.pi^2*N^2/d^2) := by linarith
      _ = Q*N^2 := by dsimp [Q]; ring
  have hsquare : Q<(Q+1)^2 := by nlinarith
  have hh := mul_lt_mul_of_pos_right hsquare (sq_pos_of_pos hN)
  nlinarith

end
end jacobi.Jacobi
