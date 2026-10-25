import polyak.FareyPlateau.Ray.ContactMoments
import polyak.FareyPlateau.Ray.Slope
import polyak.FareyPlateau.Symbols.CurvatureQuotient

/-! The slope condition in admissibility forces the actual first contact
jet of Ψ.  No contact jet is an assumption in the final source theorem. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set Filter
open scoped BigOperators Topology
variable {I : Type*} [Fintype I]

theorem phaseFloor_contact_derivative {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k)
    {b : ℤ} (hb : (b*j)%k=1) {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Symbols.Admissible k b bar n w) :
    deriv (Symbols.psi n w) (Chart.rationalCosine j k)=
      bar/(2*(Real.sin (Real.pi/k))^2)-
        (Real.cos (Real.pi/k)/Real.sin (Real.pi/k))*
          (Real.cos (Regions.rationalAngle j k)/Real.sin (Regions.rationalAngle j k)) := by
  let ω := Regions.rationalAngle j k
  let γ := Real.pi/(k:ℝ)
  have hω : ω∈Ioo (0:ℝ) Real.pi := Regions.rationalAngle_mem hj hjk
  have hk : 0<k := by omega
  have hkr : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hγ : γ∈Ioo (0:ℝ) Real.pi :=
    ⟨div_pos Real.pi_pos (by linarith),div_lt_self Real.pi_pos hkr⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have ht := Real.sin_pos_of_pos_of_lt_pi hγ.1 hγ.2
  have hμ := oneMass_pos h
  have hp := denominator_derivative_contact hk hjk.le hb h
  have hq := sineMoment_derivative_contact hk hjk.le hb h
  have hP : Symbols.denominator n w ω≠0 := (h.denominator_pos ⟨hω.1,hω.2.le⟩).ne'
  have hquot := ((Real.hasDerivAt_sin ω).mul hq).div hp hP
  have heq : (fun x=>Symbols.psi n w (Real.cos x)) =ᶠ[𝓝 ω]
      (fun x=>Real.sin x*sineMoment n w x/Symbols.denominator n w x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hω] with x hx
    exact Symbols.psi_cos n w h.nonzero (fun i=>(h.positive i).le) h.normalization h.bezout hx
  have hpsi := h.phaseFloor_analytic (Real.cos ω) ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have hchain := hpsi.differentiableAt.hasDerivAt.comp ω (Real.hasDerivAt_cos ω)
  have hd := hchain.unique (hquot.congr_of_eventuallyEq heq)
  have hM : firstMoment n w=2*oneMoment k b n w-bar*oneMass k b n w := by
    linarith [admissible_moment_balance hb h]
  change deriv (Symbols.psi n w) (Real.cos ω)*(-Real.sin ω)=_ at hd
  unfold Chart.rationalCosine
  apply (mul_right_cancel₀ (neg_ne_zero.mpr hs.ne'))
  rw [hd]
  change _=(bar/(2*(Real.sin γ)^2)-(Real.cos γ/Real.sin γ)*(Real.cos ω/Real.sin ω))*(-Real.sin ω)
  rw [denominator_contact hk hjk.le hb h]
  simp only [Pi.mul_apply]
  unfold sineMoment
  rw [sine_contact hk hjk.le hb h,hM]
  rw [show 2*Real.pi/(k:ℝ)=2*γ by dsimp [γ];ring,Real.sin_two_mul,Real.cos_two_mul]
  have hc2 : (Real.cos γ)^2=1-(Real.sin γ)^2 := by nlinarith [Real.sin_sq_add_cos_sq γ]
  rw [hc2]
  ring_nf
  field_simp [hs.ne',ht.ne',hμ.ne']
  ring_nf
  rw [hc2]
  ring

theorem phaseFloor_edge_contact {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k)
    {b : ℤ} (hb : (b*j)%k=1) {D : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Symbols.Admissible k b (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D) n w) :
    Symbols.psi n w (Chart.rationalCosine j k)=Chart.rationalHeight j k ∧
      deriv (Symbols.psi n w) (Chart.rationalCosine j k)=1+D := by
  refine ⟨phaseFloor_contact hj hjk hb h,?_⟩
  rw [phaseFloor_contact_derivative hj hjk hb h]
  have hk : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hs : 0<Real.sin (Real.pi/k) := Real.sin_pos_of_pos_of_lt_pi
    (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hk)
  unfold edgeSlope
  field_simp [hs.ne']
  ring

end polyak.FareyPlateau.Ray
