import «2610.05164v2».PrescribedSpeed.GroundFunction
import «2610.05164v2».PrescribedSpeed.Moments

/-!
Article: 2610.05164v2, Proposition 5.
The exponential in the proof of Theorem 5.1 is a positive multiple of the actual ground state from
Theorem 3.1.
Use: `«2610.05164v2».PrescribedSpeed.SpeedData.ground_coordinate` feeds
`«2610.05164v2».Primal.traceDifferenceDensity_integrable` (trace Difference Density integrable).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.calibration_Gamma` — 2610.05164v2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace «2610.05164v2».PrescribedSpeed
noncomputable section
open «2610.05164v2».GroundState «2610.05164v2».Sobolev Set MeasureTheory Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace SpeedData
variable (S : SpeedData)

/--
Theorem 5.1's prescribed parameter is the actual spectral/variational ground parameter, rather
than just a parameter of a differential equation.

Exact identity `groundParameter (S.density_integrable hκ) (S.density_nonneg hκ)=κ`.

Use: `«2610.05164v2».PrescribedSpeed.SpeedData.exponential_ground_state` rewrites with this
identity to construct witnesses satisfying `∃ c : ℝ, 0 < c ∧ S.u=fun
x => c*H1.rep G.u x`.

Article: 2610.05164v2, Theorem 5.1.

Proof: Use the identities/estimates
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
`«2610.05164v2».GroundState.density_mass_positive` with the arguments shown in the proof.
-/
theorem groundParameter_density {κ : ℝ} (hκ : 0 < κ) :
    groundParameter (S.density_integrable hκ) (S.density_nonneg hκ)=κ := by
  -- Use the identities/estimates
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
  -- `«2610.05164v2».GroundState.density_mass_positive` with the arguments shown in the proof.
  let hm := S.density_integrable hκ
  let hn := S.density_nonneg hκ
  have hM := density_mass_positive hm hn (S.density_nonzero hκ)
  have hle : κ ≤ groundParameter hm hn := by
    apply (groundParameter_variational hm hn hM κ).mp
    intro f
    have hs := (S.riccati hκ).square_identity hm f
    have hp : 0 ≤ ∫ x, (H1.slope f x-(S.riccati hκ).a x*H1.rep f x)^2 :=
      integral_nonneg (fun x => sq_nonneg _)
    linarith
  obtain ⟨v,hv⟩ := S.exists_h1_u
  have hvd : ∀ x, HasDerivAt (H1.rep v) (S.d x) x := by rw [hv]; exact S.u_derivative
  have hode : ∀ᵐ x, HasDerivAt S.d ((1-κ*S.density κ x)*H1.rep v x) x := by
    rw [hv]
    exact S.u_ode hκ
  have he := ode_energy hm κ v (Filter.Eventually.of_forall hvd) S.d_locallyAC hode
  have hvne : v ≠ 0 := by
    intro hz
    have hp := S.u_positive 0
    rw [← hv,hz,H1.rep_zero] at hp
    exact lt_irrefl 0 hp
  have hnorm : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hvne)
  have hw : 0 < ∫ x, S.density κ x*H1.rep v x^2 := by nlinarith
  have hge := groundParameter_bound hm hn hM v
  rw [he] at hge
  exact le_antisymm ((mul_le_mul_iff_left₀ hw).mp hge) hle

/--
Any intrinsic ground coordinate from Theorem 3.1 agrees pointwise with the clamped inverse
constructed from the prescribed speed.

Exact identity `G.q=S.q`.

Use: `«2610.05164v2».Calibration.Data.leftFilter_bounds` rewrites with this identity to
establish membership in the specified domain/enclosure: `C.leftFilter hκ s q ∈ Icc (0:ℝ)
(s/κ*q)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem ground_coordinate {κ : ℝ} (hκ : 0 < κ)
    (G : GroundWitness (S.density_integrable hκ) (S.density_nonneg hκ)) : G.q=S.q := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  obtain ⟨v,hv⟩ := S.exists_h1_u
  have hpos : ∀ x, 0 < H1.rep v x := by rw [hv]; exact S.u_positive
  have hd : ∀ x, HasDerivAt (H1.rep v) (S.d x) x := by rw [hv]; exact S.u_derivative
  have ho : ∀ᵐ x, HasDerivAt S.d
      ((1-groundParameter (S.density_integrable hκ) (S.density_nonneg hκ)*S.density κ x)*H1.rep v x) x := by
    rw [S.groundParameter_density hκ,hv]
    exact S.u_ode hκ
  funext x
  have he := G.coordinate_unique v hpos hd S.d_locallyAC ho x
  rw [hv] at he
  have hquot : S.d x/S.u x=1-S.q x := by
    rw [d,mul_div_cancel_right₀ _ (ne_of_gt (S.u_positive x))]
  rw [hquot] at he
  linarith

/--
The exponential in the proof of Theorem 5.1 is a positive multiple of the actual ground state
from Theorem 3.1.

Constructs witnesses with the exact properties `∃ c : ℝ, 0 < c ∧ S.u=fun x => c*H1.rep G.u x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 5.

Proof: Use the identities/estimates
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
`«2610.05164v2».PrescribedSpeed.SpeedData.exists_h1_u` with the arguments shown in the proof.
-/
theorem exponential_ground_state {κ : ℝ} (hκ : 0 < κ)
    (G : GroundWitness (S.density_integrable hκ) (S.density_nonneg hκ)) :
    ∃ c : ℝ, 0 < c ∧ S.u=fun x => c*H1.rep G.u x := by
  -- Use the identities/estimates
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.exists_h1_u` with the arguments shown in the
  -- proof.
  obtain ⟨v,hv⟩ := S.exists_h1_u
  have hpos : ∀ x, 0 < H1.rep v x := by rw [hv]; exact S.u_positive
  have hd : ∀ᵐ x, HasDerivAt (H1.rep v) (S.d x) x := by
    rw [hv]
    exact Filter.Eventually.of_forall S.u_derivative
  have ho : ∀ᵐ x, HasDerivAt S.d
      ((1-groundParameter (S.density_integrable hκ) (S.density_nonneg hκ)*S.density κ x)*H1.rep v x) x := by
    rw [S.groundParameter_density hκ,hv]
    exact S.u_ode hκ
  obtain ⟨c,hc,hv'⟩ := G.positive_multiple v hpos hd S.d_locallyAC ho
  exact ⟨c,hc,by rw [← hv,hv',H1.rep_smul]⟩

end SpeedData
end
end «2610.05164v2».PrescribedSpeed
