import chebyshev2.Calibration.Amplitude
import chebyshev2.Filters.SpectralObservations

/-!
Article: chebyshev2, Proposition 5.
Uniform compact-parameter form of ν³ ≤ C Q from Proposition 4.
Use: `chebyshev2.Calibration.Data.amplitude_cube_integrable` feeds
`chebyshev2.Calibration.Data.amplitude_defect_integrable` (amplitude defect integrable).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.Calibration
noncomputable section
open Set MeasureTheory Filter chebyshev2.GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace Data
variable (C : Data)

/--
The stated quantitative bound `C.Gamma q ≤ Q q`.

Use: `chebyshev2.Calibration.Data.amplitude_cube_bound_compact` uses this bound to
establish constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ κ ∈ K, ∀ q ∈ Icc
(0:ℝ) 2, (C.amplitude κ q)^3 ≤ A*Q q`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.Gamma_bounds` with the
arguments shown in the proof.
-/
theorem Gamma_le_Q {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) : C.Gamma q ≤ Q q := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.Gamma_bounds` with the
  -- arguments shown in the proof.
  have h := (C.Gamma_bounds hq).2
  rcases le_total q 1 with hq1 | hq1
  · have h' := h.trans (min_le_left _ _)
    have hp : 0 ≤ q*(1-q) := mul_nonneg hq.1 (sub_nonneg.mpr hq1)
    dsimp [Q]
    nlinarith
  · have h' := h.trans (min_le_right _ _)
    have hp : 0 ≤ (2-q)*(q-1) := mul_nonneg (sub_nonneg.mpr hq.2) (sub_nonneg.mpr hq1)
    dsimp [Q]
    nlinarith

/--
Continuity on the stated domain: `ContinuousOn (C.amplitude κ) (Icc (0:ℝ) 2)`.

Use: `chebyshev2.Calibration.Data.amplitude_bounded` uses this continuity result to
establish constructs witnesses with the exact properties `∃ M : ℝ, 0 < M ∧ ∀ q ∈ Icc (0:ℝ) 2,
C.amplitude κ q ≤ M`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_continuousOn`
with the arguments shown in the proof.
-/
theorem amplitude_continuousOn_fixed {κ : ℝ} (hκ : 0 < κ) :
    ContinuousOn (C.amplitude κ) (Icc (0:ℝ) 2) :=
  C.amplitude_continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hq => ⟨hκ,hq⟩)

/--
Defines `extendedAmplitude` of type `ℝ` by `C.amplitude κ (max 0 (min 2 q))`.

Use: `chebyshev2.Calibration.Data.extendedAmplitude_eq` rewrites with this definition to
establish exact identity `C.extendedAmplitude κ q=C.amplitude κ q`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def extendedAmplitude (κ q : ℝ) : ℝ := C.amplitude κ (max 0 (min 2 q))

/--
Continuity of the displayed function: `Continuous (C.extendedAmplitude κ)`.

Use: `chebyshev2.Calibration.Data.V_two` rewrites with this continuity result to establish
the precise assertion is `C.V κ 2= -(2*C.b+3/2*(∫ q in (0:ℝ)..2, C.amplitude κ q))/κ`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.Data.amplitude_continuousOn_fixed`,
`chebyshev2.Calibration.Data.clamp_mem` with the arguments shown in the proof.
-/
theorem extendedAmplitude_continuous {κ : ℝ} (hκ : 0 < κ) : Continuous (C.extendedAmplitude κ) :=
  (C.amplitude_continuousOn_fixed hκ).comp_continuous
    (continuous_const.max (continuous_const.min continuous_id)) clamp_mem

/--
Exact identity `C.extendedAmplitude κ q=C.amplitude κ q`.

Use: `chebyshev2.Calibration.Data.V_composition_integrable` rewrites with this identity to
establish integrability of the displayed function: `Integrable (fun x => C.Vprime
(groundParameter hm hn) (G.q x)*(groundParameter hm hn*m x-Q (G.q x)))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem extendedAmplitude_eq {κ q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    C.extendedAmplitude κ q=C.amplitude κ q := by simp only [extendedAmplitude,min_eq_right hq.2,max_eq_right hq.1]

/--
Constructs witnesses with the exact properties `∃ M : ℝ, 0 < M ∧ ∀ q ∈ Icc (0:ℝ) 2, C.amplitude
κ q ≤ M`.

Use: `chebyshev2.Calibration.Data.V_composition_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => C.Vprime (groundParameter hm hn)
(G.q x)*(groundParameter hm hn*m x-Q (G.q x)))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.Data.amplitude_continuousOn_fixed` with the arguments shown in the
proof.
-/
theorem amplitude_bounded {κ : ℝ} (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ q ∈ Icc (0:ℝ) 2, C.amplitude κ q ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image (C.amplitude_continuousOn_fixed hκ)
  refine ⟨max M 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro q hq
  exact (hM (mem_image_of_mem _ hq)).trans (le_max_left _ _)

/--
Uniform compact-parameter form of ν³ ≤ C Q from Proposition 4.

Constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ κ ∈ K, ∀ q ∈ Icc (0:ℝ) 2,
(C.amplitude κ q)^3 ≤ A*Q q`.

Use: `chebyshev2.Calibration.Data.amplitude_cube_bound` uses this bound to establish
constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ q ∈ Icc (0:ℝ) 2,
(C.amplitude κ q)^3 ≤ A*Q q`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_continuousOn`,
`chebyshev2.Calibration.Data.amplitude_nonneg`,
`chebyshev2.Calibration.Data.Gamma_le_Q` with the arguments shown in the proof.
-/
theorem amplitude_cube_bound_compact {K : Set ℝ} (hK : IsCompact K) (hpos : ∀ κ ∈ K, 0 < κ) :
    ∃ A : ℝ, 0 < A ∧ ∀ κ ∈ K, ∀ q ∈ Icc (0:ℝ) 2, (C.amplitude κ q)^3 ≤ A*Q q := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_continuousOn`,
  -- `chebyshev2.Calibration.Data.amplitude_nonneg`,
  -- `chebyshev2.Calibration.Data.Gamma_le_Q` with the arguments shown in the proof.
  have hcont := C.amplitude_continuousOn.mono
    (show K ×ˢ Icc (0:ℝ) 2 ⊆ {p | 0 < p.1 ∧ p.2 ∈ Icc (0:ℝ) 2} from
      fun p hp => ⟨hpos _ hp.1,hp.2⟩)
  obtain ⟨M,hM⟩ := (hK.prod isCompact_Icc).bddAbove_image hcont
  -- Establish continuity hcoef before using the function at limits or in calculus arguments.
  have hcoef : ContinuousOn (fun κ => (3*max M 1+2*C.b+2*κ*C.omega)/κ) K := by
    fun_prop (disch := exact fun κ hκ => (hpos κ hκ).ne')
  obtain ⟨A,hA⟩ := hK.bddAbove_image hcoef
  refine ⟨max A 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro κ hκ q hq
  have hk := hpos κ hκ
  have hv := C.amplitude_nonneg hk q
  have hG := C.Gamma_le_Q hq
  have hQ := Q_nonneg hq
  have hν : C.amplitude κ q ≤ max M 1 :=
    (hM (mem_image_of_mem (fun p : ℝ × ℝ => C.amplitude p.1 p.2)
      (show (κ,q) ∈ K ×ˢ Icc (0:ℝ) 2 from ⟨hκ,hq⟩))).trans (le_max_left _ _)
  have he := C.amplitude_equation hk hq
  have hw := mul_le_mul_of_nonneg_left hG (mul_nonneg (by linarith : 0 ≤ 2*κ) C.omega_nonneg)
  have hνQ := mul_le_mul_of_nonneg_left hν (by linarith : 0 ≤ 3*Q q)
  have hle : (C.amplitude κ q)^3 ≤ ((3*max M 1+2*C.b+2*κ*C.omega)/κ)*Q q := by
    have hdiv : ((3*max M 1+2*C.b+2*κ*C.omega)/κ)*Q q=
        ((3*max M 1+2*C.b+2*κ*C.omega)*Q q)/κ := by ring
    rw [hdiv]
    apply (le_div_iff₀ hk).2
    unfold constant at he
    nlinarith
  exact hle.trans (mul_le_mul_of_nonneg_right
    ((hA (mem_image_of_mem _ hκ)).trans (le_max_left _ _)) hQ)

/--
Constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ q ∈ Icc (0:ℝ) 2,
(C.amplitude κ q)^3 ≤ A*Q q`.

Use: `chebyshev2.Calibration.Data.amplitude_cube_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => (C.amplitude (groundParameter hm
hn) (G.q x))^3)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.Data.amplitude_cube_bound_compact` with the arguments shown in the
proof.
-/
theorem amplitude_cube_bound {κ : ℝ} (hκ : 0 < κ) :
    ∃ A : ℝ, 0 < A ∧ ∀ q ∈ Icc (0:ℝ) 2, (C.amplitude κ q)^3 ≤ A*Q q := by
  obtain ⟨A,hA,he⟩ := C.amplitude_cube_bound_compact isCompact_singleton
    (show ∀ t ∈ ({κ} : Set ℝ), 0 < t from fun t ht => by simpa using (mem_singleton_iff.mp ht) ▸ hκ)
  exact ⟨A,hA,he κ (mem_singleton κ)⟩

/--
Integrability of the displayed function: `Integrable (fun x => (C.amplitude (groundParameter hm
hn) (G.q x))^3)`.

Use: `chebyshev2.Calibration.Data.amplitude_defect_integrable` uses this integrability
result to establish integrability of the displayed function: `Integrable (fun x => w x*(m
x-(C.amplitude (groundParameter hm hn) (G.q x))^2))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_cube_bound`,
`chebyshev2.GroundState.GroundWitness.coupling_positive`,
`chebyshev2.Calibration.Data.amplitude_continuousOn_fixed` with the arguments shown in the
proof.
-/
theorem amplitude_cube_integrable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) :
    Integrable (fun x => (C.amplitude (groundParameter hm hn) (G.q x))^3) := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_cube_bound`,
  -- `chebyshev2.GroundState.GroundWitness.coupling_positive`,
  -- `chebyshev2.Calibration.Data.amplitude_continuousOn_fixed` with the arguments shown in
  -- the proof.
  obtain ⟨A,_,hA⟩ := C.amplitude_cube_bound G.coupling_positive
  have hc := (C.amplitude_continuousOn_fixed G.coupling_positive).comp_continuous
    G.R.q_continuous G.coordinate_mem
  apply (G.coordinate_integrability.1.const_mul A).mono' (hc.pow 3).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖(C.amplitude (groundParameter hm hn) (G.q x))^3‖ ≤ A*Q (G.q x)
    rw [Real.norm_of_nonneg (pow_nonneg (C.amplitude_nonneg G.coupling_positive _) _)]
    exact hA _ (G.coordinate_mem x))

end Data
end
end chebyshev2.Calibration
