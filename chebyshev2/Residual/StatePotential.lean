import chebyshev2.Filters.StateFlow
import chebyshev2.Calibration.ChainRule
import chebyshev2.Calibration.Tangent

/-!
Article: chebyshev2, Proposition 8.
The null Lagrangian in Proposition 8 for arbitrary C1 state potentials.
Use: `chebyshev2.Residual.statePotential_drift` feeds
`chebyshev2.Calibration.Data.flowResidual_decomposition` (flow Residual decomposition).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.Residual
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.GroundState chebyshev2.Filters chebyshev2.Calibration
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `State` of type `` by `ℝ × ℝ × ℝ × ℝ`.

Use: `chebyshev2.Residual.driftVector` uses this definition in the displayed construction
of `driftVector`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.
-/
abbrev State := ℝ × ℝ × ℝ × ℝ

/--
Defines `stateBox` of type `Set State` by `Icc (0:ℝ) 2 ×ˢ (Icc (0:ℝ) (2/κ) ×ˢ (Icc (0:ℝ) (2/κ)
×ˢ Icc (0:ℝ) 2))`.

Use: `chebyshev2.Residual.statePotential_locallyAC` uses this definition to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (fun x => Ψ
(state G x)) a b`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.
-/
def stateBox (κ : ℝ) : Set State :=
  Icc (0:ℝ) 2 ×ˢ (Icc (0:ℝ) (2/κ) ×ˢ (Icc (0:ℝ) (2/κ) ×ˢ Icc (0:ℝ) 2))

/--
Defines `inputVector` of type `State` by `(κ,1,1,0)`.

Use: `chebyshev2.Residual.bPotential` uses this definition in the displayed construction of
`bPotential`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def inputVector (κ : ℝ) : State := (κ,1,1,0)
/--
Defines `driftVector` of type `State` by `(Q
Y.1,2*Y.2.1+32*Y.2.1^2,2*Y.2.2.1+64*Y.2.2.1^2,2*Y.2.2.2-Y.1^2)`.

Use: `chebyshev2.Residual.dPotential` uses this definition in the displayed construction of
`dPotential`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def driftVector (Y : State) : State :=
  (Q Y.1,2*Y.2.1+32*Y.2.1^2,2*Y.2.2.1+64*Y.2.2.1^2,2*Y.2.2.2-Y.1^2)

/--
Defines `bPotential` of type `ℝ` by `fderiv ℝ Ψ Y (inputVector κ)`.

Use: `chebyshev2.Residual.statePotential_drift` rewrites with this definition to establish
the precise assertion is `fderiv ℝ Ψ (state G x) (stateDerivative G x)= bPotential
(groundParameter hm hn) Ψ (state G x)*m x-dPotential Ψ (state G x)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def bPotential (κ : ℝ) (Ψ : State → ℝ) (Y : State) : ℝ := fderiv ℝ Ψ Y (inputVector κ)
/--
Defines `dPotential` of type `ℝ` by `fderiv ℝ Ψ Y (driftVector Y)`.

Use: `chebyshev2.Residual.statePotential_drift` rewrites with this definition to establish
the precise assertion is `fderiv ℝ Ψ (state G x) (stateDerivative G x)= bPotential
(groundParameter hm hn) Ψ (state G x)*m x-dPotential Ψ (state G x)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def dPotential (Ψ : State → ℝ) (Y : State) : ℝ := fderiv ℝ Ψ Y (driftVector Y)

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)
include G

/--
Membership in the specified domain/enclosure: `state G x ∈ stateBox (groundParameter hm hn)`.

Use: `chebyshev2.Residual.statePotential_derivative_integrable` uses this assertion to
establish integrability of the displayed function: `Integrable (fun x => fderiv ℝ Ψ (state G x)
(stateDerivative G x))`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_bounds`,
`chebyshev2.Filters.nonlinear_le_coordinate`,
`chebyshev2.GroundState.GroundWitness.coordinate_mem` with the arguments shown in the
proof.
-/
theorem state_mem_box (x : ℝ) : state G x ∈ stateBox (groundParameter hm hn) := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_bounds`,
  -- `chebyshev2.Filters.nonlinear_le_coordinate`,
  -- `chebyshev2.GroundState.GroundWitness.coordinate_mem` with the arguments shown in the
  -- proof.
  have h0 := nonlinear_bounds hm hn (by norm_num : (0:ℝ) ≤ 32) x
  have h1 := nonlinear_bounds hm hn (by norm_num : (0:ℝ) ≤ 64) x
  have hb0 := nonlinear_le_coordinate G (by norm_num : (0:ℝ) ≤ 32) x
  have hb1 := nonlinear_le_coordinate G (by norm_num : (0:ℝ) ≤ 64) x
  have hq := G.coordinate_mem x
  have hh := defect_bounds G x
  refine ⟨hq,⟨⟨div_nonneg h0.1 (by norm_num),?_⟩,
    ⟨⟨div_nonneg h1.1 (by norm_num),?_⟩,⟨hh.1,hh.2.trans hq.2⟩⟩⟩⟩
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<32)).2
    have he : (32/groundParameter hm hn)*G.q x ≤ 32*(2/groundParameter hm hn) := by
      have h := mul_le_mul_of_nonneg_left hq.2 (div_nonneg (by norm_num : (0:ℝ) ≤ 32) G.coupling_positive.le)
      convert h using 1
      ring
    linarith
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<64)).2
    have he : (64/groundParameter hm hn)*G.q x ≤ 64*(2/groundParameter hm hn) := by
      have h := mul_le_mul_of_nonneg_left hq.2 (div_nonneg (by norm_num : (0:ℝ) ≤ 64) G.coupling_positive.le)
      convert h using 1
      ring
    linarith

omit G in
/--
The precise assertion is `IsCompact (stateBox κ)`.

Use: `chebyshev2.Residual.statePotential_derivative_integrable` uses this assertion to
establish integrability of the displayed function: `Integrable (fun x => fderiv ℝ Ψ (state G x)
(stateDerivative G x))`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem stateBox_compact (κ : ℝ) : IsCompact (stateBox κ) :=
  isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

omit G in
/--
The precise assertion is `Convex ℝ (stateBox κ)`.

Use: `chebyshev2.Residual.statePotential_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (fun x => Ψ
(state G x)) a b`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem stateBox_convex (κ : ℝ) : Convex ℝ (stateBox κ) :=
  (convex_Icc _ _).prod ((convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _)))

/--
The precise assertion is `stateDerivative G x= m x • inputVector (groundParameter hm
hn)-driftVector (state G x)`.

Use: `chebyshev2.Residual.statePotential_drift` rewrites with this identity to establish
the precise assertion is `fderiv ℝ Ψ (state G x) (stateDerivative G x)= bPotential
(groundParameter hm hn) Ψ (state G x)*m x-dPotential Ψ (state G x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Filters.state_polynomial_drift` with the
arguments shown in the proof.
-/
theorem state_drift (x : ℝ) : stateDerivative G x=
    m x • inputVector (groundParameter hm hn)-driftVector (state G x) := by
  rw [state_polynomial_drift G]
  simp only [inputVector,driftVector,Q,Prod.smul_mk,Prod.mk_sub_mk,smul_eq_mul,mul_one,mul_zero,zero_sub]
  congr 1
  · ring
  · ext <;> ring

variable {Ψ : State → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
include hΨ

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (fun x => Ψ
(state G x)) a b`.

Use: `chebyshev2.Residual.statePotential_null` uses this identity to establish exact
identity `(∫ x, fderiv ℝ Ψ (state G x) (stateDerivative G x))=0`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Residual.stateBox_convex`,
`chebyshev2.Residual.stateBox_compact`, `chebyshev2.Residual.state_mem_box` with the
arguments shown in the proof.
-/
theorem statePotential_locallyAC (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => Ψ (state G x)) a b := by
  obtain ⟨K,hK⟩ := (hΨ.contDiffOn (s := stateBox (groundParameter hm hn))).exists_lipschitzOnWith
    (by norm_num) (stateBox_convex _) (stateBox_compact _)
  exact hK.comp_absolutelyContinuousOnInterval (fun x _ => state_mem_box G x) (state_locallyAC G a b)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => Ψ
(state G x)) (fderiv ℝ Ψ (state G x) (stateDerivative G x)) x`.

Use: `chebyshev2.Residual.statePotential_null` uses this identity to establish exact
identity `(∫ x, fderiv ℝ Ψ (state G x) (stateDerivative G x))=0`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem statePotential_derivative : ∀ᵐ x, HasDerivAt (fun x => Ψ (state G x))
    (fderiv ℝ Ψ (state G x) (stateDerivative G x)) x := by
  filter_upwards [state_derivative G] with x hx
  exact (hΨ.differentiable (by norm_num) (state G x)).hasFDerivAt.comp_hasDerivAt x hx

/--
Integrability of the displayed function: `Integrable (fun x => fderiv ℝ Ψ (state G x)
(stateDerivative G x))`.

Use: `chebyshev2.Residual.statePotential_null` uses this integrability result to establish
exact identity `(∫ x, fderiv ℝ Ψ (state G x) (stateDerivative G x))=0`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Residual.stateBox_compact`,
`chebyshev2.GroundState.RiccatiData.q_continuous`,
`chebyshev2.Filters.nonlinear_continuous` with the arguments shown in the proof.
-/
theorem statePotential_derivative_integrable :
    Integrable (fun x => fderiv ℝ Ψ (state G x) (stateDerivative G x)) := by
  -- Establish continuity hfc before using the function at limits or in calculus arguments.
  have hfc : Continuous (fderiv ℝ Ψ) := hΨ.continuous_fderiv (by norm_num)
  obtain ⟨M,hM⟩ := (stateBox_compact (groundParameter hm hn)).exists_bound_of_continuousOn hfc.continuousOn
  -- Establish continuity hstate before using the function at limits or in calculus arguments.
  have hstate : Continuous (state G) := by
    exact G.R.q_continuous.prodMk ((nonlinear_continuous hm hn (by norm_num : (0:ℝ) ≤ 32)).div_const 32 |>.prodMk
      (((nonlinear_continuous hm hn (by norm_num : (0:ℝ) ≤ 64)).div_const 64).prodMk
        (locallyAC_continuous (defect_locallyAC G))))
  apply ((state_derivative_integrable G).norm.const_mul M).mono'
  · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (((hfc.comp hstate).aestronglyMeasurable).prodMk
        (state_derivative_integrable G).aestronglyMeasurable)
  · exact Eventually.of_forall (fun x => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hM _ (state_mem_box G x)) (norm_nonneg _)))

/--
Exact identity `(∫ x, fderiv ℝ Ψ (state G x) (stateDerivative G x))=0`.

Use: `chebyshev2.Calibration.Data.flowResidual_integral` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem statePotential_null (hend : Ψ (0,0,0,0)=Ψ (2,0,0,2)) :
    (∫ x, fderiv ℝ Ψ (state G x) (stateDerivative G x))=0 := by
  have h := integral_derivative_eq_limits (statePotential_locallyAC G hΨ)
    (statePotential_derivative G hΨ) (statePotential_derivative_integrable G hΨ)
    (hΨ.continuous.continuousAt.tendsto.comp (state_limits G).1)
    (hΨ.continuous.continuousAt.tendsto.comp (state_limits G).2)
  rw [hend,sub_self] at h
  exact h

omit hΨ in
/--
The precise assertion is `fderiv ℝ Ψ (state G x) (stateDerivative G x)= bPotential
(groundParameter hm hn) Ψ (state G x)*m x-dPotential Ψ (state G x)`.

Use: `chebyshev2.Calibration.Data.flowResidual_decomposition` rewrites with this identity
to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Residual.state_drift` with the arguments
shown in the proof.
-/
theorem statePotential_drift (x : ℝ) :
    fderiv ℝ Ψ (state G x) (stateDerivative G x)=
      bPotential (groundParameter hm hn) Ψ (state G x)*m x-dPotential Ψ (state G x) := by
  rw [state_drift G]
  simp only [map_sub,map_smul,smul_eq_mul,bPotential,dPotential]
  ring

end
end chebyshev2.Residual
