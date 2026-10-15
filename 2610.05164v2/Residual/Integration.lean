import «2610.05164v2».Comparison.Integrability
import «2610.05164v2».Residual.StatePotential
import «2610.05164v2».Residual.Pointwise
import «2610.05164v2».Residual.Price

/-!
Article: 2610.05164v2, Proposition 8.
Proposition 8's integration step with the actual comparison coefficients.
Use: `«2610.05164v2».Calibration.Data.energy_ge_base_add_comparison` feeds
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` (Proposition 8, including the endpoint
condition at zero amplitude).
Proof chain: `«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` — 2610.05164v2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».GroundState «2610.05164v2».Filters «2610.05164v2».Calibration «2610.05164v2».Residual
set_option backward.isDefEq.respectTransparency false
variable (C : Data) {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x}
  (G : GroundWitness hm hn)

/--
Defines `comparisonMultiplier` of type `ℝ` by `ξ₀*C.comparisonA G.coupling_positive 32 (G.q x)
(nonlinear 32 m x)+ ξ₁*C.comparisonA G.coupling_positive 64 (G.q x) (nonlinear 64 m x)+
χ*C.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)`.

Use: `«2610.05164v2».Calibration.Data.comparisonDefect` uses this definition in the displayed
construction of `comparisonDefect`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def comparisonMultiplier (ξ₀ ξ₁ χ x : ℝ) : ℝ :=
  ξ₀*C.comparisonA G.coupling_positive 32 (G.q x) (nonlinear 32 m x)+
  ξ₁*C.comparisonA G.coupling_positive 64 (G.q x) (nonlinear 64 m x)+
  χ*C.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)

/--
Defines `comparisonDefect` of type `ℝ` by `C.comparisonMultiplier G ξ₀ ξ₁ χ x*(m x-(C.amplitude
(groundParameter hm hn) (G.q x))^2)`.

Use: `«2610.05164v2».Calibration.Data.comparisonDefect_integrable` uses this definition to
establish integrability of the displayed function: `Integrable (C.comparisonDefect G ξ₀ ξ₁ χ)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def comparisonDefect (ξ₀ ξ₁ χ x : ℝ) : ℝ :=
  C.comparisonMultiplier G ξ₀ ξ₁ χ x*(m x-(C.amplitude (groundParameter hm hn) (G.q x))^2)

/--
Integrability of the displayed function: `Integrable (C.comparisonDefect G ξ₀ ξ₁ χ)`.

Use: `«2610.05164v2».Calibration.Data.flowResidual_integrable` uses this integrability result
to establish integrability of the displayed function: `Integrable (C.flowResidual G ξ₀ ξ₁ χ τ η
Ψ)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.comparisonA_integrable`,
`«2610.05164v2».Calibration.Data.comparisonA0_integrable` with the arguments shown in the
proof.
-/
theorem comparisonDefect_integrable (ξ₀ ξ₁ χ : ℝ) : Integrable (C.comparisonDefect G ξ₀ ξ₁ χ) := by
  apply ((((C.comparisonA_integrable G (by norm_num : (0:ℝ) ≤ 32)).const_mul ξ₀).add
    ((C.comparisonA_integrable G (by norm_num : (0:ℝ) ≤ 64)).const_mul ξ₁)).add
      ((C.comparisonA0_integrable G).const_mul χ)).congr
  exact Eventually.of_forall (fun x => by dsimp [comparisonDefect,comparisonMultiplier]; ring)

/--
Defines `flowResidual` of type `ℝ` by `residual (groundParameter hm hn) (C.amplitude
(groundParameter hm hn) (G.q x)) (Q (G.q x)) (C.comparisonMultiplier G ξ₀ ξ₁ χ x) (η.value (G.q
x)) τ (bPotential (groundParameter hm hn) Ψ (state G x)) (dPotential Ψ (state G x)) (sqrt (m
x))`.

Use: `«2610.05164v2».Calibration.Data.flowResidual_decomposition` uses this definition to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def flowResidual (ξ₀ ξ₁ χ τ : ℝ) (η : Price) (Ψ : State → ℝ) (x : ℝ) : ℝ :=
  residual (groundParameter hm hn) (C.amplitude (groundParameter hm hn) (G.q x))
    (Q (G.q x)) (C.comparisonMultiplier G ξ₀ ξ₁ χ x) (η.value (G.q x)) τ
    (bPotential (groundParameter hm hn) Ψ (state G x)) (dPotential Ψ (state G x)) (sqrt (m x))

/--
The precise assertion is `C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x= rho (sqrt (m x)) (C.amplitude
(groundParameter hm hn) (G.q x))- C.comparisonDefect G ξ₀ ξ₁ χ x+ (η.value (G.q
x)*(groundParameter hm hn*m x-Q (G.q x)))/groundParameter hm hn+ τ/groundParameter hm hn*Q (G.q
x)+ fderiv ℝ Ψ (state G x) (stateDerivative G x)`.

Use: `«2610.05164v2».Calibration.Data.flowResidual_integrable` uses this identity to establish
integrability of the displayed function: `Integrable (C.flowResidual G ξ₀ ξ₁ χ τ η Ψ)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Residual.statePotential_drift` with the
arguments shown in the proof.
-/
theorem flowResidual_decomposition (ξ₀ ξ₁ χ τ : ℝ) (η : Price) (Ψ : State → ℝ) (x : ℝ) :
    C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x=
      rho (sqrt (m x)) (C.amplitude (groundParameter hm hn) (G.q x))-
        C.comparisonDefect G ξ₀ ξ₁ χ x+
      (η.value (G.q x)*(groundParameter hm hn*m x-Q (G.q x)))/groundParameter hm hn+
      τ/groundParameter hm hn*Q (G.q x)+
      fderiv ℝ Ψ (state G x) (stateDerivative G x) := by
  -- Use the identities/estimates `«2610.05164v2».Residual.statePotential_drift` with the
  -- arguments shown in the proof.
  rw [statePotential_drift G]
  unfold flowResidual «2610.05164v2».Residual.residual comparisonDefect
  rw [sq_sqrt (hn x)]
  ring

/--
Integrability of the displayed function: `Integrable (fun x => η.value (G.q x)*(groundParameter
hm hn*m x-Q (G.q x)))`.

Use: `«2610.05164v2».Calibration.Data.flowResidual_integrable` uses this integrability result
to establish integrability of the displayed function: `Integrable (C.flowResidual G ξ₀ ξ₁ χ τ η
Ψ)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coordinate_integrability`,
`«2610.05164v2».Residual.Price.measurable`,
`«2610.05164v2».GroundState.RiccatiData.q_continuous` with the arguments shown in the proof.
-/
theorem flowPrice_integrable (η : Price) :
    Integrable (fun x => η.value (G.q x)*(groundParameter hm hn*m x-Q (G.q x))) :=
  G.coordinate_integrability.2.bdd_mul
    (η.measurable.comp G.R.q_continuous.measurable).aestronglyMeasurable
    (Eventually.of_forall (fun x => η.bound (G.q x)))

/--
Integrability of the displayed function: `Integrable (C.flowResidual G ξ₀ ξ₁ χ τ η Ψ)`.

Use: a standalone supporting integrability result for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 8.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.rho_integrable`,
`«2610.05164v2».Calibration.Data.comparisonDefect_integrable`,
`«2610.05164v2».Calibration.Data.flowPrice_integrable` with the arguments shown in the proof.
-/
theorem flowResidual_integrable (ξ₀ ξ₁ χ τ : ℝ) (η : Price) {Ψ : State → ℝ}
    (hΨ : ContDiff ℝ 1 Ψ) (hE : Integrable (fun x => (sqrt (m x))^3)) :
    Integrable (C.flowResidual G ξ₀ ξ₁ χ τ η Ψ) := by
  apply (((((C.rho_integrable G hE).sub (C.comparisonDefect_integrable G ξ₀ ξ₁ χ)).add
    ((flowPrice_integrable G η).div_const (groundParameter hm hn))).add
      (G.coordinate_integrability.1.const_mul (τ/groundParameter hm hn))).add
        (statePotential_derivative_integrable G hΨ)).congr
  exact Eventually.of_forall (fun x => (C.flowResidual_decomposition G ξ₀ ξ₁ χ τ η Ψ x).symm)

/--
The precise assertion is `(∫ x, C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x)= (∫ x, rho (sqrt (m x))
(C.amplitude (groundParameter hm hn) (G.q x)))- (∫ x, C.comparisonDefect G ξ₀ ξ₁ χ x)+priceCost
(groundParameter hm hn) τ η.value`.

Use: `«2610.05164v2».Calibration.Data.energy_ge_base_add_comparison` rewrites with this
identity to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem flowResidual_integral (ξ₀ ξ₁ χ τ : ℝ) (η : Price) {Ψ : State → ℝ}
    (hΨ : ContDiff ℝ 1 Ψ) (hend : Ψ (0,0,0,0)=Ψ (2,0,0,2))
    (hM : (∫ x, m x)=1) (hE : Integrable (fun x => (sqrt (m x))^3)) :
    (∫ x, C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x)=
      (∫ x, rho (sqrt (m x)) (C.amplitude (groundParameter hm hn) (G.q x)))-
      (∫ x, C.comparisonDefect G ξ₀ ξ₁ χ x)+priceCost (groundParameter hm hn) τ η.value := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let A : ℝ → ℝ := fun x => rho (sqrt (m x)) (C.amplitude (groundParameter hm hn) (G.q x))
  let B := C.comparisonDefect G ξ₀ ξ₁ χ
  let P : ℝ → ℝ := fun x => η.value (G.q x)*(groundParameter hm hn*m x-Q (G.q x))/groundParameter hm hn
  let M : ℝ → ℝ := fun x => τ/groundParameter hm hn*Q (G.q x)
  let N : ℝ → ℝ := fun x => fderiv ℝ Ψ (state G x) (stateDerivative G x)
  -- Establish iA as the integrability justification for the later integral estimates or
  -- changes of order.
  have iA : Integrable A := C.rho_integrable G hE
  -- Establish iB as the integrability justification for the later integral estimates or
  -- changes of order.
  have iB : Integrable B := C.comparisonDefect_integrable G ξ₀ ξ₁ χ
  -- Establish iP as the integrability justification for the later integral estimates or
  -- changes of order.
  have iP : Integrable P := (flowPrice_integrable G η).div_const _
  -- Establish iM as the integrability justification for the later integral estimates or
  -- changes of order.
  have iM : Integrable M := G.coordinate_integrability.1.const_mul _
  -- Establish iN as the integrability justification for the later integral estimates or
  -- changes of order.
  have iN : Integrable N := statePotential_derivative_integrable G hΨ
  have he : C.flowResidual G ξ₀ ξ₁ χ τ η Ψ=A-B+P+M+N :=
    funext (C.flowResidual_decomposition G ξ₀ ξ₁ χ τ η Ψ)
  have e1 : (∫ x, (A-B+P+M+N) x)=(∫ x, (A-B+P+M) x)+∫ x, N x :=
    integral_add (((iA.sub iB).add iP).add iM) iN
  have e2 : (∫ x, (A-B+P+M) x)=(∫ x, (A-B+P) x)+∫ x, M x :=
    integral_add ((iA.sub iB).add iP) iM
  have e3 : (∫ x, (A-B+P) x)=(∫ x, (A-B) x)+∫ x, P x :=
    integral_add (iA.sub iB) iP
  have e4 : (∫ x, (A-B) x)=(∫ x, A x)-∫ x, B x := integral_sub iA iB
  rw [he,e1,e2,e3,e4]
  dsimp only [A,B,P,M,N]
  rw [statePotential_null G hΨ hend,add_zero,integral_div,η.ground_price_identity G,integral_const_mul]
  have hQ : (∫ x, Q (G.q x))=groundParameter hm hn-2 := by
    simpa only [Q,hM,mul_one] using G.coordinate_mass
  rw [hQ]
  unfold priceCost
  ring

/--
The residual lower bound before replacing the actual signed comparison integral by the
observation differences of Theorem 3.4.

Use: `«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` uses this bound to establish
the bound stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.T_nonneg`,
`«2610.05164v2».Calibration.Data.base_identity`,
`«2610.05164v2».Calibration.Data.rho_integrable` with the arguments shown in the proof.
-/
theorem energy_ge_base_add_comparison (ξ₀ ξ₁ χ τ : ℝ) (η : Price) {Ψ : State → ℝ}
    (hΨ : ContDiff ℝ 1 Ψ) (hend : Ψ (0,0,0,0)=Ψ (2,0,0,2))
    (hM : (∫ x, m x)=1) (hE : Integrable (fun x => (sqrt (m x))^3))
    (hR : ∀ᵐ x, 0 ≤ C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x) :
    C.base (groundParameter hm hn)
      («2610.05164v2».Continuum.logDeterminant («2610.05164v2».Continuum.kernelEigenvalue hm hn)
        (C.sigma*groundParameter hm hn))+
      (∫ x, C.comparisonDefect G ξ₀ ξ₁ χ x)-priceCost (groundParameter hm hn) τ η.value ≤
        ∫ x, (sqrt (m x))^3 := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.T_nonneg`,
  -- `«2610.05164v2».Calibration.Data.base_identity`,
  -- `«2610.05164v2».Calibration.Data.rho_integrable` with the arguments shown in the proof.
  have hr := integral_nonneg_of_ae hR
  rw [C.flowResidual_integral G ξ₀ ξ₁ χ τ η hΨ hend hM hE] at hr
  have ht : 0 ≤ ∫ x, C.omega*C.T (G.q x) (C.calibrationState G x) :=
    integral_nonneg (fun x => mul_nonneg C.omega_nonneg (C.T_nonneg G x))
  rw [C.base_identity G hM hE,integral_add (C.rho_integrable G hE)
    ((C.T_integrable G).const_mul C.omega)]
  linarith

end
end «2610.05164v2».Calibration.Data
