import chebyshev2.Residual.Integration
import chebyshev2.Comparison.TraceComparison
import chebyshev2.HalfLine.FilterMeasure

/-!
Article: chebyshev2, Proposition 8.
Proposition 8 with the literal state region and spectral observations.
Use: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` feeds
`chebyshev2.DualCertificate.AnalyticData.energy_ge_value` (energy ge value).
-/
namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.GroundState chebyshev2.Filters chebyshev2.Calibration chebyshev2.Residual
set_option backward.isDefEq.respectTransparency false
variable (C : Data)

/--
Defines `stateComparisonMultiplier` of type `ℝ` by `ξ₀*C.comparisonA hκ 32 Y.1 (32*Y.2.1)+
ξ₁*C.comparisonA hκ 64 Y.1 (64*Y.2.2.1)+ χ*C.comparisonA0 hκ Y.1 (Y.1-Y.2.2.2)`.

Use: `chebyshev2.Calibration.Data.flowResidual_eq_stateResidual` rewrites with this
definition to establish `C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x=
C.stateResidual G.coupling_positive ξ₀ ξ₁ χ τ η Ψ (state G x) (sqrt (m x))`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def stateComparisonMultiplier {κ : ℝ} (hκ : 0 < κ) (ξ₀ ξ₁ χ : ℝ) (Y : State) : ℝ :=
  ξ₀*C.comparisonA hκ 32 Y.1 (32*Y.2.1)+
  ξ₁*C.comparisonA hκ 64 Y.1 (64*Y.2.2.1)+
  χ*C.comparisonA0 hκ Y.1 (Y.1-Y.2.2.2)

/--
Defines `stateResidual` of type `ℝ` by `residual κ (C.amplitude κ Y.1) (Q Y.1)
(C.stateComparisonMultiplier hκ ξ₀ ξ₁ χ Y) (η.value Y.1) τ (bPotential κ Ψ Y) (dPotential Ψ Y)
n`.

Use: `chebyshev2.Calibration.Data.flowResidual_eq_stateResidual` rewrites with this
definition to establish `C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x=
C.stateResidual G.coupling_positive ξ₀ ξ₁ χ τ η Ψ (state G x) (sqrt (m x))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def stateResidual {κ : ℝ} (hκ : 0 < κ) (ξ₀ ξ₁ χ τ : ℝ) (η : Price)
    (Ψ : State → ℝ) (Y : State) (n : ℝ) : ℝ :=
  residual κ (C.amplitude κ Y.1) (Q Y.1) (C.stateComparisonMultiplier hκ ξ₀ ξ₁ χ Y)
    (η.value Y.1) τ (bPotential κ Ψ Y) (dPotential Ψ Y) n

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)

/--
The precise assertion is `C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x= C.stateResidual G.coupling_positive
ξ₀ ξ₁ χ τ η Ψ (state G x) (sqrt (m x))`.

Use: `chebyshev2.Calibration.Data.flowResidual_nonneg_of_statewise` rewrites with this
identity to prove the eventual or almost-everywhere assertion `∀ᵐ x, 0 ≤
C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem flowResidual_eq_stateResidual (ξ₀ ξ₁ χ τ : ℝ) (η : Price) (Ψ : State → ℝ) (x : ℝ) :
    C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x=
      C.stateResidual G.coupling_positive ξ₀ ξ₁ χ τ η Ψ (state G x) (sqrt (m x)) := by
  simp only [flowResidual,stateResidual,comparisonMultiplier,stateComparisonMultiplier,state,defect,
    mul_div_cancel₀ _ (by norm_num : (32:ℝ) ≠ 0),
    mul_div_cancel₀ _ (by norm_num : (64:ℝ) ≠ 0),sub_sub_cancel]

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, 0 ≤ C.flowResidual G ξ₀
ξ₁ χ τ η Ψ x`.

Use: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` uses this bound to establish
the bound stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `G.q x=0 ∨ G.q x=2` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then
prove the asserted relation at an arbitrary point in that intersection.
-/
theorem flowResidual_nonneg_of_statewise (ξ₀ ξ₁ χ τ : ℝ) (η : Price) (Ψ : State → ℝ)
    (hinterior : ∀ Y ∈ (chebyshev2.HalfLine.stateScales G).states,
      0 < Y.1 → Y.1 < 2 → ∀ n, 0 ≤ n →
        0 ≤ C.stateResidual G.coupling_positive ξ₀ ξ₁ χ τ η Ψ Y n)
    (hboundary : ∀ Y ∈ (chebyshev2.HalfLine.stateScales G).states,
      Y.1=0 ∨ Y.1=2 → 0 ≤ C.stateResidual G.coupling_positive ξ₀ ξ₁ χ τ η Ψ Y 0) :
    ∀ᵐ x, 0 ≤ C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x := by
  -- Separate `G.q x=0 ∨ G.q x=2` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  filter_upwards [derivative_zero_on_level_ae G.q 0,derivative_zero_on_level_ae G.q 2,
    G.coordinate_derivative] with x h0 h2 hq
  rw [C.flowResidual_eq_stateResidual G]
  by_cases hb : G.q x=0 ∨ G.q x=2
  · have hd : groundParameter hm hn*m x=0 := by
      rcases hb with hz | hz
      · have h := h0 hz _ hq
        simpa only [hz,zero_mul,sub_zero] using h
      · have h := h2 hz _ hq
        simpa only [hz,sub_self,mul_zero,sub_zero] using h
    have hm0 : m x=0 := (mul_eq_zero.mp hd).resolve_left G.coupling_positive.ne'
    rw [hm0,sqrt_zero]
    exact hboundary _ (chebyshev2.HalfLine.state_mem G x) hb
  · exact hinterior _ (chebyshev2.HalfLine.state_mem G x)
      (lt_of_le_of_ne (G.coordinate_mem x).1 (Ne.symm (not_or.mp hb).1))
      (lt_of_le_of_ne (G.coordinate_mem x).2 (not_or.mp hb).2) _ (sqrt_nonneg _)

/--
Defines `determinantDifference` of type `ℝ`. The displayed construction fixes its component
data; its proof fields enforce the listed compatibility properties.

Use: `chebyshev2.Calibration.Data.comparisonDefect_integral` uses this definition to
establish the precise assertion is `(∫ x, C.comparisonDefect G ξ₀ ξ₁ χ x)=
ξ₀*C.determinantDifference G 32+ξ₁*C.determinantDifference G 64+χ*C.traceDifference G`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def determinantDifference (s : ℝ) : ℝ :=
  chebyshev2.Continuum.logDeterminant (chebyshev2.Continuum.kernelEigenvalue hm hn) s-
    chebyshev2.Continuum.logDeterminant
      (chebyshev2.Continuum.kernelEigenvalue
        ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive)
        ((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive)) s

/--
Defines `traceDifference` of type `ℝ` by `(∫ x, (linear hm hn x)^2)- (∫ x, (linear
((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive)
((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive) x)^2)`.

Use: `chebyshev2.Calibration.Data.comparisonDefect_integral` uses this definition to
establish the precise assertion is `(∫ x, C.comparisonDefect G ξ₀ ξ₁ χ x)=
ξ₀*C.determinantDifference G 32+ξ₁*C.determinantDifference G 64+χ*C.traceDifference G`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def traceDifference : ℝ :=
  (∫ x, (linear hm hn x)^2)-
    (∫ x, (linear ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive)
      ((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive) x)^2)

/--
The precise assertion is `(∫ x, C.comparisonDefect G ξ₀ ξ₁ χ x)= ξ₀*C.determinantDifference G
32+ξ₁*C.determinantDifference G 64+χ*C.traceDifference G`.

Use: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` rewrites with this identity to
establish the bound stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem comparisonDefect_integral (ξ₀ ξ₁ χ : ℝ) :
    (∫ x, C.comparisonDefect G ξ₀ ξ₁ χ x)=
      ξ₀*C.determinantDifference G 32+ξ₁*C.determinantDifference G 64+χ*C.traceDifference G := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let D₀ : ℝ → ℝ := fun x => ξ₀*C.comparisonA G.coupling_positive 32 (G.q x) (nonlinear 32 m x)*
    (m x-(C.amplitude (groundParameter hm hn) (G.q x))^2)
  let D₁ : ℝ → ℝ := fun x => ξ₁*C.comparisonA G.coupling_positive 64 (G.q x) (nonlinear 64 m x)*
    (m x-(C.amplitude (groundParameter hm hn) (G.q x))^2)
  let D₂ : ℝ → ℝ := fun x => χ*C.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)*
    (m x-(C.amplitude (groundParameter hm hn) (G.q x))^2)
  -- Establish i₀ as the integrability justification for the later integral estimates or
  -- changes of order.
  have i₀ : Integrable D₀ := by
    convert (C.comparisonA_integrable G (by norm_num : (0:ℝ) ≤ 32)).const_mul ξ₀ using 1
    funext x; dsimp [D₀]; ring
  -- Establish i₁ as the integrability justification for the later integral estimates or
  -- changes of order.
  have i₁ : Integrable D₁ := by
    convert (C.comparisonA_integrable G (by norm_num : (0:ℝ) ≤ 64)).const_mul ξ₁ using 1
    funext x; dsimp [D₁]; ring
  -- Establish i₂ as the integrability justification for the later integral estimates or
  -- changes of order.
  have i₂ : Integrable D₂ := by
    convert (C.comparisonA0_integrable G).const_mul χ using 1
    funext x; dsimp [D₂]; ring
  have he : C.comparisonDefect G ξ₀ ξ₁ χ=D₀+D₁+D₂ := by
    funext x
    dsimp [comparisonDefect,comparisonMultiplier,D₀,D₁,D₂]
    ring
  have e₁ : (∫ x, (D₀+D₁+D₂) x)=(∫ x, (D₀+D₁) x)+∫ x, D₂ x := integral_add (i₀.add i₁) i₂
  have e₂ : (∫ x, (D₀+D₁) x)=(∫ x, D₀ x)+∫ x, D₁ x := integral_add i₀ i₁
  rw [he,e₁,e₂]
  dsimp only [D₀,D₁,D₂]
  simp_rw [mul_assoc,integral_const_mul]
  rw [← C.signed_determinant_comparison G (by norm_num : (0:ℝ) ≤ 32),
    ← C.signed_determinant_comparison G (by norm_num : (0:ℝ) ≤ 64),← C.signed_trace_comparison G]
  rfl

/--
Proposition 8, including the endpoint condition at zero amplitude.

Use: `chebyshev2.DualCertificate.AnalyticData.energy_ge_value` uses this bound to establish
the bound stated in that declaration.

Article: chebyshev2, Theorem 3.5.

Proof: Use the identities/estimates
`chebyshev2.Calibration.Data.comparisonDefect_integral`,
`chebyshev2.Calibration.Data.energy_ge_base_add_comparison`,
`chebyshev2.Calibration.Data.flowResidual_nonneg_of_statewise` with the arguments shown in
the proof.
-/
theorem energy_ge_spectral_bound (ξ₀ ξ₁ χ τ : ℝ) (η : Price) {Ψ : State → ℝ}
    (hΨ : ContDiff ℝ 1 Ψ) (hend : Ψ (0,0,0,0)=Ψ (2,0,0,2))
    (hM : (∫ x, m x)=1) (hE : Integrable (fun x => (sqrt (m x))^3))
    (hinterior : ∀ Y ∈ (chebyshev2.HalfLine.stateScales G).states,
      0 < Y.1 → Y.1 < 2 → ∀ n, 0 ≤ n →
        0 ≤ C.stateResidual G.coupling_positive ξ₀ ξ₁ χ τ η Ψ Y n)
    (hboundary : ∀ Y ∈ (chebyshev2.HalfLine.stateScales G).states,
      Y.1=0 ∨ Y.1=2 → 0 ≤ C.stateResidual G.coupling_positive ξ₀ ξ₁ χ τ η Ψ Y 0) :
    C.base (groundParameter hm hn)
      (chebyshev2.Continuum.logDeterminant (chebyshev2.Continuum.kernelEigenvalue hm hn)
        (C.sigma*groundParameter hm hn))+
      (ξ₀*C.determinantDifference G 32+ξ₁*C.determinantDifference G 64+χ*C.traceDifference G)-
        priceCost (groundParameter hm hn) τ η.value ≤ ∫ x, (sqrt (m x))^3 := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.comparisonDefect_integral`,
  -- `chebyshev2.Calibration.Data.energy_ge_base_add_comparison`,
  -- `chebyshev2.Calibration.Data.flowResidual_nonneg_of_statewise` with the arguments
  -- shown in the proof.
  rw [← C.comparisonDefect_integral G]
  exact C.energy_ge_base_add_comparison G ξ₀ ξ₁ χ τ η hΨ hend hM hE
    (C.flowResidual_nonneg_of_statewise G ξ₀ ξ₁ χ τ η Ψ hinterior hboundary)

end
end chebyshev2.Calibration.Data
