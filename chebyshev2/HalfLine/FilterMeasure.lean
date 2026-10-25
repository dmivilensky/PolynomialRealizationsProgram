import chebyshev2.HalfLine.GroundResolvent
import chebyshev2.HalfLine.JostResolvent
import chebyshev2.HalfLine.MeasureIdentities
import chebyshev2.Filters.StateFlow

/-!
Article: chebyshev2, Proposition 7.
Proposition 7 for the literal ODE state and the actual density parameter.
Use: `chebyshev2.HalfLine.state_mem` feeds
`chebyshev2.Calibration.Data.flowResidual_nonneg_of_statewise` (flow Residual nonneg of
statewise).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.HalfLine
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t} (G : GroundWitness hm hn)

/--
The precise assertion is `IsProbabilityMeasure (commonMeasure G x)`.

Use: `chebyshev2.HalfLine.state_mem` uses this assertion to establish membership in the
specified domain/enclosure: `Filters.state G x ∈ (stateScales G).states`.

Article: chebyshev2, Theorem 3.3.

Proof: Use the identities/estimates `chebyshev2.HalfLine.commonMeasure_probability`,
`chebyshev2.HalfLine.groundQuadratic_eq_coordinate` with the arguments shown in the proof.
-/
theorem commonMeasure_ode_probability {x : ℝ} (hq : 0 < G.q x) :
    IsProbabilityMeasure (commonMeasure G x) :=
  commonMeasure_probability G x (by rw [groundQuadratic_eq_coordinate]; exact hq)

/--
Theorem 3.3, with one actual measure for every positive scale.

The precise assertion is `groundParameter hm hn*Filters.nonlinear s m x/(s*G.q x)= ∫ z,
(1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure G x`.

Use: `chebyshev2.HalfLine.state_mem` uses this identity to establish membership in the
specified domain/enclosure: `Filters.state G x ∈ (stateScales G).states`.

Article: chebyshev2, Theorem 3.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem commonMeasure_filter {x : ℝ} (hq : 0 < G.q x) {s : ℝ} (hs : 0 < s) :
    groundParameter hm hn*Filters.nonlinear s m x/(s*G.q x)=
      ∫ z, (1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure G x := by
  rw [commonMeasure_response G x (by rw [groundQuadratic_eq_coordinate]; exact hq) s hs.le,
    groundQuadratic_eq_coordinate, ← responseQuadratic_eq_nonlinear hm hn hs.le]
  field_simp

/--
Exact identity `Filters.linear hm hn x/G.q x=∫ z, 1-z ∂commonMeasure G x`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 3.3.

Proof: Use the identities/estimates `chebyshev2.HalfLine.commonMeasure_linear`,
`chebyshev2.HalfLine.groundQuadratic_eq_coordinate`,
`chebyshev2.HalfLine.linear_eq_vector_norm` with the arguments shown in the proof.
-/
theorem commonMeasure_linear_filter {x : ℝ} (hq : 0 < G.q x) :
    Filters.linear hm hn x/G.q x=∫ z, 1-z ∂commonMeasure G x := by
  rw [commonMeasure_linear G x (by rw [groundQuadratic_eq_coordinate]; exact hq),
    groundQuadratic_eq_coordinate, linear_eq_vector_norm]
  ring

/--
Exact identity `Filters.defect G x/G.q x=∫ z, z ∂commonMeasure G x`.

Use: `chebyshev2.HalfLine.state_mem` uses this identity to establish membership in the
specified domain/enclosure: `Filters.state G x ∈ (stateScales G).states`.

Article: chebyshev2, Theorem 3.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem commonMeasure_defect {x : ℝ} (hq : 0 < G.q x) :
    Filters.defect G x/G.q x=∫ z, z ∂commonMeasure G x := by
  rw [commonMeasure_mean G x (by rw [groundQuadratic_eq_coordinate]; exact hq),
    groundQuadratic_eq_coordinate]
  dsimp only [Filters.defect]
  field_simp

/--
The zero-coordinate case of Theorem 3.3.

Exact identity `Filters.linear hm hn x=0 ∧ ∀ s, 0 ≤ s → Filters.nonlinear s m x=0`.

Use: `chebyshev2.HalfLine.state_mem` uses this identity to establish membership in the
specified domain/enclosure: `Filters.state G x ∈ (stateScales G).states`.

Article: chebyshev2, Theorem 3.3.

Proof: Use the identities/estimates `chebyshev2.HalfLine.zero_quadratics`,
`chebyshev2.HalfLine.groundQuadratic_eq_coordinate`,
`chebyshev2.HalfLine.responseQuadratic_eq_nonlinear` with the arguments shown in the proof.
-/
theorem zero_filters {x : ℝ} (hq : G.q x=0) :
    Filters.linear hm hn x=0 ∧ ∀ s, 0 ≤ s → Filters.nonlinear s m x=0 := by
  have hz := zero_quadratics G x (by rw [groundQuadratic_eq_coordinate,hq])
  refine ⟨hz.1,?_⟩
  intro s hs
  rw [← responseQuadratic_eq_nonlinear hm hn hs x, hz.2 s hs, mul_zero]

/--
Defines `stateScales` of type `chebyshev2.StateRegion.Scales` by `⟨groundParameter hm
hn,32,32,G.coupling_positive,by norm_num,by norm_num⟩`.

Use: `chebyshev2.HalfLine.stateScales_response` uses this definition to establish the
precise assertion is `(stateScales G).response s z= (1-z)/(1+(s/groundParameter hm hn)*z)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def stateScales : chebyshev2.StateRegion.Scales :=
  ⟨groundParameter hm hn,32,32,G.coupling_positive,by norm_num,by norm_num⟩

/--
The precise assertion is `(stateScales G).response s z= (1-z)/(1+(s/groundParameter hm hn)*z)`.

Use: `chebyshev2.HalfLine.state_mem` rewrites with this identity to establish membership in
the specified domain/enclosure: `Filters.state G x ∈ (stateScales G).states`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem stateScales_response (s z : ℝ) : (stateScales G).response s z=
    (1-z)/(1+(s/groundParameter hm hn)*z) := by
  have he : 1+(s/groundParameter hm hn)*z=(groundParameter hm hn+s*z)/groundParameter hm hn := by
    field_simp [G.coupling_positive.ne']
  rw [he,div_div_eq_mul_div]
  dsimp only [chebyshev2.StateRegion.Scales.response,stateScales]
  ring

/--
Proposition 7 for the literal ODE state and the actual density parameter.

Membership in the specified domain/enclosure: `Filters.state G x ∈ (stateScales G).states`.

Use: `chebyshev2.Calibration.Data.flowResidual_nonneg_of_statewise` uses this assertion to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, 0 ≤
C.flowResidual G ξ₀ ξ₁ χ τ η Ψ x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `G.q x=0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem state_mem (x : ℝ) : Filters.state G x ∈ (stateScales G).states := by
  -- Separate `G.q x=0` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hq : G.q x=0
  · have hz := zero_filters G hq
    have he : Filters.state G x=(0,0,0,0) := by
      simp [Filters.state,Filters.defect,hq,hz.1,hz.2 32 (by norm_num),hz.2 64 (by norm_num)]
    rw [he]
    exact (stateScales G).zero_state_mem
  · have hp : 0 < G.q x := lt_of_le_of_ne (G.coordinate_mem x).1 (Ne.symm hq)
    let :=  commonMeasure_ode_probability G hp
    apply (stateScales G).states_iff.mpr
    right
    let U := ∫ z, (stateScales G).response 32 z ∂commonMeasure G x
    let V := ∫ z, (stateScales G).response 64 z ∂commonMeasure G x
    let theta := ∫ z, z ∂commonMeasure G x
    refine ⟨G.q x,⟨hp,(G.coordinate_mem x).2⟩,U,V,theta,?_,?_⟩
    · refine ⟨⟨commonMeasure G x,inferInstance,
        (commonMeasure_supported G x).mono (fun _ hz => ⟨hz.1,hz.2.le⟩),rfl,?_,rfl⟩⟩
      change (∫ z, (stateScales G).response ((32:ℝ)+32) z ∂commonMeasure G x)=V
      norm_num
      rfl
    · have hu : U=groundParameter hm hn*Filters.nonlinear 32 m x/(32*G.q x) := by
        dsimp only [U]
        simp_rw [stateScales_response]
        exact (commonMeasure_filter G hp (by norm_num : (0:ℝ) < 32)).symm
      have hv : V=groundParameter hm hn*Filters.nonlinear 64 m x/(64*G.q x) := by
        dsimp only [V]
        simp_rw [stateScales_response]
        exact (commonMeasure_filter G hp (by norm_num : (0:ℝ) < 64)).symm
      have hh : theta=Filters.defect G x/G.q x := (commonMeasure_defect G hp).symm
      rw [hu,hv,hh]
      change (G.q x,Filters.nonlinear 32 m x/32,Filters.nonlinear 64 m x/64,Filters.defect G x)=_
      simp only [stateScales,Prod.mk.injEq]
      refine ⟨trivial,?_,?_,?_⟩ <;> field_simp [G.coupling_positive.ne',hq]

end
end chebyshev2.HalfLine
