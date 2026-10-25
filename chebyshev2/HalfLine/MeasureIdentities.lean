import chebyshev2.HalfLine.CommonMeasure
import chebyshev2.StateRegion.OriginalAttainment

/-!
Article: chebyshev2, Theorem 3.3.
Measure Identities.
Use: `chebyshev2.HalfLine.zero_quadratics` feeds `chebyshev2.HalfLine.zero_filters` (The
zero-coordinate case of Theorem 3.3).
Proof chain: `chebyshev2.HalfLine.zero_filters` — chebyshev2, Theorem 3.3; A common compact
probability measure for all scales.
-/
namespace chebyshev2.HalfLine
noncomputable section
open Set MeasureTheory Real chebyshev2.Continuum chebyshev2.GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ)

/--
The value of a convergent infinite sum: `HasSum (fun i : (spectralData hm hn x).Index => (inner
ℝ ((spectralData hm hn x).basis i) (vector hm hn x))^2) (‖vector hm hn x‖^2)`.

Use: `chebyshev2.HalfLine.groundQuadratic_lower` uses this infinite-sum formula to
establish the stated quantitative bound `groundParameter hm hn*‖vector hm hn x‖^2 ≤
groundQuadratic G x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_linear_filter`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem basis_vector_square_hasSum :
    HasSum (fun i : (spectralData hm hn x).Index =>
      (inner ℝ ((spectralData hm hn x).basis i) (vector hm hn x))^2) (‖vector hm hn x‖^2) := by
  simpa only [real_inner_comm (vector hm hn x) _,← pow_two,real_inner_self_eq_norm_sq] using
    (spectralData hm hn x).basis.hasSum_inner_mul_inner (vector hm hn x) (vector hm hn x)

/--
The stated quantitative bound `groundParameter hm hn*‖vector hm hn x‖^2 ≤ groundQuadratic G x`.

Use: `chebyshev2.HalfLine.groundQuadratic_eq_zero_iff` uses this bound to establish
equivalence of the displayed criteria: `groundQuadratic G x=0 ↔ vector hm hn x=0`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.zero_filters`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.basis_vector_square_hasSum`,
`chebyshev2.HalfLine.groundQuadratic_hasSum`, `chebyshev2.HalfLine.spectral_den_pos`
with the arguments shown in the proof.
-/
theorem groundQuadratic_lower :
    groundParameter hm hn*‖vector hm hn x‖^2 ≤ groundQuadratic G x := by
  -- Use the identities/estimates `chebyshev2.HalfLine.basis_vector_square_hasSum`,
  -- `chebyshev2.HalfLine.groundQuadratic_hasSum`,
  -- `chebyshev2.HalfLine.spectral_den_pos` with the arguments shown in the proof.
  have h₁ := (basis_vector_square_hasSum (hm := hm) (hn := hn) x).mul_left (groundParameter hm hn)
  have h₂ := groundQuadratic_hasSum G x
  rw [← h₁.tsum_eq,← h₂.tsum_eq]
  apply h₁.summable.tsum_le_tsum _ h₂.summable
  intro i
  apply (le_div_iff₀ (spectral_den_pos G x i)).mpr
  have hk := G.coupling_positive.le
  have he := (spectralData hm hn x).nonneg i
  have hc : 0 ≤ groundParameter hm hn*
      (inner ℝ ((spectralData hm hn x).basis i) (vector hm hn x))^2 := mul_nonneg hk (sq_nonneg _)
  nlinarith [mul_nonneg hc (mul_nonneg hk he)]

/--
The stated quantitative bound `0 ≤ groundQuadratic G x`.

Use: `chebyshev2.HalfLine.groundQuadratic_pos_iff` uses this bound to establish equivalence
of the displayed criteria: `0 < groundQuadratic G x ↔ vector hm hn x ≠ 0`.

Article: chebyshev2, Theorem 3.3.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coupling_positive`,
`chebyshev2.HalfLine.groundQuadratic_lower` with the arguments shown in the proof.
-/
theorem groundQuadratic_nonneg : 0 ≤ groundQuadratic G x :=
  (mul_nonneg G.coupling_positive.le (sq_nonneg _)).trans (groundQuadratic_lower G x)

/--
Equivalence of the displayed criteria: `groundQuadratic G x=0 ↔ vector hm hn x=0`.

Use: `chebyshev2.HalfLine.groundQuadratic_pos_iff` uses this identity to establish
equivalence of the displayed criteria: `0 < groundQuadratic G x ↔ vector hm hn x ≠ 0`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.zero_filters`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.groundQuadratic_lower`,
`chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem groundQuadratic_eq_zero_iff : groundQuadratic G x=0 ↔ vector hm hn x=0 := by
  -- Use the identities/estimates `chebyshev2.HalfLine.groundQuadratic_lower`,
  -- `chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in
  -- the proof.
  constructor
  · intro hz
    have h := groundQuadratic_lower G x
    rw [hz] at h
    have hsq : ‖vector hm hn x‖^2=0 := le_antisymm
      (nonpos_of_mul_nonpos_right h G.coupling_positive) (sq_nonneg _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro hz
    simp [groundQuadratic,hz]

/--
Equivalence of the displayed criteria: `0 < groundQuadratic G x ↔ vector hm hn x ≠ 0`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.3.

Proof: Use the identities/estimates `chebyshev2.HalfLine.groundQuadratic_eq_zero_iff`,
`chebyshev2.HalfLine.groundQuadratic_nonneg` with the arguments shown in the proof.
-/
theorem groundQuadratic_pos_iff : 0 < groundQuadratic G x ↔ vector hm hn x ≠ 0 := by
  constructor
  · intro h hz
    have h0 := (groundQuadratic_eq_zero_iff G x).mpr hz
    linarith
  · intro hv
    exact lt_of_le_of_ne (groundQuadratic_nonneg G x)
      (fun hz => hv ((groundQuadratic_eq_zero_iff G x).mp hz.symm))

/--
Exact identity `responseQuadratic (hm := hm) (hn := hn) x 0 le_rfl=‖vector hm hn x‖^2`.

Use: `chebyshev2.HalfLine.commonMeasure_linear` uses this identity to establish exact
identity `(∫ z, 1-z ∂commonMeasure G x)=groundParameter hm hn/groundQuadratic G x*‖vector hm hn
x‖^2`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_linear_filter`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.responseQuadratic_hasSum`,
`chebyshev2.HalfLine.basis_vector_square_hasSum` with the arguments shown in the proof.
-/
theorem responseQuadratic_zero : responseQuadratic (hm := hm) (hn := hn) x 0 le_rfl=‖vector hm hn x‖^2 := by
  have h := responseQuadratic_hasSum (hm := hm) (hn := hn) x 0 le_rfl
  simp only [zero_mul,add_zero,div_one] at h
  exact h.unique (basis_vector_square_hasSum (hm := hm) (hn := hn) x)

/--
Exact identity `(∫ z, 1-z ∂commonMeasure G x)=groundParameter hm hn/groundQuadratic G x*‖vector
hm hn x‖^2`.

Use: `chebyshev2.HalfLine.commonMeasure_mean` uses this identity to establish exact
identity `(∫ z, z ∂commonMeasure G x)=1-Filters.linear hm hn x/groundQuadratic G x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_linear_filter`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.commonMeasure_response`,
`chebyshev2.HalfLine.responseQuadratic_zero` with the arguments shown in the proof.
-/
theorem commonMeasure_linear (hq : 0 < groundQuadratic G x) :
    (∫ z, 1-z ∂commonMeasure G x)=groundParameter hm hn/groundQuadratic G x*‖vector hm hn x‖^2 := by
  have h := commonMeasure_response G x hq 0 le_rfl
  simpa only [zero_div,zero_mul,add_zero,div_one,responseQuadratic_zero] using h

/--
Exact identity `(∫ z, z ∂commonMeasure G x)=1-Filters.linear hm hn x/groundQuadratic G x`.

Use: `chebyshev2.HalfLine.commonMeasure_defect` rewrites with this identity to establish
exact identity `Filters.defect G x/G.q x=∫ z, z ∂commonMeasure G x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_defect`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.commonMeasure_probability`,
`chebyshev2.HalfLine.commonMeasure_supported`,
`chebyshev2.HalfLine.commonMeasure_linear` with the arguments shown in the proof.
-/
theorem commonMeasure_mean (hq : 0 < groundQuadratic G x) :
    (∫ z, z ∂commonMeasure G x)=1-Filters.linear hm hn x/groundQuadratic G x := by
  -- Use the identities/estimates `chebyshev2.HalfLine.commonMeasure_probability`,
  -- `chebyshev2.HalfLine.commonMeasure_supported`,
  -- `chebyshev2.HalfLine.commonMeasure_linear` with the arguments shown in the proof.
  let _ := commonMeasure_probability G x hq
  have hμ : ∀ᵐ z ∂commonMeasure G x, z ∈ Icc (0:ℝ) 1 :=
    (commonMeasure_supported G x).mono (fun _ hz => ⟨hz.1,hz.2.le⟩)
  have h := commonMeasure_linear G x hq
  rw [integral_sub (integrable_const _) (chebyshev2.StateRegion.Scales.coord_integrable hμ)] at h
  simp only [integral_const,smul_eq_mul] at h
  simp at h
  rw [linear_eq_vector_norm]
  linarith [show groundParameter hm hn/groundQuadratic G x*‖vector hm hn x‖^2=
    groundParameter hm hn*‖vector hm hn x‖^2/groundQuadratic G x by ring]

/--
Exact identity `Filters.linear hm hn x=0 ∧ ∀ s hs, responseQuadratic (hm := hm) (hn := hn) x s
hs=0`.

Use: `chebyshev2.HalfLine.zero_filters` uses this identity to establish the identity
`Filters.linear hm hn x=0 ∧ ∀ s, 0 ≤ s → Filters.nonlinear s m x=0`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.zero_filters`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.groundQuadratic_eq_zero_iff`,
`chebyshev2.HalfLine.linear_eq_vector_norm` with the arguments shown in the proof.
-/
theorem zero_quadratics (hq : groundQuadratic G x=0) :
    Filters.linear hm hn x=0 ∧ ∀ s hs, responseQuadratic (hm := hm) (hn := hn) x s hs=0 := by
  have hv := (groundQuadratic_eq_zero_iff G x).mp hq
  constructor
  · simp [linear_eq_vector_norm, hv]
  · intro s hs
    simp [responseQuadratic,hv]

end
end chebyshev2.HalfLine
