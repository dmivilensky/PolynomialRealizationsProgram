import «2610.05164v2».HalfLine.Operator
import «2610.05164v2».GroundState.Article

/-!
Article: 2610.05164v2, Theorem 3.3.
The strict half-line spectral gap used in C.1.
Use: `«2610.05164v2».HalfLine.operator_norm_strict` feeds
`«2610.05164v2».HalfLine.ground_pencil_unit` (ground pencil unit).
Proof chain: `«2610.05164v2».HalfLine.commonMeasure_ode_probability` — 2610.05164v2, Theorem 3.3; A
common compact probability measure for all scales.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Continuum «2610.05164v2».Sobolev «2610.05164v2».GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `inner ℝ (feature x) (boundaryProjection x u)=0`.

Use: `«2610.05164v2».HalfLine.boundaryProjection_idempotent` rewrites with this identity to
establish exact identity `boundaryProjection x (boundaryProjection x u)=boundaryProjection x
u`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_norm` with the arguments
shown in the proof.
-/
theorem boundaryProjection_orthogonal (x : ℝ) (u : FeatureSpace) :
    inner ℝ (feature x) (boundaryProjection x u)=0 := by
  change inner ℝ (feature x) (u-inner ℝ (feature x) u • feature x)=0
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,feature_norm]
  ring

/--
Exact identity `boundaryProjection x (boundaryProjection x u)=boundaryProjection x u`.

Use: `«2610.05164v2».HalfLine.boundaryProjection_norm` rewrites with this identity to establish
exact identity `‖boundaryProjection x u‖^2=inner ℝ u (boundaryProjection x u)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.boundaryProjection_orthogonal`
with the arguments shown in the proof.
-/
theorem boundaryProjection_idempotent (x : ℝ) (u : FeatureSpace) :
    boundaryProjection x (boundaryProjection x u)=boundaryProjection x u := by
  change boundaryProjection x u-featureProjection x (boundaryProjection x u)=boundaryProjection x u
  simp [featureProjection,InnerProductSpace.rankOne_apply,boundaryProjection_orthogonal]

/--
Exact identity `‖boundaryProjection x u‖^2=inner ℝ u (boundaryProjection x u)`.

Use: `«2610.05164v2».HalfLine.eigenvalue_strict` uses this identity to establish the stated
quantitative bound `lambda < 1/groundParameter hm hn`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.boundaryProjection_positive`,
`«2610.05164v2».HalfLine.boundaryProjection_idempotent` with the arguments shown in the proof.
-/
theorem boundaryProjection_norm (x : ℝ) (u : FeatureSpace) :
    ‖boundaryProjection x u‖^2=inner ℝ u (boundaryProjection x u) := by
  rw [← real_inner_self_eq_norm_sq]
  have h := (boundaryProjection_positive x).isSymmetric u (boundaryProjection x u)
  change inner ℝ (boundaryProjection x u) (boundaryProjection x u)=
    inner ℝ u (boundaryProjection x (boundaryProjection x u)) at h
  rw [boundaryProjection_idempotent] at h
  exact h

/--
Exact identity `H1.rep (boundaryProjection x u) x=0`.

Use: `«2610.05164v2».HalfLine.eigenvalue_strict` uses this identity to establish the stated
quantitative bound `lambda < 1/groundParameter hm hn`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.boundaryProjection_orthogonal`
with the arguments shown in the proof.
-/
theorem boundaryProjection_rep (x : ℝ) (u : FeatureSpace) :
    H1.rep (boundaryProjection x u) x=0 := by
  change (sqrt 2)⁻¹*inner ℝ (feature x) (boundaryProjection x u)=0
  rw [boundaryProjection_orthogonal,mul_zero]

/--
A nonzero Dirichlet test function cannot attain the full-line ground Rayleigh bound: equality
would make it a multiple of a strictly positive ground.

The stated quantitative bound `groundParameter hm hn*(∫ t, m t*(H1.rep u t)^2) < ‖u‖^2`.

Use: `«2610.05164v2».HalfLine.eigenvalue_strict` uses this bound to establish the stated
quantitative bound `lambda < 1/groundParameter hm hn`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.groundParameter_bound`,
`«2610.05164v2».GroundState.GroundWitness.square_identity`,
`«2610.05164v2».GroundState.GroundWitness.square_eq_zero_iff` with the arguments shown in the
proof.
-/
theorem ground_strict_dirichlet {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ) (u : H1) (hu : u ≠ 0) (hb : H1.rep u x=0) :
    groundParameter hm hn*(∫ t, m t*(H1.rep u t)^2) < ‖u‖^2 := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.groundParameter_bound`,
  -- `«2610.05164v2».GroundState.GroundWitness.square_identity`,
  -- `«2610.05164v2».GroundState.GroundWitness.square_eq_zero_iff` with the arguments shown in
  -- the proof.
  have hle := groundParameter_bound hm hn G.mass_positive u
  apply lt_of_le_of_ne hle
  intro he
  have hz : (∫ t, (H1.slope u t-(G.d t/H1.rep G.u t)*H1.rep u t)^2)=0 := by
    rw [← G.square_identity]
    linarith
  obtain ⟨r,hr⟩ := (G.square_eq_zero_iff u).mp hz
  have hb' : r*H1.rep G.u x=0 := by simpa only [hr,H1.rep_smul] using hb
  have hr0 : r=0 := (mul_eq_zero.mp hb').resolve_right (G.positive x).ne'
  exact hu (by rw [hr,hr0,zero_smul])

/--
Exact identity `evaluation hm hn x (boundaryProjection x ((evaluation hm hn x).adjoint
f))=(2:ℝ) • operator hm hn x f`.

Use: `«2610.05164v2».HalfLine.eigenvalue_strict` rewrites with this identity to establish the
stated quantitative bound `lambda < 1/groundParameter hm hn`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem operator_apply {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) (f : FeatureSpace) :
    evaluation hm hn x (boundaryProjection x ((evaluation hm hn x).adjoint f))=(2:ℝ) • operator hm hn x f := by
  simp only [operator,smul_apply,ContinuousLinearMap.comp_apply,smul_smul]
  norm_num

/--
The stated quantitative bound `lambda < 1/groundParameter hm hn`.

Use: `«2610.05164v2».HalfLine.operator_norm_strict` uses this bound to establish the stated
quantitative bound `‖operator hm hn x‖ < 1/groundParameter hm hn`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem eigenvalue_strict {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ) {f : FeatureSpace} {lambda : ℝ}
    (hf : f ≠ 0) (hl : 0 < lambda) (he : operator hm hn x f=lambda • f) :
    lambda < 1/groundParameter hm hn := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let g := boundaryProjection x ((evaluation hm hn x).adjoint f)
  have hgA : evaluation hm hn x g=(2*lambda) • f := by
    rw [operator_apply,he,smul_smul]
  have hgn : ‖g‖^2=2*lambda*‖f‖^2 := by
    calc
      _ = inner ℝ ((evaluation hm hn x).adjoint f) g := boundaryProjection_norm _ _
      _ = inner ℝ f (evaluation hm hn x g) := by rw [ContinuousLinearMap.adjoint_inner_left]
      _ = _ := by rw [hgA,real_inner_smul_right,real_inner_self_eq_norm_sq]
  have hg : g ≠ 0 := by
    intro hz
    rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hgn
    have hp : 0 < 2*lambda*‖f‖^2 := by
      have hf' := norm_pos_iff.mpr hf
      positivity
    linarith
  have hweighted : (∫ t, leftDensity m x t*(H1.rep g t)^2)=2*lambda^2*‖f‖^2 := by
    have h := evaluationOperator_inner (leftDensity_integrable hm x) (leftDensity_nonneg hn x) g g
    change inner ℝ (evaluation hm hn x g) (evaluation hm hn x g)=inner ℝ g (densityOperator (leftDensity m x) g) at h
    rw [hgA,real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
      sobolevDensityOperator_quadratic (leftDensity_integrable hm x)] at h
    nlinarith
  have hmono : (∫ t, leftDensity m x t*(H1.rep g t)^2) ≤ ∫ t, m t*(H1.rep g t)^2 := by
    apply integral_mono (weighted_square_integrable (leftDensity_integrable hm x) g)
      (weighted_square_integrable hm g)
    intro t
    by_cases ht : t < x
    · simp [leftDensity,ht]
    · simp [leftDensity,ht,mul_nonneg (hn t) (sq_nonneg _)]
  have hs := ground_strict_dirichlet G x g hg (boundaryProjection_rep _ _)
  have hc := G.coupling_positive
  have hmul := mul_le_mul_of_nonneg_left hmono hc.le
  have hlt := hmul.trans_lt hs
  rw [hweighted,hgn] at hlt
  apply (lt_div_iff₀ hc).mpr
  have hf' : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  have hfactor : 0 < 2*lambda*‖f‖^2 := by positivity
  apply (mul_lt_mul_iff_right₀ hfactor).mp
  nlinarith only [hlt]

/--
The stated quantitative bound `‖T‖ ≤ D.eigenvalue 0`.

Use: `«2610.05164v2».HalfLine.operator_norm_strict` uses this bound to establish the stated
quantitative bound `‖operator hm hn x‖ < 1/groundParameter hm hn`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Separate `u=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
private theorem norm_le_top {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : E →L[ℝ] E} (D : PositiveSpectralData T) (hp : T.IsPositive) :
    ‖T‖ ≤ D.eigenvalue 0 := by
  -- Separate `u=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hp.isSymmetric]
  apply ciSup_le
  intro u
  by_cases hu : u=0
  · simp only [hu,ContinuousLinearMap.rayleighQuotient,norm_zero,
      zero_pow (by decide : 2 ≠ 0),div_zero,abs_zero]
    exact D.eigenvalue_nonneg 0
  · have hpos := hp.re_inner_nonneg_left u
    change 0 ≤ inner ℝ (T u) u at hpos
    simp only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real,abs_div,abs_of_nonneg hpos,abs_of_nonneg (sq_nonneg ‖u‖)]
    apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hu))).mpr
    rw [real_inner_comm]
    exact D.top_quadratic_bound u

/--
The strict half-line spectral gap used in C.1. Compactness promotes the strict bound on each
positive eigenvalue to a strict operator-norm bound.

The stated quantitative bound `‖operator hm hn x‖ < 1/groundParameter hm hn`.

Use: `«2610.05164v2».HalfLine.ground_pencil_unit` uses this bound to establish the precise
assertion is `IsUnit (ContinuousLinearMap.id ℝ FeatureSpace-groundParameter hm hn • operator hm
hn x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Separate `0 < D.eigenvalue 0` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem operator_norm_strict {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ) : ‖operator hm hn x‖ < 1/groundParameter hm hn := by
  -- Separate `0 < D.eigenvalue 0` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  let D := spectralData hm hn x
  have htop := norm_le_top D (operator_positive hm hn x)
  by_cases ht : 0 < D.eigenvalue 0
  · have htrace : 0 < ∑' i, D.eig i := ht.trans_le (D.eigenvalue_le_trace 0)
    obtain ⟨_,f,hfn,hfe⟩ := D.top_attained htrace
    have hf : f ≠ 0 := by intro hf; simp [hf] at hfn
    exact htop.trans_lt (eigenvalue_strict G x hf ht hfe)
  · exact (htop.trans (le_of_not_gt ht)).trans_lt (one_div_pos.mpr G.coupling_positive)

end
end «2610.05164v2».HalfLine
