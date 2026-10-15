import «2610.05164v2».Continuum.GramCompact
import «2610.05164v2».Continuum.PositiveSpectrum
import «2610.05164v2».Continuum.NuclearAlgebra

/-!
Article: 2610.05164v2, Theorem 3.3.
The Dirichlet half-line Birman--Schwinger operator, embedded in L2(R) by zero extension.
Use: `«2610.05164v2».HalfLine.green` feeds `«2610.05164v2».HalfLine.greenSolution_integral` (The
solution is the literal integral against the Dirichlet Green kernel).
Proof chain: `«2610.05164v2».HalfLine.commonMeasure_ode_probability` — 2610.05164v2, Theorem 3.3; A
common compact probability measure for all scales.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Defines `leftDensity` of type `ℝ → ℝ` by `(Iio x).indicator m`.

Use: `«2610.05164v2».HalfLine.leftDensity_nonneg` rewrites with this definition to establish
the stated quantitative bound `0 ≤ leftDensity m x t`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.
-/
def leftDensity (m : ℝ → ℝ) (x : ℝ) : ℝ → ℝ := (Iio x).indicator m

/--
Integrability of the displayed function: `Integrable (leftDensity m x)`.

Use: `«2610.05164v2».HalfLine.evaluation` uses this integrability result in the displayed
construction of `evaluation`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem leftDensity_integrable {m : ℝ → ℝ} (hm : Integrable m) (x : ℝ) :
    Integrable (leftDensity m x) := hm.indicator measurableSet_Iio

/--
The stated quantitative bound `0 ≤ leftDensity m x t`.

Use: `«2610.05164v2».HalfLine.evaluation` uses this bound in the displayed construction of
`evaluation`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_linear_filter`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem leftDensity_nonneg {m : ℝ → ℝ} (hn : ∀ t, 0 ≤ m t) (x t : ℝ) :
    0 ≤ leftDensity m x t := by by_cases h : t < x <;> simp [leftDensity,h,hn]

/--
Defines `boundaryProjection` of type `FeatureSpace →L[ℝ] FeatureSpace` by
`ContinuousLinearMap.id ℝ FeatureSpace-featureProjection x`.

Use: `«2610.05164v2».HalfLine.operator` uses this definition in the displayed construction of
`operator`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.
-/
def boundaryProjection (x : ℝ) : FeatureSpace →L[ℝ] FeatureSpace :=
  ContinuousLinearMap.id ℝ FeatureSpace-featureProjection x

/--
The precise assertion is `(boundaryProjection x).IsPositive`.

Use: `«2610.05164v2».HalfLine.operator_positive` uses this assertion to establish the precise
assertion is `(operator hm hn x).IsPositive`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.featureProjection_inner`,
`«2610.05164v2».Continuum.featureProjection_quadratic`, `«2610.05164v2».Continuum.feature_norm`
with the arguments shown in the proof.
-/
theorem boundaryProjection_positive (x : ℝ) : (boundaryProjection x).IsPositive := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.featureProjection_inner`,
  -- `«2610.05164v2».Continuum.featureProjection_quadratic`,
  -- `«2610.05164v2».Continuum.feature_norm` with the arguments shown in the proof.
  constructor
  · intro u v
    change inner ℝ (u-featureProjection x u) v=inner ℝ u (v-featureProjection x v)
    rw [inner_sub_left,inner_sub_right]
    congr 1
    rw [real_inner_comm,featureProjection_inner,featureProjection_inner]
    ring
  · intro u
    change 0 ≤ inner ℝ (u-featureProjection x u) u
    rw [real_inner_comm,inner_sub_right,real_inner_self_eq_norm_sq,featureProjection_quadratic]
    have h := norm_inner_le_norm (𝕜 := ℝ) (feature x) u
    rw [feature_norm,one_mul,Real.norm_eq_abs] at h
    have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h
    rw [sq_abs] at hs
    linarith

/--
Defines `evaluation` of type `FeatureSpace →L[ℝ] FeatureSpace` by `evaluationOperator
(leftDensity_integrable hm x) (leftDensity_nonneg hn x)`.

Use: `«2610.05164v2».HalfLine.operator` uses this definition in the displayed construction of
`operator`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_linear_filter`.
-/
def evaluation {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    FeatureSpace →L[ℝ] FeatureSpace :=
  evaluationOperator (leftDensity_integrable hm x) (leftDensity_nonneg hn x)

/--
Defines `vector` of type `FeatureSpace` by `evaluation hm hn x (feature x)`.

Use: `«2610.05164v2».HalfLine.operator_compact` uses this definition to establish compactness
of the displayed operator: `IsCompactOperator (operator hm hn x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_linear_filter`.
-/
def vector {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) : FeatureSpace :=
  evaluation hm hn x (feature x)

/--
Defines `operator` of type `FeatureSpace →L[ℝ] FeatureSpace` by `(1/2:ℝ) • (evaluation hm hn x
∘L boundaryProjection x ∘L (evaluation hm hn x).adjoint)`.

Use: `«2610.05164v2».HalfLine.operator_rankOne` uses this definition to establish exact
identity `operator hm hn x = (1/2:ℝ) • (kernelOperator (leftDensity_integrable hm x)
(leftDensity_nonneg hn x)- InnerProductSpace.rankOne ℝ (vector hm hn x) (vector hm hn x))`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.
-/
def operator {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    FeatureSpace →L[ℝ] FeatureSpace :=
  (1/2:ℝ) • (evaluation hm hn x ∘L boundaryProjection x ∘L (evaluation hm hn x).adjoint)

/--
The precise assertion is `(operator hm hn x).IsPositive`.

Use: `«2610.05164v2».HalfLine.spectralData` uses this assertion in the displayed construction
of `spectralData`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.boundaryProjection_positive` with
the arguments shown in the proof.
-/
theorem operator_positive {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    (operator hm hn x).IsPositive :=
  ((boundaryProjection_positive x).conj_adjoint (evaluation hm hn x)).smul_of_nonneg (by norm_num)

/--
Exact identity `operator hm hn x = (1/2:ℝ) • (kernelOperator (leftDensity_integrable hm x)
(leftDensity_nonneg hn x)- InnerProductSpace.rankOne ℝ (vector hm hn x) (vector hm hn x))`.

Use: `«2610.05164v2».HalfLine.operator_compact` rewrites with this identity to establish
compactness of the displayed operator: `IsCompactOperator (operator hm hn x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem operator_rankOne {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    operator hm hn x = (1/2:ℝ) •
      (kernelOperator (leftDensity_integrable hm x) (leftDensity_nonneg hn x)-
        InnerProductSpace.rankOne ℝ (vector hm hn x) (vector hm hn x)) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  unfold operator boundaryProjection
  rw [ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.id_comp]
  simp only [featureProjection,InnerProductSpace.comp_rankOne,InnerProductSpace.rankOne_comp,
    ContinuousLinearMap.adjoint_adjoint]
  rfl

/--
Compactness of the displayed operator: `IsCompactOperator (operator hm hn x)`.

Use: `«2610.05164v2».HalfLine.spectralData` uses this assertion in the displayed construction
of `spectralData`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.leftDensity_integrable`,
`«2610.05164v2».HalfLine.leftDensity_nonneg`, `«2610.05164v2».HalfLine.operator_rankOne` with
the arguments shown in the proof.
-/
theorem operator_compact {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    IsCompactOperator (operator hm hn x) := by
  rw [operator_rankOne]
  exact ((kernelOperator_isCompact (leftDensity_integrable hm x) (leftDensity_nonneg hn x)).sub
    (rankOne_isCompact _ _)).smul (1/2:ℝ)

/--
The trace-class property: `IsTraceClass (operator hm hn x)`.

Use: `«2610.05164v2».HalfLine.spectralData` uses this assertion in the displayed construction
of `spectralData`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.leftDensity_integrable`,
`«2610.05164v2».HalfLine.leftDensity_nonneg`, `«2610.05164v2».HalfLine.operator_rankOne` with
the arguments shown in the proof.
-/
theorem operator_traceClass {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    IsTraceClass (operator hm hn x) := by
  rw [operator_rankOne]
  exact ((kernelOperator_isTraceClass (leftDensity_integrable hm x) (leftDensity_nonneg hn x)).sub
    (rankOne_isTraceClass _ _)).smul (1/2:ℝ)

/--
Defines `spectralData` of type `PositiveSpectralData (operator hm hn x)` by
`positiveSpectralData _ (operator_compact hm hn x) (operator_positive hm hn x)
(operator_traceClass hm hn x)`.

Use: `«2610.05164v2».HalfLine.basis_vector_square_hasSum` uses this definition to establish the
value of a convergent infinite sum: `HasSum (fun i : (spectralData hm hn x).Index => (inner ℝ
((spectralData hm hn x).basis i) (vector hm hn x))^2) (‖vector hm hn x‖^2)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.
-/
def spectralData {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    PositiveSpectralData (operator hm hn x) :=
  positiveSpectralData _ (operator_compact hm hn x) (operator_positive hm hn x)
    (operator_traceClass hm hn x)

/--
The actual vector from C.1, with zero extension outside the half-line.

The stated quantitative bound `vector hm hn x =ᵐ[volume] (Iio x).indicator (fun t => sqrt (m
t)*exp (t-x))`.

Use: `«2610.05164v2».HalfLine.vector_coe_density` uses this identity to establish the stated
quantitative bound `vector hm hn x =ᵐ[volume] (fun t => sqrt (leftDensity m x t)*exp (t-x))`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_linear_filter`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem vector_coe {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    vector hm hn x =ᵐ[volume] (Iio x).indicator (fun t => sqrt (m t)*exp (t-x)) := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  filter_upwards [evaluationOperator_coe (leftDensity_integrable hm x)
    (leftDensity_nonneg hn x) (feature x)] with t ht
  change evaluationOperator (leftDensity_integrable hm x) (leftDensity_nonneg hn x) (feature x) t=_
  rw [ht,rawEvaluation,feature_inner]
  by_cases hx : t < x
  · rw [leftDensity,indicator_of_mem (show t ∈ Iio x from hx),indicator_of_mem (show t ∈ Iio x from hx),
      abs_of_nonpos (sub_nonpos.mpr hx.le)]
    congr 2
    ring
  · simp [leftDensity,hx]

/--
Defines `green` of type `ℝ` by `(exp (-|t-y|)-exp (t+y-2*x))/2`.

Use: `«2610.05164v2».HalfLine.dirichletFeature_gram` uses this definition to establish exact
identity `inner ℝ (dirichletFeature x t) (dirichletFeature x y)=2*green x t y`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.
-/
def green (x t y : ℝ) : ℝ := (exp (-|t-y|)-exp (t+y-2*x))/2
/--
Defines `dirichletFeature` of type `FeatureSpace` by `feature t-exp (t-x) • feature x`.

Use: `«2610.05164v2».HalfLine.dirichletFeature_gram` rewrites with this definition to establish
exact identity `inner ℝ (dirichletFeature x t) (dirichletFeature x y)=2*green x t y`.

Article: 2610.05164v2, Theorem 3.3.
-/
def dirichletFeature (x t : ℝ) : FeatureSpace := feature t-exp (t-x) • feature x

/--
Exact identity `inner ℝ (dirichletFeature x t) (dirichletFeature x y)=2*green x t y`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.3.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_inner` with the arguments
shown in the proof.
-/
theorem dirichletFeature_gram {x t y : ℝ} (ht : t ≤ x) (hy : y ≤ x) :
    inner ℝ (dirichletFeature x t) (dirichletFeature x y)=2*green x t y := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.feature_inner` with the arguments
  -- shown in the proof.
  simp only [dirichletFeature,inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,feature_inner,sub_self,abs_zero,neg_zero,exp_zero]
  rw [abs_of_nonpos (sub_nonpos.mpr ht),abs_of_nonneg (sub_nonneg.mpr hy)]
  have hty : exp (t-x)*exp (y-x)=exp (t+y-2*x) := by rw [← exp_add]; congr 1; ring
  have ht' : exp (-(-(t-x)))=exp (t-x) := by rw [neg_neg]
  rw [ht',show -(x-y)=y-x by ring]
  dsimp [green]
  nlinarith [hty]

/--
The stated quantitative bound `0 ≤ green x t y`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.3.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem green_nonneg {x t y : ℝ} (ht : t ≤ x) (hy : y ≤ x) : 0 ≤ green x t y := by
  have hab : t+y-2*x ≤ -|t-y| := by
    have h : |t-y| ≤ -(t+y-2*x) := abs_le.mpr ⟨by linarith,by linarith⟩
    linarith
  exact div_nonneg (sub_nonneg.mpr (exp_le_exp.mpr hab)) (by norm_num)

/--
The stated quantitative bound `green x t y ≤ exp (-|t-y|)/2`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.3.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem green_upper (x t y : ℝ) : green x t y ≤ exp (-|t-y|)/2 := by
  dsimp [green]
  linarith [exp_pos (t+y-2*x)]

end
end «2610.05164v2».HalfLine
