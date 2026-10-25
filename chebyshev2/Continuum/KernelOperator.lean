import chebyshev2.Continuum.CompactOperator

/-!
Article: chebyshev2, Proposition 2.
The factorization gives exactly the integral kernel printed in Section 2.2.
Use: `chebyshev2.Continuum.kernelOperator_coe` feeds
`chebyshev2.SineContinuum.sineKernel_conjugacy_apply` (Literal Proposition 2 conjugacy, on all
L² vectors).
Proof chain: `chebyshev2.GroundState.ground_state` — chebyshev2, Theorem 3.1; Sharp
ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace chebyshev2.Continuum
noncomputable section
open MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `MemLp (fun x => sqrt (m x)) 2 volume`.

Use: `chebyshev2.Continuum.evaluationLinear_bound` uses this identity to establish the
stated quantitative bound `‖evaluationLinear hm hn u‖ ≤ ‖sqrtDensity hm hn‖ * ‖u‖`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem sqrtDensity_memLp {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    MemLp (fun x => sqrt (m x)) 2 volume := by
  apply (memLp_two_iff_integrable_sq ?_).mpr
  · simpa only [sq_sqrt (hn _)] using hm
  · exact continuous_sqrt.comp_aestronglyMeasurable hm.aestronglyMeasurable

/--
Defines `sqrtDensity` of type `FeatureSpace` by `(sqrtDensity_memLp hm hn).toLp (fun x => sqrt
(m x))`.

Use: `chebyshev2.Continuum.evaluationOperator` uses this definition in the displayed
construction of `evaluationOperator`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def sqrtDensity {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) : FeatureSpace :=
  (sqrtDensity_memLp hm hn).toLp (fun x => sqrt (m x))

/--
Defines `rawEvaluation` of type `ℝ` by `sqrt (m x) * inner ℝ (feature x) u`.

Use: `chebyshev2.Continuum.evaluationLinear` uses this definition in the displayed
construction of `evaluationLinear`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def rawEvaluation (m : ℝ → ℝ) (u : FeatureSpace) (x : ℝ) : ℝ := sqrt (m x) * inner ℝ (feature x) u

/--
The stated quantitative bound `‖rawEvaluation m u x‖ ≤ ‖u‖ * ‖sqrt (m x)‖`.

Use: `chebyshev2.Continuum.evaluationLinear_bound` uses this bound to establish the stated
quantitative bound `‖evaluationLinear hm hn u‖ ≤ ‖sqrtDensity hm hn‖ * ‖u‖`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_norm` with the arguments
shown in the proof.
-/
theorem rawEvaluation_bound (m : ℝ → ℝ) (u : FeatureSpace) (x : ℝ) :
    ‖rawEvaluation m u x‖ ≤ ‖u‖ * ‖sqrt (m x)‖ := by
  have h := norm_inner_le_norm (𝕜 := ℝ) (feature x) u
  rw [feature_norm, one_mul] at h
  simpa only [rawEvaluation, norm_mul, mul_comm] using
    mul_le_mul_of_nonneg_left h (norm_nonneg (sqrt (m x)))

/--
The precise assertion is `MemLp (rawEvaluation m u) 2 volume`.

Use: `chebyshev2.Continuum.evaluationLinear` uses this assertion in the displayed
construction of `evaluationLinear`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.sqrtDensity_memLp`,
`chebyshev2.Continuum.feature_continuous`, `chebyshev2.Continuum.rawEvaluation_bound`
with the arguments shown in the proof.
-/
theorem rawEvaluation_memLp {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (u : FeatureSpace) :
    MemLp (rawEvaluation m u) 2 volume := by
  apply (sqrtDensity_memLp hm hn).of_le_mul
  · exact (continuous_sqrt.comp_aestronglyMeasurable hm.aestronglyMeasurable).mul
      (feature_continuous.inner continuous_const).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (rawEvaluation_bound m u)

/--
Constructs `evaluationLinear` of type `FeatureSpace →ₗ[ℝ] FeatureSpace` by the displayed record
fields. Data fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.Continuum.evaluationOperator` uses this definition in the displayed
construction of `evaluationOperator`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def evaluationLinear {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    FeatureSpace →ₗ[ℝ] FeatureSpace where
  toFun u := (rawEvaluation_memLp hm hn u).toLp (rawEvaluation m u)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(rawEvaluation_memLp hm hn (u+v)).coeFn_toLp,
      (rawEvaluation_memLp hm hn u).coeFn_toLp,
      (rawEvaluation_memLp hm hn v).coeFn_toLp, Lp.coeFn_add
        ((rawEvaluation_memLp hm hn u).toLp (rawEvaluation m u))
        ((rawEvaluation_memLp hm hn v).toLp (rawEvaluation m v))] with x h₁ h₂ h₃ h₄
    rw [h₁, h₄]
    change rawEvaluation m (u + v) x = _ + _
    rw [h₂, h₃]
    simp [rawEvaluation, inner_add_right, mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(rawEvaluation_memLp hm hn (c • u)).coeFn_toLp,
      (rawEvaluation_memLp hm hn u).coeFn_toLp,
      Lp.coeFn_smul c ((rawEvaluation_memLp hm hn u).toLp (rawEvaluation m u))] with x h₁ h₂ h₃
    change _ = (c • ((rawEvaluation_memLp hm hn u).toLp (rawEvaluation m u))) x
    rw [h₁, h₃]
    change rawEvaluation m (c • u) x = c * _
    rw [h₂]
    simp [rawEvaluation, real_inner_smul_right, mul_left_comm]

/--
The stated quantitative bound `‖evaluationLinear hm hn u‖ ≤ ‖sqrtDensity hm hn‖ * ‖u‖`.

Use: `chebyshev2.Continuum.evaluationOperator` uses this bound in the displayed
construction of `evaluationOperator`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem evaluationLinear_bound {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (u : FeatureSpace) :
    ‖evaluationLinear hm hn u‖ ≤ ‖sqrtDensity hm hn‖ * ‖u‖ := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(rawEvaluation_memLp hm hn u).coeFn_toLp,
    (sqrtDensity_memLp hm hn).coeFn_toLp] with x hu hr
  change ‖((rawEvaluation_memLp hm hn u).toLp (rawEvaluation m u)) x‖ ≤
    ‖u‖ * ‖((sqrtDensity_memLp hm hn).toLp (fun x => sqrt (m x))) x‖
  rw [hu, hr]
  exact rawEvaluation_bound m u x

/--
Defines `evaluationOperator` of type `FeatureSpace →L[ℝ] FeatureSpace` by `(evaluationLinear hm
hn).mkContinuous ‖sqrtDensity hm hn‖ (evaluationLinear_bound hm hn)`.

Use: `chebyshev2.Continuum.kernelOperator` uses this definition in the displayed
construction of `kernelOperator`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def evaluationOperator {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    FeatureSpace →L[ℝ] FeatureSpace :=
  (evaluationLinear hm hn).mkContinuous ‖sqrtDensity hm hn‖ (evaluationLinear_bound hm hn)

/--
The precise assertion is `evaluationOperator hm hn u =ᵐ[volume] rawEvaluation m u`.

Use: `chebyshev2.Continuum.evaluationOperator_adjoint_apply` uses this identity to
establish exact identity `(evaluationOperator hm hn).adjoint f = ∫ x, (sqrt (m x) * f x) •
feature x`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.rawEvaluation_memLp` with the
arguments shown in the proof.
-/
theorem evaluationOperator_coe {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (u : FeatureSpace) :
    evaluationOperator hm hn u =ᵐ[volume] rawEvaluation m u := (rawEvaluation_memLp hm hn u).coeFn_toLp

/--
Exact identity `inner ℝ (evaluationOperator hm hn u) (evaluationOperator hm hn v) = inner ℝ u
(densityOperator m v)`.

Use: `chebyshev2.Continuum.evaluationOperator_adjoint_comp` rewrites with this identity to
establish exact identity `(evaluationOperator hm hn).adjoint ∘L evaluationOperator hm hn =
densityOperator m`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem evaluationOperator_inner {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (u v : FeatureSpace) : inner ℝ (evaluationOperator hm hn u) (evaluationOperator hm hn v) =
      inner ℝ u (densityOperator m v) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [L2.inner_def, densityOperator_inner hm]
  apply integral_congr_ae
  filter_upwards [evaluationOperator_coe hm hn u, evaluationOperator_coe hm hn v] with x hu hv
  rw [hu, hv]
  simp only [rawEvaluation, RCLike.inner_apply, conj_trivial]
  calc
    _ = sqrt (m x)^2 * (inner ℝ (feature x) u * inner ℝ (feature x) v) := by ring
    _ = _ := by rw [sq_sqrt (hn x)]

/--
A* A is the actual Bochner feature operator; no assumed spectral model.

Exact identity `(evaluationOperator hm hn).adjoint ∘L evaluationOperator hm hn =
densityOperator m`.

Use: `chebyshev2.Continuum.densityKernelEigenspaceEquiv` uses this identity in the
displayed construction of `densityKernelEigenspaceEquiv`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.evaluationOperator_inner` with
the arguments shown in the proof.
-/
theorem evaluationOperator_adjoint_comp {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    (evaluationOperator hm hn).adjoint ∘L evaluationOperator hm hn = densityOperator m := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, evaluationOperator_inner]

/--
The Birman--Schwinger operator on L2(dx), defined by its Gram factorization.

Use: `chebyshev2.Continuum.kernelOperator_coe` uses this definition to establish the stated
quantitative bound `kernelOperator hm hn f =ᵐ[volume] (fun x => sqrt (m x) * ∫ y, exp (-|x-y|)
* sqrt (m y) * f y)`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packedKernel_hasSum_square_trace`.
-/
def kernelOperator {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) : FeatureSpace →L[ℝ] FeatureSpace :=
  evaluationOperator hm hn ∘L (evaluationOperator hm hn).adjoint

/--
The precise assertion is `(kernelOperator hm hn).IsPositive`.

Use: `chebyshev2.Continuum.kernelSpectralData` uses this assertion in the displayed
construction of `kernelSpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packedKernel_hasSum_square_trace`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem kernelOperator_positive {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    (kernelOperator hm hn).IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint _


/--
Integrability of the displayed function: `Integrable (fun x => sqrt (m x) * f x)`.

Use: `chebyshev2.Continuum.synthesis_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun x => (sqrt (m x) * f x) •
feature x)`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem synthesis_coefficient_integrable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (f : FeatureSpace) : Integrable (fun x => sqrt (m x) * f x) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (sqrtDensity hm hn) f).congr
  filter_upwards [(sqrtDensity_memLp hm hn).coeFn_toLp] with x hx
  change inner ℝ (((sqrtDensity_memLp hm hn).toLp (fun x => sqrt (m x))) x) (f x) = _
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/--
Integrability of the displayed function: `Integrable (fun x => (sqrt (m x) * f x) • feature
x)`.

Use: `chebyshev2.Continuum.evaluationOperator_adjoint_apply` rewrites with this
integrability result to establish the identity `(evaluationOperator hm hn).adjoint f = ∫ x,
(sqrt (m x) * f x) • feature x`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Use the identities/estimates
`chebyshev2.Continuum.synthesis_coefficient_integrable`,
`chebyshev2.Continuum.feature_continuous`, `chebyshev2.Continuum.feature_norm` with the
arguments shown in the proof.
-/
theorem synthesis_integrable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (f : FeatureSpace) : Integrable (fun x => (sqrt (m x) * f x) • feature x) := by
  apply (synthesis_coefficient_integrable hm hn f).norm.mono'
  · exact ((continuous_sqrt.comp_aestronglyMeasurable hm.aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)).smul feature_continuous.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by simp [norm_smul, feature_norm])

/--
The adjoint is the article's synthesis integral, on the actual L2 classes.

Exact identity `(evaluationOperator hm hn).adjoint f = ∫ x, (sqrt (m x) * f x) • feature x`.

Use: `chebyshev2.Continuum.kernelOperator_coe` rewrites with this identity to establish the
stated quantitative bound `kernelOperator hm hn f =ᵐ[volume] (fun x => sqrt (m x) * ∫ y, exp
(-|x-y|) * sqrt (m y) * f y)`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem evaluationOperator_adjoint_apply {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (f : FeatureSpace) : (evaluationOperator hm hn).adjoint f =
      ∫ x, (sqrt (m x) * f x) • feature x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def,
    ← integral_inner (synthesis_integrable hm hn f) u]
  apply integral_congr_ae
  filter_upwards [evaluationOperator_coe hm hn u] with x hx
  rw [hx]
  simp only [rawEvaluation, RCLike.inner_apply, conj_trivial, real_inner_smul_right]
  rw [real_inner_comm u (feature x)]
  ring

/--
The factorization gives exactly the integral kernel printed in Section 2.2.

The stated quantitative bound `kernelOperator hm hn f =ᵐ[volume] (fun x => sqrt (m x) * ∫ y,
exp (-|x-y|) * sqrt (m y) * f y)`.

Use: `chebyshev2.GroundState.kernel_absolute_domination` uses this identity to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, |kernelOperator hm hn f
x| ≤ kernelOperator hm hn (absoluteLp f) x`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem kernelOperator_coe {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (f : FeatureSpace) : kernelOperator hm hn f =ᵐ[volume]
      (fun x => sqrt (m x) * ∫ y, exp (-|x-y|) * sqrt (m y) * f y) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [evaluationOperator_coe hm hn ((evaluationOperator hm hn).adjoint f)] with x hx
  change (evaluationOperator hm hn ((evaluationOperator hm hn).adjoint f)) x = _
  rw [hx, rawEvaluation, evaluationOperator_adjoint_apply,
    ← integral_inner (synthesis_integrable hm hn f) (feature x)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    change inner ℝ (feature x) ((sqrt (m y) * f y) • feature y) = _
    rw [real_inner_smul_right, feature_inner]
    ring)

end
end chebyshev2.Continuum
