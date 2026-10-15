import «2610.05164v2».SineContinuum.SineHilbertBasis
import «2610.05164v2».SineContinuum.GreenEigenfunctions
import «2610.05164v2».Continuum.DiagonalOperator
import «2610.05164v2».Continuum.ReferenceSpectrum

/-!
Article: 2610.05164v2, Lemma 5.
Lemma 5's spectral expansion is an equality for the actual integral operator, with convergence in
operator norm.
Use: `«2610.05164v2».SineContinuum.greenOperator_positive` feeds
`«2610.05164v2».SineContinuum.greenOperator_repr` (green Operator repr).
Proof chain: `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range` — 2610.05164v2, Lemma 5;
Legendre operator, nonlogarithmic realization and continuum sine spectrum.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency true

/--
Defines `greenContinuousKernel` of type `C(LegendreInterval × LegendreInterval,ℝ)`. The
displayed construction fixes its component data; its proof fields enforce the listed
compatibility properties.

Use: `«2610.05164v2».SineContinuum.greenEvaluationLinear_bound` uses this definition to
establish the stated quantitative bound `‖greenEvaluationLinear f‖ ≤ greenRowBound*‖f‖`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.
-/
def greenContinuousKernel : C(LegendreInterval × LegendreInterval,ℝ) :=
  ⟨fun z => green z.1 z.2,by
    have hc : Continuous (fun z : LegendreInterval × LegendreInterval => ((z.1:ℝ),(z.2:ℝ))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
    exact green_continuousOn.comp_continuous
      (f := fun z : LegendreInterval × LegendreInterval => ((z.1:ℝ),(z.2:ℝ))) hc
      (fun z => ⟨z.1.property,z.2.property⟩)⟩

/--
Defines `greenRow` of type `LegendreSpace` by `ContinuousMap.toLp 2 volume ℝ
(greenContinuousKernel.curry t)`.

Use: `«2610.05164v2».SineContinuum.greenEvaluation` uses this definition in the displayed
construction of `greenEvaluation`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.
-/
def greenRow (t : LegendreInterval) : LegendreSpace :=
  ContinuousMap.toLp 2 volume ℝ (greenContinuousKernel.curry t)

/--
Continuity of the displayed function: `Continuous greenRow`.

Use: `«2610.05164v2».SineContinuum.greenEvaluation` uses this continuity result in the
displayed construction of `greenEvaluation`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem greenRow_continuous : Continuous greenRow :=
  (ContinuousMap.toLp 2 volume ℝ).continuous.comp greenContinuousKernel.curry.continuous

/--
Defines `greenRowBound` of type `ℝ` by `‖ContinuousMap.toLp (E := ℝ) 2 (volume : Measure
LegendreInterval) ℝ‖* ‖greenContinuousKernel.curry‖`.

Use: `«2610.05164v2».SineContinuum.greenEvaluationLinear_bound` uses this definition to
establish the stated quantitative bound `‖greenEvaluationLinear f‖ ≤ greenRowBound*‖f‖`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.
-/
def greenRowBound : ℝ := ‖ContinuousMap.toLp (E := ℝ) 2 (volume : Measure LegendreInterval) ℝ‖*
  ‖greenContinuousKernel.curry‖

/--
The stated quantitative bound `‖greenRow t‖ ≤ greenRowBound`.

Use: `«2610.05164v2».SineContinuum.greenEvaluationLinear_bound` uses this bound to establish
the stated quantitative bound `‖greenEvaluationLinear f‖ ≤ greenRowBound*‖f‖`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem greenRow_norm (t : LegendreInterval) : ‖greenRow t‖ ≤ greenRowBound :=
  ((ContinuousMap.toLp 2 volume ℝ).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (greenContinuousKernel.curry.norm_coe_le_norm t) (norm_nonneg _))
/--
Defines `greenEvaluation` of type `C(LegendreInterval,ℝ)` by `⟨fun t => inner ℝ (greenRow t)
f,greenRow_continuous.inner continuous_const⟩`.

Use: `«2610.05164v2».SineContinuum.greenEvaluationLinear` uses this definition in the displayed
construction of `greenEvaluationLinear`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.
-/
def greenEvaluation (f : LegendreSpace) : C(LegendreInterval,ℝ) :=
  ⟨fun t => inner ℝ (greenRow t) f,greenRow_continuous.inner continuous_const⟩

/--
Constructs `greenEvaluationLinear` of type `LegendreSpace →ₗ[ℝ] C(LegendreInterval,ℝ)` by the
displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `«2610.05164v2».SineContinuum.greenOperator` uses this definition in the displayed
construction of `greenOperator`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.
-/
def greenEvaluationLinear : LegendreSpace →ₗ[ℝ] C(LegendreInterval,ℝ) where
  toFun := greenEvaluation
  map_add' f g := by
    ext t
    change inner ℝ (greenRow t) (f+g)=inner ℝ (greenRow t) f+inner ℝ (greenRow t) g
    exact inner_add_right _ _ _
  map_smul' c f := by
    ext t
    change inner ℝ (greenRow t) (c • f)=c*inner ℝ (greenRow t) f
    exact real_inner_smul_right _ _ _

/--
The stated quantitative bound `‖greenEvaluationLinear f‖ ≤ greenRowBound*‖f‖`.

Use: `«2610.05164v2».SineContinuum.greenOperator` uses this bound in the displayed construction
of `greenOperator`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.greenRow_norm` with the
arguments shown in the proof.
-/
theorem greenEvaluationLinear_bound (f : LegendreSpace) :
    ‖greenEvaluationLinear f‖ ≤ greenRowBound*‖f‖ := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.greenRow_norm` with the
  -- arguments shown in the proof.
  change ‖greenEvaluation f‖ ≤ greenRowBound*‖f‖
  have hb : 0 ≤ greenRowBound :=
    mul_nonneg (norm_nonneg (ContinuousMap.toLp (E := ℝ) 2 (volume : Measure LegendreInterval) ℝ))
      (norm_nonneg greenContinuousKernel.curry)
  apply ((greenEvaluation f).norm_le
    (mul_nonneg hb (norm_nonneg f))).mpr
  intro t
  exact (norm_inner_le_norm (𝕜 := ℝ) (greenRow t) f).trans
    (mul_le_mul_of_nonneg_right (greenRow_norm t) (norm_nonneg f))

/--
The actual continuous-kernel integral operator on Lebesgue L²(0,1).

Use: `«2610.05164v2».SineContinuum.greenOperator_diagonal` uses this definition to establish
exact identity `greenOperator=Continuum.diagonalOperator sineHilbertBasis (fun n => (mu n)⁻¹)`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.
-/
def greenOperator : LegendreSpace →L[ℝ] LegendreSpace :=
  (ContinuousMap.toLp 2 volume ℝ) ∘L
    greenEvaluationLinear.mkContinuous greenRowBound greenEvaluationLinear_bound

/--
Exact identity `greenOperator f=ᵐ[volume] (fun t : LegendreInterval => inner ℝ (greenRow t)
f)`.

Use: `«2610.05164v2».SineContinuum.greenOperator_basis` uses this identity to establish exact
identity `greenOperator (sineHilbertBasis n)=(mu n)⁻¹ • sineHilbertBasis n`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem greenOperator_ae (f : LegendreSpace) : greenOperator f=ᵐ[volume]
    (fun t : LegendreInterval => inner ℝ (greenRow t) f) :=
  ContinuousMap.coeFn_toLp volume (greenEvaluation f)

/--
Exact identity `greenRow t=ᵐ[volume] (fun s : LegendreInterval => green t s)`.

Use: `«2610.05164v2».SineContinuum.greenRow_eigenfunction` uses this identity to establish
exact identity `inner ℝ (greenRow t) (sineHilbertBasis n)=upsilon n t/mu n`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem greenRow_ae (t : LegendreInterval) : greenRow t=ᵐ[volume]
    (fun s : LegendreInterval => green t s) :=
  ContinuousMap.coeFn_toLp volume (greenContinuousKernel.curry t)

/--
Exact identity `inner ℝ (greenRow t) (sineHilbertBasis n)=upsilon n t/mu n`.

Use: `«2610.05164v2».SineContinuum.greenOperator_basis` rewrites with this identity to
establish exact identity `greenOperator (sineHilbertBasis n)=(mu n)⁻¹ • sineHilbertBasis n`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem greenRow_eigenfunction (n : ℕ) (t : LegendreInterval)
    (ht : (t:ℝ) ∈ Ioo (0:ℝ) 1) :
    inner ℝ (greenRow t) (sineHilbertBasis n)=upsilon n t/mu n := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [L2.inner_def]
  have he : (fun s : LegendreInterval => inner ℝ (greenRow t s) (sineHilbertBasis n s))=ᵐ[volume]
      (fun s : LegendreInterval => green t s*upsilon n s) := by
    filter_upwards [greenRow_ae t,sineHilbertBasis_ae n] with s hg hu
    rw [hg,hu]
    change upsilon n s*green t s=green t s*upsilon n s
    ring
  rw [integral_congr_ae he]
  rw [integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc (fun s : ℝ => green t s*upsilon n s)]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact green_eigenfunction n ht

/--
Exact identity `greenOperator (sineHilbertBasis n)=(mu n)⁻¹ • sineHilbertBasis n`.

Use: `«2610.05164v2».SineContinuum.greenOperator_diagonal` rewrites with this identity to
establish exact identity `greenOperator=Continuum.diagonalOperator sineHilbertBasis (fun n =>
(mu n)⁻¹)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem greenOperator_basis (n : ℕ) :
    greenOperator (sineHilbertBasis n)=(mu n)⁻¹ • sineHilbertBasis n := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply Lp.ext
  filter_upwards [greenOperator_ae (sineHilbertBasis n),
    Lp.coeFn_smul (mu n)⁻¹ (sineHilbertBasis n),sineHilbertBasis_ae n,interval_interior_ae]
    with t hg hs hu ht
  rw [hg,greenRow_eigenfunction n t ht,hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hu,div_eq_mul_inv,mul_comm]

/--
Exact identity `(mu n)⁻¹=(1/2)*Continuum.referenceEigenvalue n`.

Use: `«2610.05164v2».SineContinuum.inverse_mu_summable` uses this identity to establish
summability of the displayed sequence: `Summable (fun n => |(mu n)⁻¹|)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.referenceEigenvalue_eq` with the
arguments shown in the proof.
-/
theorem mu_reference (n : ℕ) : (mu n)⁻¹=(1/2)*Continuum.referenceEigenvalue n := by
  rw [Continuum.referenceEigenvalue_eq]
  dsimp [mu]
  ring

/--
Summability of the displayed sequence: `Summable (fun n => |(mu n)⁻¹|)`.

Use: `«2610.05164v2».SineContinuum.greenOperator_compact` uses this summability result to
establish compactness of the displayed operator: `IsCompactOperator greenOperator`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.mu_reference`,
`«2610.05164v2».Continuum.referenceEigenvalue_pos`,
`«2610.05164v2».Continuum.summable_reference` with the arguments shown in the proof.
-/
theorem inverse_mu_summable : Summable (fun n => |(mu n)⁻¹|) := by
  simpa only [mu_reference,abs_of_pos (mul_pos (by norm_num : (0:ℝ)<1/2)
    (Continuum.referenceEigenvalue_pos _))] using Continuum.summable_reference.mul_left (1/2:ℝ)

/--
Lemma 5's spectral expansion is an equality for the actual integral operator, with convergence
in operator norm.

Exact identity `greenOperator=Continuum.diagonalOperator sineHilbertBasis (fun n => (mu n)⁻¹)`.

Use: `«2610.05164v2».SineContinuum.greenOperator_compact` rewrites with this identity to
establish compactness of the displayed operator: `IsCompactOperator greenOperator`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem greenOperator_diagonal :
    greenOperator=Continuum.diagonalOperator sineHilbertBasis (fun n => (mu n)⁻¹) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  apply ContinuousLinearMap.ext
  intro f
  have h₁ := greenOperator.hasSum (sineHilbertBasis.hasSum_repr f)
  have h₂ := (Continuum.diagonalOperator sineHilbertBasis (fun n => (mu n)⁻¹)).hasSum
    (sineHilbertBasis.hasSum_repr f)
  have he : (fun n => greenOperator (sineHilbertBasis.repr f n • sineHilbertBasis n))=
      (fun n => Continuum.diagonalOperator sineHilbertBasis (fun n => (mu n)⁻¹)
        (sineHilbertBasis.repr f n • sineHilbertBasis n)) := by
    funext n
    rw [map_smul,map_smul,greenOperator_basis,
      Continuum.diagonalOperator_basis sineHilbertBasis inverse_mu_summable]
  rw [he] at h₁
  exact h₁.unique h₂

/--
The value of a convergent infinite sum: `HasSum (fun n => (mu n)⁻¹ • InnerProductSpace.rankOne
ℝ (sineHilbertBasis n) (sineHilbertBasis n)) greenOperator`.

Use: a standalone supporting infinite-sum formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.greenOperator_diagonal`,
`«2610.05164v2».Continuum.diagonalOperator_summable`,
`«2610.05164v2».SineContinuum.inverse_mu_summable` with the arguments shown in the proof.
-/
theorem greenOperator_series : HasSum
    (fun n => (mu n)⁻¹ • InnerProductSpace.rankOne ℝ (sineHilbertBasis n) (sineHilbertBasis n)) greenOperator := by
  rw [greenOperator_diagonal]
  exact (Continuum.diagonalOperator_summable sineHilbertBasis inverse_mu_summable).hasSum

/--
The precise assertion is `greenOperator.IsPositive`.

Use: `«2610.05164v2».SineContinuum.greenOperator_repr` uses this assertion to establish the
precise assertion is `sineHilbertBasis.repr (greenOperator f) n= (mu n)⁻¹*sineHilbertBasis.repr
f n`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.sineOperator_domain_eq_range`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.greenOperator_diagonal`,
`«2610.05164v2».Continuum.diagonalOperator_positive`,
`«2610.05164v2».SineContinuum.inverse_mu_summable` with the arguments shown in the proof.
-/
theorem greenOperator_positive : greenOperator.IsPositive := by
  rw [greenOperator_diagonal]
  exact Continuum.diagonalOperator_positive _ inverse_mu_summable (fun n => (inv_pos.mpr (mu_positive n)).le)

/--
Compactness of the displayed operator: `IsCompactOperator greenOperator`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.greenOperator_diagonal`,
`«2610.05164v2».Continuum.diagonalOperator_isCompact`,
`«2610.05164v2».SineContinuum.inverse_mu_summable` with the arguments shown in the proof.
-/
theorem greenOperator_compact : IsCompactOperator greenOperator := by
  rw [greenOperator_diagonal]
  exact Continuum.diagonalOperator_isCompact _ inverse_mu_summable

end
end «2610.05164v2».SineContinuum
