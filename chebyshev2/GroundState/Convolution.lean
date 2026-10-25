import chebyshev2.Sobolev.Operators

/-!
Article: chebyshev2, Theorem 3.1.
The exponential convolution, as an actual H1 element for arbitrary L1 data.
Use: `chebyshev2.GroundState.convolution_positive` feeds
`chebyshev2.GroundState.exists_regular_positive_ground` (Classical and Sobolev regularity of the
ground state, for general L1 density: no continuity or boundedness of m is assumed).
Proof chain: `chebyshev2.GroundState.ground_state` — chebyshev2, Theorem 3.1; Sharp
ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace chebyshev2.GroundState
noncomputable section
open chebyshev2.Continuum chebyshev2.Sobolev Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Integrability of the displayed function: `Integrable (fun x => j x • feature x)`.

Use: `chebyshev2.GroundState.convolution_rep` rewrites with this integrability result to
establish exact identity `H1.rep (convolution j) x=∫ y, exp (-|x-y|)*j y`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_continuous`,
`chebyshev2.Continuum.feature_norm` with the arguments shown in the proof.
-/
theorem synthesisL1_integrable {j : ℝ → ℝ} (hj : Integrable j) :
    Integrable (fun x => j x • feature x) := by
  apply hj.norm.mono'
  · exact hj.aestronglyMeasurable.smul feature_continuous.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by simp [norm_smul,feature_norm])

/--
The exponential convolution, as an actual H1 element for arbitrary L1 data.

Use: `chebyshev2.GroundState.convolution_rep` rewrites with this definition to establish
exact identity `H1.rep (convolution j) x=∫ y, exp (-|x-y|)*j y`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.
-/
def convolution (j : ℝ → ℝ) : H1 := sqrt 2 • ∫ x, j x • feature x

/--
Exact identity `H1.rep (convolution j) x=∫ y, exp (-|x-y|)*j y`.

Use: `chebyshev2.GroundState.convolution_positive` rewrites with this identity to establish
the stated quantitative bound `0 < H1.rep (convolution j) x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem convolution_rep {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    H1.rep (convolution j) x=∫ y, exp (-|x-y|)*j y := by
  simp only [H1.rep, causalValue, convolution, real_inner_smul_right,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (sqrt_pos.mpr (by norm_num : (0:ℝ)<2))), one_mul]
  rw [← integral_inner (synthesisL1_integrable hj) (feature x)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun y => by
    change inner ℝ (feature x) (j y • feature y)=exp (-|x-y|)*j y
    rw [real_inner_smul_right,feature_inner,mul_comm]))

/--
Integrability of the displayed function: `Integrable (fun y => exp (-|x-y|)*j y)`.

Use: `chebyshev2.GroundState.convolution_positive` uses this integrability result to
establish the stated quantitative bound `0 < H1.rep (convolution j) x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem convolution_kernel_integrable {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    Integrable (fun y => exp (-|x-y|)*j y) := by
  apply hj.norm.mono'
  · exact ((continuous_exp.comp ((continuous_const.sub continuous_id).abs.neg)).aestronglyMeasurable).mul
      hj.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun y => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))))

/--
The stated quantitative bound `0 < H1.rep (convolution j) x`.

Use: `chebyshev2.GroundState.exists_positive_ground_eigenfunction` uses this bound to
establish constructs witnesses with the exact properties `∃ u : H1, (∀ x, 0 < H1.rep u x) ∧
densityOperator m u=kernelEigenvalue hm hn 0 • u`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem convolution_positive {j : ℝ → ℝ} (hj : Integrable j)
    (hn : ∀ᵐ y, 0 ≤ j y) (hM : 0 < ∫ y, j y) (x : ℝ) :
    0 < H1.rep (convolution j) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [convolution_rep hj]
  have hi := convolution_kernel_integrable hj x
  have hp : ∀ᵐ y, 0 ≤ exp (-|x-y|)*j y := hn.mono (fun y hy => mul_nonneg (exp_pos _).le hy)
  apply lt_of_le_of_ne (integral_nonneg_of_ae hp)
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae hp hi).mp he.symm
  have hjz : j =ᵐ[volume] 0 := by
    filter_upwards [hz] with y hy
    exact (mul_eq_zero.mp hy).resolve_left (exp_ne_zero _)
  have hmz : (∫ y, j y)=0 := by simpa using integral_congr_ae hjz
  linarith

/--
Exact identity `inner ℝ v (convolution (fun x => sqrt (m x)*f x)) = sqrt 2*inner ℝ
(evaluationOperator hm hn v) f`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.1.

Proof: Use the identities/estimates `chebyshev2.Continuum.evaluationOperator_adjoint_apply`
with the arguments shown in the proof.
-/
theorem convolution_weak_equation {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (f : FeatureSpace) (v : H1) :
    inner ℝ v (convolution (fun x => sqrt (m x)*f x)) =
      sqrt 2*inner ℝ (evaluationOperator hm hn v) f := by
  rw [convolution]
  change inner ℝ v (sqrt 2 • ∫ x, (sqrt (m x)*f x) • feature x)=_
  rw [← evaluationOperator_adjoint_apply hm hn f, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right]

end
end chebyshev2.GroundState
