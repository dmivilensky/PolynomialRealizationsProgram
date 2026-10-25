import chebyshev2.HalfLine.Resolvent

/-!
Article: chebyshev2, Theorem 3.3.
The factorized positive compact operator has exactly the weighted Green kernel in C.1, embedded in
L2(R) by zero extension.
Use: `chebyshev2.HalfLine.operator_coe` feeds `chebyshev2.HalfLine.operator_weightedVector`
(operator weighted Vector).
Proof chain: `chebyshev2.HalfLine.commonMeasure_ode_probability` — chebyshev2, Theorem 3.3; A
common compact probability measure for all scales.
-/
namespace chebyshev2.HalfLine
noncomputable section
open Set MeasureTheory Real chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `inner ℝ (boundaryProjection x (feature t)) (feature y)=2*green x t y`.

Use: `chebyshev2.HalfLine.operator_coe` rewrites with this identity to establish the stated
quantitative bound `operator hm hn x f =ᵐ[volume] (fun t => sqrt (leftDensity m x t)*∫ y, green
x t y*sqrt (leftDensity m x y)*f y)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_inner` with the arguments
shown in the proof.
-/
theorem boundaryProjection_feature_inner {x t y : ℝ} (ht : t ≤ x) (hy : y ≤ x) :
    inner ℝ (boundaryProjection x (feature t)) (feature y)=2*green x t y := by
  -- Use the identities/estimates `chebyshev2.Continuum.feature_inner` with the arguments
  -- shown in the proof.
  change inner ℝ (feature t-inner ℝ (feature x) (feature t) • feature x) (feature y)=_
  rw [inner_sub_left,real_inner_smul_left,feature_inner,feature_inner,feature_inner,
    abs_of_nonneg (sub_nonneg.mpr ht),abs_of_nonneg (sub_nonneg.mpr hy),← exp_add]
  dsimp [green]
  have he : -(x-t)+-(x-y)=t+y-2*x := by ring
  rw [he]
  ring

/--
The factorized positive compact operator has exactly the weighted Green kernel in C.1, embedded
in L2(R) by zero extension.

The stated quantitative bound `operator hm hn x f =ᵐ[volume] (fun t => sqrt (leftDensity m x
t)*∫ y, green x t y*sqrt (leftDensity m x y)*f y)`.

Use: `chebyshev2.HalfLine.operator_weightedVector` uses this identity to establish exact
identity `operator hm hn x (weightedVector hm hn x hy hC)=ᵐ[volume] (fun t => sqrt (leftDensity
m x t)*greenSolution x (fun z => leftDensity m x z*y z) t)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Identify the summands/integrands
on their required domain before replacing the sum or integral.
-/
theorem operator_coe {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) (f : FeatureSpace) : operator hm hn x f =ᵐ[volume]
      (fun t => sqrt (leftDensity m x t)*∫ y, green x t y*sqrt (leftDensity m x y)*f y) := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let A := evaluation hm hn x
  let P := boundaryProjection x
  have hA := evaluationOperator_coe (leftDensity_integrable hm x) (leftDensity_nonneg hn x) (P (A.adjoint f))
  have hs := Lp.coeFn_smul (1/2:ℝ) (A (P (A.adjoint f)))
  filter_upwards [hA,hs] with t ht hsmul
  change ((1/2:ℝ) • A (P (A.adjoint f))) t=_
  rw [hsmul]
  change (1/2:ℝ)*(A (P (A.adjoint f)) t)=_
  change A (P (A.adjoint f)) t=rawEvaluation (leftDensity m x) (P (A.adjoint f)) t at ht
  rw [ht,rawEvaluation]
  by_cases htx : t < x
  · have hsym := (boundaryProjection_positive x).isSymmetric (feature t) (A.adjoint f)
    change inner ℝ (P (feature t)) (A.adjoint f)=inner ℝ (feature t) (P (A.adjoint f)) at hsym
    rw [← hsym]
    dsimp only [A,evaluation]
    rw [evaluationOperator_adjoint_apply,← integral_inner
      (synthesis_integrable (leftDensity_integrable hm x) (leftDensity_nonneg hn x) f) (P (feature t))]
    rw [show (1/2:ℝ)*(sqrt (leftDensity m x t)*∫ y,
      inner ℝ (P (feature t)) ((sqrt (leftDensity m x y)*f y) • feature y))=
      sqrt (leftDensity m x t)*(∫ y, (1/2:ℝ)*
        inner ℝ (P (feature t)) ((sqrt (leftDensity m x y)*f y) • feature y)) by
          rw [integral_const_mul]; ring]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by
      change (1/2:ℝ)*inner ℝ (P (feature t)) ((sqrt (leftDensity m x y)*f y) • feature y)=
        green x t y*sqrt (leftDensity m x y)*f y
      rw [real_inner_smul_right]
      by_cases hyx : y < x
      · rw [boundaryProjection_feature_inner htx.le hyx.le]
        ring
      · simp [leftDensity,hyx])
  · simp [leftDensity,htx]

end
end chebyshev2.HalfLine
