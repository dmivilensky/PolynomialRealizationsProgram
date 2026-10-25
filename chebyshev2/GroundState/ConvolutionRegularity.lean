import chebyshev2.GroundState.ConvolutionHalves
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Article: chebyshev2, Theorem 3.1.
The article's sharp pointwise bound, for arbitrary nonnegative L1 forcing.
Use: `chebyshev2.GroundState.convolutionSlope_abs_le` feeds
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
Defines `convolutionSlope` of type `ℝ` by `rightGreen j x-leftGreen j x`.

Use: `chebyshev2.GroundState.convolution_contDiff` uses this definition to establish
smoothness to the stated order: `ContDiff ℝ 1 (H1.rep (convolution j))`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.
-/
def convolutionSlope (j : ℝ → ℝ) (x : ℝ) : ℝ := rightGreen j x-leftGreen j x

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(convolutionSlope j) a b`.

Use: `chebyshev2.GroundState.convolutionSlope_continuous` uses this assertion to establish
continuity of the displayed function: `Continuous (convolutionSlope j)`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Use the identities/estimates `chebyshev2.GroundState.rightGreen_locallyAC`,
`chebyshev2.GroundState.leftGreen_locallyAC` with the arguments shown in the proof.
-/
theorem convolutionSlope_locallyAC {j : ℝ → ℝ} (hj : Integrable j) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (convolutionSlope j) a b := by
  apply ((rightGreen_locallyAC hj a b).sub (leftGreen_locallyAC hj a b)).congr
  intro x _
  rfl

/--
Continuity of the displayed function: `Continuous (convolutionSlope j)`.

Use: `chebyshev2.GroundState.convolution_contDiff` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (H1.rep (convolution j))`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Proof: Use the identities/estimates `chebyshev2.GroundState.locallyAC_continuous`,
`chebyshev2.GroundState.convolutionSlope_locallyAC` with the arguments shown in the proof.
-/
theorem convolutionSlope_continuous {j : ℝ → ℝ} (hj : Integrable j) : Continuous (convolutionSlope j) :=
  locallyAC_continuous (convolutionSlope_locallyAC hj)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (H1.rep
(convolution j)) (convolutionSlope j x) x`.

Use: `chebyshev2.GroundState.convolutionSlope_memLp` uses this assertion to establish the
precise assertion is `MemLp (convolutionSlope j) 2 volume`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem convolution_derivative_ae {j : ℝ → ℝ} (hj : Integrable j) :
    ∀ᵐ x, HasDerivAt (H1.rep (convolution j)) (convolutionSlope j x) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have he : (fun x => leftGreen j x+rightGreen j x)=H1.rep (convolution j) :=
    funext (fun x => (convolution_halves hj x).symm)
  filter_upwards [leftGreen_derivative_ae hj,rightGreen_derivative_ae hj] with x hl hr
  have hd := hl.add hr
  change HasDerivAt (fun x => leftGreen j x+rightGreen j x)
    ((-leftGreen j x+j x)+(rightGreen j x-j x)) x at hd
  rw [he] at hd
  convert hd using 1
  dsimp [convolutionSlope]
  ring

/--
The actual derivative at the stated point: `HasDerivAt (H1.rep (convolution j))
(convolutionSlope j x) x`.

Use: `chebyshev2.GroundState.convolution_contDiff` uses this derivative formula to
establish smoothness to the stated order: `ContDiff ℝ 1 (H1.rep (convolution j))`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.locallyAC_hasDerivAt_of_continuous`,
`chebyshev2.Sobolev.H1.regular`, `chebyshev2.GroundState.convolution_derivative_ae`
with the arguments shown in the proof.
-/
theorem convolution_hasDerivAt {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    HasDerivAt (H1.rep (convolution j)) (convolutionSlope j x) x :=
  locallyAC_hasDerivAt_of_continuous (H1.regular (convolution j)).locally_ac
    (convolution_derivative_ae hj) (convolutionSlope_continuous hj) x

/--
Smoothness to the stated order: `ContDiff ℝ 1 (H1.rep (convolution j))`.

Use: `chebyshev2.GroundState.exists_regular_positive_ground` uses this assertion to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem convolution_contDiff {j : ℝ → ℝ} (hj : Integrable j) : ContDiff ℝ 1 (H1.rep (convolution j)) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (convolution_hasDerivAt hj x).differentiableAt, ?_⟩
  have he : deriv (H1.rep (convolution j))=convolutionSlope j :=
    funext (fun x => (convolution_hasDerivAt hj x).deriv)
  rw [he]
  exact convolutionSlope_continuous hj

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(convolutionSlope j) (H1.rep (convolution j) x-2*j x) x`.

Use: `chebyshev2.GroundState.exists_regular_positive_ground` uses this assertion to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem convolution_second_derivative_ae {j : ℝ → ℝ} (hj : Integrable j) :
    ∀ᵐ x, HasDerivAt (convolutionSlope j) (H1.rep (convolution j) x-2*j x) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [leftGreen_derivative_ae hj,rightGreen_derivative_ae hj] with x hl hr
  have hd := hr.sub hl
  change HasDerivAt (convolutionSlope j)
    ((rightGreen j x-j x)-(-leftGreen j x+j x)) x at hd
  convert hd using 1
  rw [convolution_halves hj]
  ring

/--
The precise assertion is `MemLp (convolutionSlope j) 2 volume`.

Use: `chebyshev2.GroundState.exists_regular_positive_ground` uses this assertion to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem convolutionSlope_memLp {j : ℝ → ℝ} (hj : Integrable j) : MemLp (convolutionSlope j) 2 volume := by
  apply (H1.regular (convolution j)).derivative_memLp.ae_eq
  filter_upwards [(H1.regular (convolution j)).derivative_ae,convolution_derivative_ae hj] with x ha hb
  exact ha.unique hb

/--
The stated quantitative bound `0 ≤ leftGreen j x`.

Use: `chebyshev2.GroundState.convolutionSlope_abs_le` uses this bound to establish the
stated quantitative bound `|convolutionSlope j x| ≤ H1.rep (convolution j) x`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem leftGreen_nonneg {j : ℝ → ℝ} (hn : ∀ᵐ x, 0 ≤ j x) (x : ℝ) :
    0 ≤ leftGreen j x := by
  apply mul_nonneg (exp_pos _).le
  apply integral_nonneg_of_ae
  exact (ae_restrict_of_ae hn).mono (fun t ht => mul_nonneg (exp_pos _).le ht)

/--
The stated quantitative bound `0 ≤ rightGreen j x`.

Use: `chebyshev2.GroundState.convolutionSlope_abs_le` uses this bound to establish the
stated quantitative bound `|convolutionSlope j x| ≤ H1.rep (convolution j) x`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem rightGreen_nonneg {j : ℝ → ℝ} (hn : ∀ᵐ x, 0 ≤ j x) (x : ℝ) :
    0 ≤ rightGreen j x := by
  apply mul_nonneg (exp_pos _).le
  apply integral_nonneg_of_ae
  exact (ae_restrict_of_ae hn).mono (fun t ht => mul_nonneg (exp_pos _).le ht)

/--
The article's sharp pointwise bound, for arbitrary nonnegative L1 forcing.

The stated quantitative bound `|convolutionSlope j x| ≤ H1.rep (convolution j) x`.

Use: `chebyshev2.GroundState.exists_regular_positive_ground` uses this bound to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Use the identities/estimates `chebyshev2.GroundState.convolution_halves`,
`chebyshev2.GroundState.leftGreen_nonneg`, `chebyshev2.GroundState.rightGreen_nonneg`
with the arguments shown in the proof.
-/
theorem convolutionSlope_abs_le {j : ℝ → ℝ} (hj : Integrable j) (hn : ∀ᵐ x, 0 ≤ j x) (x : ℝ) :
    |convolutionSlope j x| ≤ H1.rep (convolution j) x := by
  rw [convolution_halves hj]
  change |rightGreen j x-leftGreen j x| ≤ leftGreen j x+rightGreen j x
  exact abs_sub_le_iff.mpr ⟨by
    linarith [leftGreen_nonneg hn x], by
    linarith [rightGreen_nonneg hn x]⟩

end
end chebyshev2.GroundState
