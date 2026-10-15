import «2610.05164v2».Continuum.SpectralQuadratic
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
Article: 2610.05164v2, Theorem 3.1.
Equality in the global Rayleigh bound implies the eigenvector equation.
Use: `«2610.05164v2».Continuum.PositiveSpectralData.top_eigen_of_equality` feeds
`«2610.05164v2».GroundState.exists_nonnegative_maximizer` (The article's nonnegative normalized
Rayleigh maximizer exists for every nonnegative integrable density of positive mass, on the actual
kernel operator).
Proof chain: `«2610.05164v2».GroundState.ground_state` — 2610.05164v2, Theorem 3.1; Sharp
ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace Topology BigOperators
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace PositiveSpectralData
variable {T : E →L[ℝ] E} (D : PositiveSpectralData T)

omit [CompleteSpace E] in
/--
The stated quantitative bound `inner ℝ x (T x) ≤ D.eigenvalue 0*‖x‖^2`.

Use: `«2610.05164v2».Continuum.PositiveSpectralData.top_eigen_of_equality` uses this bound to
establish exact identity `T x=D.eigenvalue 0 • x`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.groundParameter_variational`.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.PositiveSpectralData.quadratic_le_eigenvalue` with the arguments
shown in the proof.
-/
theorem top_quadratic_bound (x : E) : inner ℝ x (T x) ≤ D.eigenvalue 0*‖x‖^2 :=
  D.quadratic_le_eigenvalue 0 x (by simp [spectralSelected])

omit [CompleteSpace E] in
/--
Exact identity `0 < D.eigenvalue 0 ∧ ∃ x : E, ‖x‖=1 ∧ T x=D.eigenvalue 0 • x`.

Use: `«2610.05164v2».GroundState.exists_nonnegative_maximizer` uses this identity to establish
constructs witnesses with the exact properties `∃ f : FeatureSpace, ‖f‖=1 ∧ (∀ᵐ x, 0 ≤ f x) ∧
kernelOperator hm hn f=kernelEigenvalue hm hn 0 • f`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.groundParameter_variational`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities. Prove equality of functions by evaluating both sides at an
arbitrary argument.
-/
theorem top_attained (htrace : 0 < ∑' i, D.eig i) :
    0 < D.eigenvalue 0 ∧ ∃ x : E, ‖x‖=1 ∧ T x=D.eigenvalue 0 • x := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  have hp : ∃ i, 0 < D.eig i := by
    by_contra! hn
    have he : D.eig=0 := funext (fun i => le_antisymm (hn i) (D.nonneg i))
    simp [he] at htrace
  cases he : spectralNext D.summable (spectralSelected D.summable 0) with
  | none =>
    obtain ⟨i,hi⟩ := hp
    have hn := spectralNext_none D.summable he i (by simp [spectralSelected])
    exact (not_lt_of_ge hn hi).elim
  | some i =>
    have hi := spectralNext_some D.summable he
    have hlambda : D.eigenvalue 0=D.eig i := spectralSorted_eq D.summable he
    refine ⟨hlambda ▸ hi.2.1, D.basis i, D.basis.orthonormal.norm_eq_one i, ?_⟩
    rw [hlambda, D.equation]

/--
Equality in the global Rayleigh bound implies the eigenvector equation. The proof uses
mathlib's Lagrange-multiplier theorem on the actual Hilbert sphere.

Exact identity `T x=D.eigenvalue 0 • x`.

Use: `«2610.05164v2».GroundState.exists_nonnegative_maximizer` uses this identity to establish
constructs witnesses with the exact properties `∃ f : FeatureSpace, ‖f‖=1 ∧ (∀ᵐ x, 0 ≤ f x) ∧
kernelOperator hm hn f=kernelEigenvalue hm hn 0 • f`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Separate `x=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem top_eigen_of_equality (hp : T.IsPositive) (x : E)
    (he : inner ℝ x (T x)=D.eigenvalue 0*‖x‖^2) : T x=D.eigenvalue 0 • x := by
  -- Separate `x=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hx : x=0
  · simp [hx]
  have hmax : IsMaxOn T.reApplyInnerSelf (Metric.sphere (0:E) ‖x‖) x := by
    apply isMaxOn_iff.mpr
    intro y hy
    have hy' : ‖y‖=‖x‖ := by simpa only [Metric.mem_sphere, dist_zero_right] using hy
    have hb := D.top_quadratic_bound y
    rw [hy', ← he] at hb
    simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      real_inner_comm] using hb
  have heig := hp.isSelfAdjoint.eq_smul_self_of_isLocalExtrOn_real (Or.inr hmax.isLocalMaxOn)
  rw [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm] at heig
  change T x=(inner ℝ x (T x)/‖x‖^2) • x at heig
  rw [he, mul_div_cancel_right₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))] at heig
  exact heig

end PositiveSpectralData
end
end «2610.05164v2».Continuum
