import chebyshev1.Nonlinear.Methods
import chebyshev1.Nonlinear.AveragedHessian

/-!
Article: chebyshev1, Corollary 5.4.
Corollary 5.4 in coordinates centered at the stationary point.
Result: `chebyshev1.Nonlinear.lipschitzHessian_error_le` supplies the stated article conclusion.
-/
namespace chebyshev1.Nonlinear
noncomputable section
open scoped Matrix.Norms.L2Operator
open Set Polynomial Polynomial.Chebyshev
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
Defines `gradientCoordinates` of type `(d → ℝ) → d → ℝ` by `fun v => WithLp.ofLp (g
(WithLp.toLp 2 v))`.

Use: `chebyshev1.Nonlinear.errorTrajectory` uses this definition in the displayed
construction of `errorTrajectory`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.
-/
def gradientCoordinates (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d) :
    (d → ℝ) → d → ℝ := fun v => WithLp.ofLp (g (WithLp.toLp 2 v))

/--
Defines `hessianMatrix` of type `Matrix d d ℝ` by `(Matrix.toEuclideanCLM (n := d) (𝕜 :=
ℝ)).symm A`.

Use: `chebyshev1.Nonlinear.lipschitzHessian_error_le` rewrites with this definition to
establish the stated quantitative bound `‖errorTrajectory family I N g e0 N‖ ≤ I.epsilon N * (T
ℝ N).eval (1+rho*R/I.delta) * ‖e0‖`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.
-/
def hessianMatrix (A : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) : Matrix d d ℝ :=
  (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).symm A

/--
Exact identity `opNorm (hessianMatrix A) = ‖A‖`.

Use: `chebyshev1.Nonlinear.lipschitzHessian_error_le` uses this identity to establish the
stated quantitative bound `‖errorTrajectory family I N g e0 N‖ ≤ I.epsilon N * (T ℝ N).eval
(1+rho*R/I.delta) * ‖e0‖`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem opNorm_hessianMatrix (A : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    opNorm (hessianMatrix A) = ‖A‖ := by
  rw [opNorm, ← Matrix.l2_opNorm_toEuclideanCLM]
  simp [hessianMatrix]

/--
Defines `errorTrajectory` of type `EuclideanSpace ℝ d` by `WithLp.toLp 2 (((family.data
N).method I).nonlinearError (gradientCoordinates g) (WithLp.ofLp e0) s)`.

Use: `chebyshev1.Nonlinear.lipschitzHessian_error_le` uses this definition to establish the
stated quantitative bound `‖errorTrajectory family I N g e0 N‖ ≤ I.epsilon N * (T ℝ N).eval
(1+rho*R/I.delta) * ‖e0‖`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.
-/
def errorTrajectory (family : MethodFamily) (I : SpectralInterval) (N : ℕ)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d) (e0 : EuclideanSpace ℝ d)
    (s : ℕ) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 (((family.data N).method I).nonlinearError
    (gradientCoordinates g) (WithLp.ofLp e0) s)

/--
Corollary 5.4 in coordinates centered at the stationary point. The derivative and continuity
hypotheses are required only along the queried segments; they follow from a C² objective on the
convex region in the paper.

The stated quantitative bound `‖errorTrajectory family I N g e0 N‖ ≤ I.epsilon N * (T ℝ N).eval
(1+rho*R/I.delta) * ‖e0‖`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Corollary 5.4.

Proof: Use the identities/estimates `chebyshev1.Nonlinear.averagedDerivative_apply`,
`chebyshev1.Nonlinear.averagedDerivative_sub_norm_le`,
`chebyshev1.Nonlinear.opNorm_hessianMatrix` with the arguments shown in the proof.
-/
theorem lipschitzHessian_error_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ) (hrho : 0 ≤ rho) (hR : 0 ≤ R)
    (hg0 : g 0 = 0)
    (hH : (hessianMatrix (A 0)).IsHermitian)
    (hspec : spectrum ℝ (hessianMatrix (A 0)) ⊆ Icc I.mu I.L)
    (hA : ∀ s < N, ContinuousOn
      (fun t : ℝ => A (t • errorTrajectory family I N g e0 s)) (Icc 0 1))
    (hder : ∀ s < N, ∀ t ∈ Icc (0:ℝ) 1,
      HasFDerivAt g (A (t • errorTrajectory family I N g e0 s))
        (t • errorTrajectory family I N g e0 s))
    (hlip : ∀ s < N, ∀ t ∈ Icc (0:ℝ) 1,
      ‖A (t • errorTrajectory family I N g e0 s)-A 0‖ ≤
        rho * ‖t • errorTrajectory family I N g e0 s‖)
    (hbound : ∀ s < N, ‖errorTrajectory family I N g e0 s‖ ≤ R) :
    ‖errorTrajectory family I N g e0 N‖ ≤
      I.epsilon N * (T ℝ N).eval (1+rho*R/I.delta) * ‖e0‖ := by
  -- Use the identities/estimates `chebyshev1.Nonlinear.averagedDerivative_apply`,
  -- `chebyshev1.Nonlinear.averagedDerivative_sub_norm_le`,
  -- `chebyshev1.Nonlinear.opNorm_hessianMatrix` with the arguments shown in the proof.
  let Hs : ℕ → Matrix d d ℝ := fun s =>
    hessianMatrix (averagedDerivative A 0 (errorTrajectory family I N g e0 s))
  have heq (s : ℕ) (hs : s < N) :
      gradientCoordinates g (((family.data N).method I).nonlinearError
        (gradientCoordinates g) (WithLp.ofLp e0) s) =
      (Hs s).mulVec (((family.data N).method I).nonlinearError
        (gradientCoordinates g) (WithLp.ofLp e0) s) := by
    have ha := averagedDerivative_apply g A 0 (errorTrajectory family I N g e0 s)
      (by simpa using hA s hs) (by simpa using hder s hs)
    simp only [zero_add, hg0, sub_zero] at ha
    have ht : Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Hs s) =
        averagedDerivative A 0 (errorTrajectory family I N g e0 s) := by
      simp [Hs, hessianMatrix]
    rw [← ht] at ha
    exact (congrArg WithLp.ofLp ha).symm
  have herr : ∀ s < N, opNorm (Hs s-hessianMatrix (A 0)) ≤ rho*R/2 := by
    intro s hs
    have ha := averagedDerivative_sub_norm_le A 0 (errorTrajectory family I N g e0 s)
      rho (by simpa using hA s hs) (by simpa using hlip s hs)
    have hn : opNorm (Hs s-hessianMatrix (A 0)) =
        ‖averagedDerivative A 0 (errorTrajectory family I N g e0 s)-A 0‖ := by
      change opNorm (hessianMatrix _ - hessianMatrix _) = _
      change opNorm ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).symm _ - (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).symm _) = _
      rw [← map_sub]
      exact opNorm_hessianMatrix _
    rw [hn]
    exact ha.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound s hs) hrho) (by norm_num))
  have hb := family.transfer_le I hN (hessianMatrix (A 0)) hH hspec Hs (rho*R/2)
    (by positivity) herr
  have hv := ((family.data N).method I).nonlinearError_eq_transfer_upto
    (gradientCoordinates g) (WithLp.ofLp e0) Hs N heq N le_rfl
  have hm := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)
    (((family.data N).realization I).operatorTransfer N Hs)).le_opNorm e0
  change ‖WithLp.toLp 2 _‖ ≤ _
  rw [hv]
  change ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)
    (((family.data N).realization I).operatorTransfer N Hs) e0‖ ≤ _
  refine hm.trans ?_
  change opNorm (((family.data N).realization I).operatorTransfer N Hs) * ‖e0‖ ≤ _
  have hb' := mul_le_mul_of_nonneg_right hb (norm_nonneg e0)
  convert hb' using 1
  congr 2
  ring_nf

end
end chebyshev1.Nonlinear
