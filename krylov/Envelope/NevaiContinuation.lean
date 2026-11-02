import krylov.Reference.JacobiMeasureDomains
import krylov.Envelope.GaussContinuation
import krylov.Envelope.ContinuationUniformLimit
import krylov.Envelope.HeavyBallPolynomial
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), full original Nevai Gaussian continuation limit.
Use: conclude the printed uniform heavy-ball continuation limit for actual finite Gaussian CG executions along every genuine growing admissible suffix.
Source: original compact probability support and Jacobi recurrence orthogonality, actual measure-derived CG coefficient limits, genuine finite Gaussian coherence and compact polynomial convergence.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference Matrix Polynomial Polynomial.Chebyshev Filter chebyshev1
open scoped Topology

/-- The actual continuations of the original Gaussian rules converge uniformly on the true physical interval to the printed Chebyshev heavy-ball polynomial under the original Nevai hypotheses.
Use: The actual continuations of the original Gaussian rules converge uniformly on the true physical interval to the printed Chebyshev heavy-ball polynomial under the original Nevai hypotheses.
Article: main_krylov, prop:phi(c), full original Nevai Gaussian continuation limit.
Proof: Derive actual common coefficient limits from original measure support and true Jacobi data, transfer every genuine used finite Gaussian suffix, and insert the printed square-root Chebyshev coordinate. -/
theorem nevai_gauss_continuation_uniform (J : JacobiData) (hJ : ∀ n,0≤J.aSq n)
    (hpos : ∀ n,0<n → 0<J.aSq n) (sigma : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure sigma] (I : SpectralInterval)
    (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (ho : ∀ m q,q.natDegree<m → measurePolynomialIntegral sigma I hI (J.leading m*q)=0)
    (hA : Tendsto J.b atTop (𝓝 ((I.L+I.mu)/2)))
    (hB : Tendsto (fun n => Real.sqrt (J.aSq (n+1))) atTop (𝓝 ((I.L-I.mu)/4)))
    (r : ℕ) (N : ℕ → ℕ) (hN : ∀ᶠ j in atTop,j+r<N j) :
    TendstoUniformlyOn (fun j lam =>
      (phi (CG.length (cgOperator (J.matrix 0 (N j))) (WithLp.toLp 2 (JacobiData.site (N j) 0)))
        (CG.beta (cgOperator (J.matrix 0 (N j))) (WithLp.toLp 2 (JacobiData.site (N j) 0))) j r).eval lam)
      (fun lam => (HeavyBallParameters.ratio I)^r*((U ℝ (r:ℤ)).eval (I.z lam)-
        HeavyBallParameters.ratio I*(U ℝ ((r:ℤ)-1)).eval (I.z lam))) atTop (Set.Icc I.mu I.L) := by
  -- The limiting coefficients are derived from the original spectral measure and genuine principal determinants.
  let d := jacobiPivot J.b (fun n => Real.sqrt (J.aSq (n+1)))
  let a := fun n => (d n)⁻¹
  let b := fun n => (Real.sqrt (J.aSq (n+1))/d n)^2
  have hc := jacobiMeasure_nevai_coefficients J hJ hpos sigma I hI ho hA hB
  have h := continuation_uniform_limit a b (HeavyBallParameters.pivot I)⁻¹
    ((HeavyBallParameters.ratio I)^2) hc.1 hc.2 (Set.Icc I.mu I.L) isCompact_Icc r
  have hright := h.congr_right (g := fun lam => (HeavyBallParameters.ratio I)^r*
    ((U ℝ (r:ℤ)).eval (I.z lam)-HeavyBallParameters.ratio I*(U ℝ ((r:ℤ)-1)).eval (I.z lam))) (by
      intro lam _
      dsimp only
      rw [constant_phi_chebyshev _ _ (inv_ne_zero (HeavyBallParameters.pivot_pos I).ne')
        (HeavyBallParameters.ratio_domain I).1.ne' 0 r lam,HeavyBallParameters.coordinate])
  -- Each actual growing finite rule uses exactly the common chronological coefficients before its true termination.
  apply hright.congr
  filter_upwards [hN] with j hj
  intro lam _
  have hw := jacobiMeasure_residual_window J hJ hpos sigma I hI ho
  have he := gauss_phi_common J hpos I.mu I.mu_pos (fun m => (hw m).1) (N j) j r hj.le
  exact congrArg (fun p : ℝ[X] => p.eval lam) he.symm
end
end krylov.Envelope
