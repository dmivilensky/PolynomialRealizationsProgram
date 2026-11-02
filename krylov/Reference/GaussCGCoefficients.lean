import krylov.Reference.JacobiOrientation
import krylov.Reference.JacobiCoefficients
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), actual common CG sequence of the Gaussian rules.
Use: identify genuine measured CG coefficients of the original positive-edge Gauss matrices with one common original determinant-pivot sequence.
Source: actual Jacobi orientation covariance, true physical inverse domains and the determinant-derived raw CG dictionary.
-/

namespace krylov.Reference
noncomputable section
open Matrix chebyshev1

/-- All original Gaussian Jacobi rules have the same actual measured CG line and internal recurrence coefficients before their true finite termination.
Use: All original Gaussian Jacobi rules have the same actual measured CG line and internal recurrence coefficients before their true finite termination.
Article: main_krylov, prop:phi(c), actual common CG sequence of the Gaussian rules.
Proof: Transfer the genuine measured coefficients through the first-site-preserving alternating isometry, then read the true common original principal pivots. -/
theorem gauss_cg_coefficients (J : JacobiData) (hpos : ∀ n,0<n → 0<J.aSq n)
    (mu : ℝ) (hmu : 0<mu)
    (hlo : ∀ N,(jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N-mu • 1).PosSemidef)
    (N k : ℕ) (hk : k<N) :
    let g : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (JacobiData.site N 0)
    let d := jacobiPivot J.b (fun n => Real.sqrt (J.aSq (n+1)))
    CG.length (cgOperator (J.matrix 0 N)) g k=(d k)⁻¹ ∧
    (k+1<N → CG.beta (cgOperator (J.matrix 0 N)) g k=(Real.sqrt (J.aSq (k+1))/d k)^2) ∧
    (k+1=N → CG.beta (cgOperator (J.matrix 0 N)) g k=0) := by
  -- Transfer actual computed coefficients only after the genuine original finite inverse domain has been derived.
  dsimp only
  have hB (n : ℕ) : 0<Real.sqrt (J.aSq (n+1)) := Real.sqrt_pos.mpr (hpos (n+1) (by omega))
  have hT := jacobiPrefix_posDef J.b (fun n => Real.sqrt (J.aSq (n+1))) mu hmu N (hlo N)
  have hc := jacobiData_orientation_coefficients J N k
  dsimp only at hc
  refine ⟨hc.1.trans (jacobi_cg_length _ _ hB N hT k hk),?_,?_⟩
  · intro hi
    exact hc.2.trans (jacobi_cg_beta_internal _ _ hB N hT k hi)
  · intro hi
    exact hc.2.trans (jacobi_cg_beta_terminal _ _ hB N hT k hi)
end
end krylov.Reference
