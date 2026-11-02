import jacobi.Trichotomy.SupercriticalTail

/-!
Article: jacobi, Proposition C.4.
The result is a direct substitution into the fully proved genuine
supercritical packing theorem, retaining the same original density.
Use: closes the persymmetric-tail assertion in the original residual-polynomial application, independently of the already proved finite terminal realization identities.
-/
namespace jacobi.Applications
noncomputable section
open Real Filter jacobi.Trichotomy
open scoped Topology

/-- The actual packed persymmetric density of the Nesterov Jacobi factor has exactly its printed two-sided spatial exponential rate.
Use: closes the persymmetric-tail assertion in the original residual-polynomial application, independently of the already proved finite terminal realization identities.
Article: jacobi, Proposition C.4.
Proof: b>-1 puts the actual order b/2 in the full supercritical range. Substitute it into the genuine both-end tail theorem and simplify the positive original denominator. -/
theorem nesterov_packing_tail {b : ℝ} (hb : -1<b) :
    Tendsto (fun x : ℝ => log (packedDensity (b/2) (by linarith) x)/|x|)
      (cocompact ℝ) (𝓝 (-8/(b+1))) := by
  have h := supercritical_density_tail (a := b/2) (by linarith) (by linarith)
  have he : -2/(b/2/2+1/4)= -8/(b+1) := by
    rw [show b/2/2+1/4=(b+1)/4 by ring,div_div_eq_mul_div]
    ring
  rwa [he] at h

end
end jacobi.Applications
