import krylov.Envelope.ScenarioCoordinates

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, actual last-singleton source operators.
Use: identify genuine unchanged quadratic prefixes and the true final
probe perturbation caused by a real newest singleton source increment.
Source: actual finite chronological canonical increment sums and the
genuine positive-root physical segment congruence.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine singleton canonical increment contributes its true physical congruence precisely after its actual chronological index.
Use: A genuine singleton canonical increment contributes its true physical congruence precisely after its actual chronological index.
Article: main_krylov, s3:thm:cf, actual last-singleton source operators.
Proof: Compute the real finite singleton prefix sum before applying the genuine metric congruence. -/
theorem singleton_cumulativeDrift (base : Matrix (Fin n) (Fin n) ℝ) (k j : ℕ) (D : Matrix (Fin n) (Fin n) ℝ) :
    cumulativeDrift base (Pi.single k D) j=
      if k<j then cgOperator (metricRoot base*D*metricRoot base) else 0 := by
  classical
  have hs : (∑ l∈range j,(Pi.single k D : ℕ → Matrix (Fin n) (Fin n) ℝ) l)=if k<j then D else 0 := by
    simp [Pi.single_apply]
  unfold cumulativeDrift
  rw [hs]
  split
  · rfl
  · simp only [Matrix.mul_zero,Matrix.zero_mul,map_zero]

/-- Every actual canonical segment before a genuine singleton source increment is exactly the true constant quadratic reference.
Use: Every actual canonical segment before a genuine singleton source increment is exactly the true constant quadratic reference.
Article: main_krylov, s3:thm:cf, actual last-singleton source operators.
Proof: Its real cumulative prefix contains no actual singleton increment. -/
theorem singleton_canonicalPath_before (base : Matrix (Fin n) (Fin n) ℝ) (k j : ℕ)
    (D : Matrix (Fin n) (Fin n) ℝ) (hj : j≤k) (t : ℝ) :
    canonicalFCPath base (Pi.single k D) t j=cgOperator base := by
  rw [canonicalFCPath,singleton_cumulativeDrift]
  rw [ite_eq_right (by omega : ¬ k<j)]
  ext v
  simp only [_root_.add_apply,_root_.smul_apply,_root_.zero_apply,smul_zero,add_zero]

/-- The genuine first changed canonical segment is exactly the true quadratic reference plus the actual parameter times the real singleton congruence.
Use: The genuine first changed canonical segment is exactly the true quadratic reference plus the actual parameter times the real singleton congruence.
Article: main_krylov, s3:thm:cf, actual last-singleton source operators.
Proof: The genuine cumulative prefix contains exactly the true singleton increment. -/
theorem singleton_canonicalPath_last (base : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (D : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    canonicalFCPath base (Pi.single k D) t (k+1)=cgOperator base+t • cgOperator (metricRoot base*D*metricRoot base) := by
  rw [canonicalFCPath,singleton_cumulativeDrift,ite_eq_left (by omega)]
end
end krylov.Envelope
