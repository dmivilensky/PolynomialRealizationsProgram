import bezout.History.Bezout
import Mathlib.Topology.Algebra.Polynomial

/-!
Article: bezout, Theorem 2.1 (the diagonal extension).
Use: the physical divided-difference factorization extends continuously to
coincident spectral parameters, where it is the terminal derivative.
Proof: represent the divided difference by the finite response/query sum.
-/

namespace bezout.History

noncomputable section
variable {N : ℕ}

/-- The physical Bezoutian is jointly continuous in the two spectral parameters.
Article: bezout, Theorem 2.1. Use: the stated continuous diagonal extension. -/
theorem continuous_physical_bezout (h : bezout.History N) :
    Continuous (fun xy : ℝ × ℝ => dividedDifference h.terminal xy.1 xy.2) := by
  have hf : (fun xy : ℝ × ℝ => dividedDifference h.terminal xy.1 xy.2) =
      (fun xy => ∑ s, (h.response s).eval xy.1 * (h.query s).eval xy.2) := by
    funext xy
    exact (h.physical_bezout_all xy.1 xy.2).symm
  rw [hf]
  fun_prop

end
end bezout.History
