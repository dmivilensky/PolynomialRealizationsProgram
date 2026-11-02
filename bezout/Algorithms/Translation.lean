import bezout.Algorithms.Flat
import bezout.Algorithms.Balanced
import bezout.History.Translation

/-!
Article: bezout, Algorithms 1--2 applied to arbitrary centered quadratics.
Use: the literal programs start at the absolute point x0 and call the affine
quadratic oracle; their terminal errors are the established linear-error runs.
Proof: all-oracle-stream program equivalence and causal translation invariance.
-/

namespace bezout.Algorithms
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Flat's absolute-point quadratic execution has exactly the proved terminal error. -/
theorem Flat.affineOracle_output (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (H : E →ₗ[ℝ] E) (initial center : E) (noise : Fin N → E) :
    (Flat.program I N).output (fun s y => H (y-center)+noise s) initial - center =
      ((bezout.Flat.history I N hN).run H (initial-center) noise).output := by
  rw [Flat.output_eq_history I N hN, bezout.History.affineOracle_output]

/-- Balanced's absolute-point quadratic execution has exactly the proved terminal error. -/
theorem Balanced.affineOracle_output (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (H : E →ₗ[ℝ] E) (initial center : E) (noise : Fin N → E) :
    (Balanced.program I N hN).output (fun s y => H (y-center)+noise s) initial - center =
      ((bezout.Balanced.history I N hN).run H (initial-center) noise).output := by
  rw [Balanced.output_eq_history I N hN, bezout.History.affineOracle_output]

end
end bezout.Algorithms
