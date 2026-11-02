import bezout.History.Oracle

/-!
Article: bezout, actual quadratic oracle executions in Algorithms 1--2.
Use: passes between absolute points x and errors x-x_star for any fixed center.
Proof: normalized causal query and output equations commute with translation;
strict-causal oracle uniqueness identifies the complete physical answer stream.
-/

namespace bezout.History
noncomputable section
open scoped BigOperators
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Recenter an arbitrary actual oracle at a fixed point, without changing answers. -/
def translatedOracle (oracle : Fin N → E → E) (center : E) : Fin N → E → E :=
  fun s error => oracle s (error+center)

/-- Absolute-point and error-coordinate executions return exactly the same answers. -/
theorem oracleAnswers_translate (h : bezout.History N) (initial center : E)
    (oracle : Fin N → E → E) :
    h.oracleAnswers (initial-center) (translatedOracle oracle center) =
      h.oracleAnswers initial oracle := by
  symm
  apply h.oracleAnswers_unique
  intro s
  rw [h.oracleAnswers_eq]
  unfold translatedOracle oracleQuery
  congr 1
  abel

/-- The complete physical query stream commutes with translation to errors. -/
theorem oracleQuery_translate (h : bezout.History N) (initial center : E)
    (oracle : Fin N → E → E) (s : Fin N) :
    h.oracleQuery initial oracle s - center =
      h.oracleQuery (initial-center) (translatedOracle oracle center) s := by
  unfold oracleQuery
  rw [h.oracleAnswers_translate]
  abel

/-- The physical terminal error is exactly the output of the recentered execution. -/
theorem oracleOutput_translate (h : bezout.History N) (initial center : E)
    (oracle : Fin N → E → E) :
    h.oracleOutput initial oracle - center =
      h.oracleOutput (initial-center) (translatedOracle oracle center) := by
  unfold oracleOutput
  rw [h.oracleAnswers_translate]
  abel

/-- An actual affine quadratic oracle has exactly the established linear-error
execution, sample by sample for every physical error stream. -/
theorem affineOracle_output (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial center : E) (noise : Fin N → E) :
    h.oracleOutput initial (fun s y => H (y-center)+noise s) - center =
      (h.run H (initial-center) noise).output := by
  rw [h.oracleOutput_translate]
  have he : translatedOracle (fun s y => H (y-center)+noise s) center =
      fun s y => H y+noise s := by
    funext s y
    simp [translatedOracle]
  rw [he, h.oracleOutput_linear]

end
end bezout.History
