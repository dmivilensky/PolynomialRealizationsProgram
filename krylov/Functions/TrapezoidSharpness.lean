import krylov.Functions.TrapezoidLipschitz

/-!
Article: main_krylov, thm:Fexact, sharpness of the endpoint constant.
Use: certify the sharp 1/12 constant with an actual quartic and all its actual
successive derivatives, rather than a prescribed formal remainder.
Source: Appendix G, the quartic equality example for the Peano kernel.
-/

namespace krylov.Functions
noncomputable section
open Set

/-- The normalized quartic whose fourth derivative is identically one.
Article: main_krylov, thm:Fexact, the sharp endpoint example. -/
def endpointQuartic (t : ℝ) : ℝ := t ^ 4 / 24

/-- The actual first derivative of the sharp quartic example.
Article: main_krylov, thm:Fexact. -/
theorem endpointQuartic_hasDerivAt (t : ℝ) :
    HasDerivAt endpointQuartic (t ^ 3 / 6) t := by
  convert! ((hasDerivAt_id t).pow 4).div_const 24 using 1
  simp only [id_eq]
  ring

/-- The actual second derivative of the sharp quartic example.
Article: main_krylov, thm:Fexact. -/
theorem endpointQuartic_second (t : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 3 / 6) (t ^ 2 / 2) t := by
  convert! ((hasDerivAt_id t).pow 3).div_const 6 using 1
  simp only [id_eq]
  ring

/-- The actual third derivative of the sharp quartic example.
Article: main_krylov, thm:Fexact. -/
theorem endpointQuartic_third (t : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
  convert! ((hasDerivAt_id t).pow 2).div_const 2 using 1
  simp only [id_eq]
  ring

/-- The actual fourth derivative and Lipschitz third derivative of the same quartic.
Article: main_krylov, thm:Fexact. -/
theorem endpointQuartic_fourth :
    (∀ t : ℝ, HasDerivAt (fun t : ℝ => t) 1 t) ∧
      LipschitzOnWith 1 (fun t : ℝ => t) (Icc (0 : ℝ) 1) := by
  exact ⟨fun t => hasDerivAt_id t, LipschitzWith.id.lipschitzOnWith⟩

/-- The quartic attains the exact 1/12 endpoint diagonal remainder.
Article: main_krylov, thm:Fexact, sharpness at x=b and lambda=1/2. -/
theorem endpointQuartic_remainder_equality :
    |(1 : ℝ) ^ 3 / 6 - 0 ^ 3 / 6 -
      6 * trapezoidDefect endpointQuartic (fun t => t ^ 3 / 6) - 1 ^ 2 / 2| = 1 / 12 := by
  norm_num [trapezoidDefect, endpointQuartic]

/-- Every smaller nonnegative universal endpoint coefficient fails on the actual quartic.
Article: main_krylov, thm:Fexact, optimality of the constant 1/12. -/
theorem endpointQuartic_excludes_smaller_constant (C : ℝ) (hC : C < 1 / 12) :
    ¬ |(1 : ℝ) ^ 3 / 6 - 0 ^ 3 / 6 -
      6 * trapezoidDefect endpointQuartic (fun t => t ^ 3 / 6) - 1 ^ 2 / 2| ≤ C := by
  rw [endpointQuartic_remainder_equality]
  exact not_le.mpr hC

end
end krylov.Functions
