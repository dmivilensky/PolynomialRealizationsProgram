import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
Article: jacobi, Corollary C.6.
Exact original N-cubed energy normalizations for complex squares and
squared moduli. These identities retain the original matrix dimension
and distinguish the two genuine shifted energies.
Use: shiftedTargetSquare_energy_uniform transfers the proved genuine spectral diagonal energy to the actual original complex matrix inverse.
-/
namespace jacobi.Analysis
noncomputable section
open Real

/-- Squaring the original N-normalized complex diagonal and averaging
its N entries gives precisely the printed N-cubed complex energy.
Use: shiftedTargetSquare_energy_uniform transfers the proved genuine
spectral diagonal energy to the actual original complex matrix inverse.
Article: jacobi, Corollary C.6.
Proof: move the common squared denominator outside the actual finite
sum and combine the original scalar factors exactly. -/
theorem scaled_complex_square_sum (n:ℕ) (f:Fin (n+1)→ℂ) :
    (1/((n:ℝ)+1)) • (∑i:Fin (n+1),(f i/(((n:ℝ)+1:ℝ):ℂ))^2)=
      (∑i:Fin (n+1),(f i)^2)/((((n:ℝ)+1:ℝ):ℂ)^3) := by
  change ((1/((n:ℝ)+1):ℝ):ℂ)*(∑i:Fin (n+1),(f i/(((n:ℝ)+1:ℝ):ℂ))^2)=_
  simp_rw [div_pow]
  rw [← Finset.sum_div,Complex.ofReal_div,Complex.ofReal_one]
  field_simp

/-- The actual squared moduli have the same exact N-cubed physical
normalization, with the original positive real N retained.
Use: shiftedTargetNormSquare_energy_uniform transfers the second
proved genuine spectral energy to the actual complex matrix inverse.
Article: jacobi, Corollary C.6.
Proof: the actual denominator is a positive real number; its complex
norm is N, and the exact scalar square-sum cancellation applies. -/
theorem scaled_norm_square_sum (n:ℕ) (f:Fin (n+1)→ℂ) :
    (∑i:Fin (n+1),‖f i/(((n:ℝ)+1:ℝ):ℂ)‖^2)/((n:ℝ)+1)=
      (∑i:Fin (n+1),‖f i‖^2)/((n:ℝ)+1)^3 := by
  simp_rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : (0:ℝ)<(n:ℝ)+1),div_pow]
  rw [← Finset.sum_div]
  field_simp

end
end jacobi.Analysis
