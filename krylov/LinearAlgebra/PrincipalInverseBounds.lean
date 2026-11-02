import krylov.LinearAlgebra.InverseSpectralOrder
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine Schur spectral enclosure.
Use: obtain actual Schur eigenvalue bounds from the proved true principal inverse block identity.
Source: positive inverse spectral coordinate tests, principal compression positivity and genuine reciprocal-order equivalence.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
variable {n p : ℕ}

/-- A genuine positive matrix whose inverse is an actual principal block inherits the original positive spectral interval.
Use: A genuine positive matrix whose inverse is an actual principal block inherits the original positive spectral interval.
Article: main_krylov, prop:phi(a), genuine Schur spectral enclosure.
Proof: Compress both actual inverse positivity shifts, use the true principal inverse identity and invert the genuine positive eigenvalue inequalities. -/
theorem principal_inverse_spectral_interval (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.PosDef)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosDef) (f : Fin p → Fin n)
    (hf : Function.Injective f) (he : T⁻¹.submatrix f f=S⁻¹) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hlo : ∀ i,a≤hT.1.eigenvalues i)
    (hhi : ∀ i,hT.1.eigenvalues i≤b) :
    ∀ i,a≤hS.1.eigenvalues i ∧ hS.1.eigenvalues i≤b := by
  -- Invert the genuine spectral interval before taking the actual principal block.
  have hlow : (T⁻¹-b⁻¹ • 1).PosSemidef := (inverse_lower_shift_iff T hT b⁻¹).mpr fun i =>
    (inv_le_inv₀ hb (hT.eigenvalues_pos i)).mpr (hhi i)
  have hupp : (a⁻¹ • 1-T⁻¹).PosSemidef := (inverse_upper_shift_iff T hT a⁻¹).mpr fun i =>
    (inv_le_inv₀ (hT.eigenvalues_pos i) ha).mpr (hlo i)
  have hsub (c : ℝ) : (c • (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix f f=c • 1 := by
    ext i j
    simp [Matrix.one_apply,hf.eq_iff]
  -- Actual principal compression preserves both true inverse shifted positivity tests.
  have hl : (S⁻¹-b⁻¹ • 1).PosSemidef := by
    have h := hlow.submatrix f
    change ((T⁻¹).submatrix f f-(b⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix f f).PosSemidef at h
    rwa [he,hsub] at h
  have hu : (a⁻¹ • 1-S⁻¹).PosSemidef := by
    have h := hupp.submatrix f
    change ((a⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix f f-(T⁻¹).submatrix f f).PosSemidef at h
    rwa [he,hsub] at h
  -- Restore the original orientation using only genuine positive eigenvalue denominators.
  intro i
  exact ⟨(inv_le_inv₀ (hS.eigenvalues_pos i) ha).mp ((inverse_upper_shift_iff S hS a⁻¹).mp hu i),
    (inv_le_inv₀ hb (hS.eigenvalues_pos i)).mp ((inverse_lower_shift_iff S hS b⁻¹).mp hl i)⟩
end
end krylov.LinearAlgebra
