import krylov.Secant.MSS
import Mathlib.Tactic.Linarith

/-!
Article: main_krylov, thm:window and apG:mss, positive-metric rank-one geometry.
Use: normalize the actual oldest dual vector and prove its physical Loewner budget.
Source: Cauchy--Schwarz for a positive quadratic form, proved by completing its square.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped Matrix MatrixOrder
variable {n : ℕ}

/-- Cauchy--Schwarz for the actual positive-definite physical curvature form.
Use: the normalized oldest dual rank-one perturbation is bounded by its base.
Article: main_krylov, proof of thm:window, γhhᵀ ⪯ A.
Proof: evaluate the positive form at v−⟨u,Av⟩u/⟨u,Au⟩ and clear its positive pivot. -/
theorem positive_cauchy (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (u v : Fin n → ℝ) :
    (u ⬝ᵥ (A *ᵥ v))^2 ≤ (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) := by
  by_cases hu : u = 0
  · simp [hu]
  -- Complete the square at the unique scalar minimizer along u.
  have hd : 0 < u ⬝ᵥ (A *ᵥ u) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_pos hu
  have hs : v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
    simpa only [star_trivial] using hA.1.star_dotProduct_mulVec_comm v u
  let z := v - ((u ⬝ᵥ (A *ᵥ v)) / (u ⬝ᵥ (A *ᵥ u))) • u
  have hz : 0 ≤ z ⬝ᵥ (A *ᵥ z) := by
    simpa only [star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg z
  have he : (u ⬝ᵥ (A *ᵥ u)) * (z ⬝ᵥ (A *ᵥ z)) =
      (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) - (u ⬝ᵥ (A *ᵥ v))^2 := by
    simp only [z, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul,
      sub_dotProduct, smul_dotProduct, smul_eq_mul, hs]
    field_simp
    ring
  have hn := mul_nonneg hd.le hz
  rw [he] at hn
  linarith

/-- A normalized physical rank-one perturbation lies between zero and the base.
Use: the hidden rank-one scenarios obey all their signed Loewner budgets.
Article: main_krylov, proof of thm:window, 0 ⪯ γhhᵀ ⪯ A.
Proof: its positive rank-one form is bounded by the preceding metric Cauchy inequality. -/
theorem normalized_rankOne_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (u : Fin n → ℝ) (hu : u ≠ 0) :
    let d := u ⬝ᵥ (A *ᵥ u)
    let H := d⁻¹ • vecMulVec (A *ᵥ u) (A *ᵥ u)
    H.PosSemidef ∧ H ≤ A := by
  -- The positive pivot permits normalization; Cauchy--Schwarz controls the upper Loewner bound.
  have hd : 0 < u ⬝ᵥ (A *ᵥ u) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_pos hu
  have hH : ((u ⬝ᵥ (A *ᵥ u))⁻¹ • vecMulVec (A *ᵥ u) (A *ᵥ u)).PosSemidef := by
    have h := (Matrix.posSemidef_vecMulVec_self_star (A *ᵥ u)).smul (inv_nonneg.mpr hd.le)
    simpa only [star_trivial] using h
  refine ⟨hH, ?_⟩
  change (A - (u ⬝ᵥ (A *ᵥ u))⁻¹ • vecMulVec (A *ᵥ u) (A *ᵥ u)).PosSemidef
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hA.1.sub hH.1)
  intro v
  have hs : (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (A *ᵥ v) := by
    rw [dotProduct_comm (A *ᵥ u) v]
    simpa only [star_trivial] using hA.1.star_dotProduct_mulVec_comm v u
  have hc : (u ⬝ᵥ (A *ᵥ v))^2 / (u ⬝ᵥ (A *ᵥ u)) ≤ v ⬝ᵥ (A *ᵥ v) :=
    (div_le_iff₀ hd).mpr (by nlinarith [positive_cauchy A hA u v])
  have hsv : v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
    simpa only [star_trivial] using hA.1.star_dotProduct_mulVec_comm v u
  simp only [star_trivial, sub_mulVec, smul_mulVec, krylov.Secant.outer_mulVec,
    dotProduct_sub, dotProduct_smul, smul_smul, smul_eq_mul, hs, hsv]
  convert sub_nonneg.mpr hc using 1
  ring

end
end krylov.LinearAlgebra
