import krylov.LinearAlgebra.Schur
import krylov.LinearAlgebra.NormOrder
import Mathlib.Tactic.Module

/-!
Article: main_krylov, apA:galerkin(f), eq:block-completion.
Use: characterize the entire spectral-norm completion fibre, including singular
boundary blocks and the necessary cross-block range conditions.
Source: Albert69; reuse the proved generalized Schur criterion and spectral norm test.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped Matrix MatrixOrder
variable {n p : ℕ}

/-- Negating a rectangular cross block preserves its actual column range.
Use: the two shifted Schur tests have the same range condition on X.
Article: main_krylov, apA:galerkin(f).
Proof: the associated linear map is its negative, whose range is unchanged. -/
theorem range_neg_matrix (X : Matrix (Fin n) (Fin p) ℝ) :
    LinearMap.range (-X).mulVecLin = LinearMap.range X.mulVecLin := by
  have he : (-X).mulVecLin = -X.mulVecLin := by ext v i; simp
  rw [he, LinearMap.range_neg]

/-- The complete block norm ball is exactly the two pseudoinverse bounds and
both cross-block range conditions, including singular endpoints.
Use: the actual completion criterion, rather than just a sufficient invertible-block test.
Article: main_krylov, apA:galerkin(f), eq:block-completion.
Proof: rewrite the two shifted positive forms as block matrices and apply the
generalized Schur criterion to each; the two negative cross signs cancel. -/
theorem block_completion_iff (Y : Matrix (Fin p) (Fin p) ℝ) (hY : Y.IsSymm)
    (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
    (X : Matrix (Fin n) (Fin p) ℝ) {ω : ℝ} (hω : 0 ≤ ω)
    (hn : chebyshev1.opNorm K ≤ ω) :
    let Aplus := ω • (1 : Matrix (Fin n) (Fin n) ℝ) + K
    let Aminus := ω • (1 : Matrix (Fin n) (Fin n) ℝ) - K
    let hp := ((spectral_norm_iff_shifted_posSemidef K (Matrix.isHermitian_iff_isSymm.mpr hK) hω).mp hn).2
    let hm := ((spectral_norm_iff_shifted_posSemidef K (Matrix.isHermitian_iff_isSymm.mpr hK) hω).mp hn).1
    chebyshev1.opNorm (fromBlocks Y Xᵀ X K) ≤ ω ↔
      (LinearMap.range X.mulVecLin ≤ LinearMap.range Aplus.mulVecLin) ∧
      (LinearMap.range X.mulVecLin ≤ LinearMap.range Aminus.mulVecLin) ∧
      -ω • (1 : Matrix (Fin p) (Fin p) ℝ) + Xᵀ * pseudoinverse Aplus hp.1 * X ≤ Y ∧
      Y ≤ ω • (1 : Matrix (Fin p) (Fin p) ℝ) - Xᵀ * pseudoinverse Aminus hm.1 * X := by
  dsimp only
  have hs := (spectral_norm_iff_shifted_posSemidef K (Matrix.isHermitian_iff_isSymm.mpr hK) hω).mp hn
  have hb : (fromBlocks Y Xᵀ X K).IsHermitian :=
    Matrix.IsHermitian.fromBlocks (Matrix.isHermitian_iff_isSymm.mpr hY) (by simp) (Matrix.isHermitian_iff_isSymm.mpr hK)
  have hminus : ω • (1 : Matrix (Fin p ⊕ Fin n) (Fin p ⊕ Fin n) ℝ) -
      fromBlocks Y Xᵀ X K = fromBlocks (ω • 1 - Y) (-X)ᵀ (-X) (ω • 1 - K) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  have hplus : ω • (1 : Matrix (Fin p ⊕ Fin n) (Fin p ⊕ Fin n) ℝ) +
      fromBlocks Y Xᵀ X K = fromBlocks (ω • 1 + Y) Xᵀ X (ω • 1 + K) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  -- Singular cross-block compatibility is proved by the two full Schur equivalences.
  rw [spectral_norm_iff_shifted_posSemidef _ hb hω, hminus, hplus,
    generalized_schur_iff _ _ hs.1 (-X), generalized_schur_iff _ _ hs.2 X,
    range_neg_matrix]
  simp only [transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have hlo : ∀ Z : Matrix (Fin p) (Fin p) ℝ,
      (ω • 1 + Y - Z).PosSemidef ↔ -ω • 1 + Z ≤ Y := by
    intro Z
    rw [Matrix.le_iff]
    simp only [neg_smul]
    abel_nf
  have hhi : ∀ Z : Matrix (Fin p) (Fin p) ℝ,
      (ω • 1 - Y - Z).PosSemidef ↔ Y ≤ ω • 1 - Z := by
    intro Z
    rw [Matrix.le_iff]
    abel_nf
  rw [hhi, hlo]
  tauto

/-- A strict symmetric spectral ball has positive definite shifted endpoint blocks.
Use: ordinary inverses in the hidden scalar-entry interval have no zero denominators.
Article: main_krylov, apA:galerkin(f), ‖K‖<ω.
Proof: split each shift into a positive multiple of I plus its semidefinite norm-bound shift. -/
theorem strict_shifted_posDef (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
    {ω : ℝ} (hn : chebyshev1.opNorm K < ω) :
    (ω • (1 : Matrix (Fin n) (Fin n) ℝ) - K).PosDef ∧
      (ω • (1 : Matrix (Fin n) (Fin n) ℝ) + K).PosDef := by
  -- Add the strictly positive remaining scalar gap to each semidefinite endpoint shift.
  let r := chebyshev1.opNorm K
  have hs := (spectral_norm_iff_shifted_posSemidef K (Matrix.isHermitian_iff_isSymm.mpr hK)
    (chebyshev1.opNorm_nonneg K)).mp le_rfl
  have hp : ((ω - r) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (sub_pos.mpr hn)
  have hm := hp.add_posSemidef hs.1
  have hl := hp.add_posSemidef hs.2
  have he₁ : (ω - r) • (1 : Matrix (Fin n) (Fin n) ℝ) + (r • 1 - K) = ω • 1 - K := by module
  have he₂ : (ω - r) • (1 : Matrix (Fin n) (Fin n) ℝ) + (r • 1 + K) = ω • 1 + K := by module
  exact ⟨he₁ ▸ hm, he₂ ▸ hl⟩

/-- In the strict norm ball the full completion criterion uses the ordinary endpoint inverses.
Use: no range condition survives once both shifted endpoint blocks are actually positive definite.
Article: main_krylov, apA:galerkin(f), strict Schur bounds.
Proof: both endpoint operators are surjective by their proved positive determinants;
their actual pseudoinverses coincide with the ordinary inverses. -/
theorem strict_block_completion_iff (Y : Matrix (Fin p) (Fin p) ℝ) (hY : Y.IsSymm)
    (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
    (X : Matrix (Fin n) (Fin p) ℝ) {ω : ℝ} (hn : chebyshev1.opNorm K < ω) :
    chebyshev1.opNorm (fromBlocks Y Xᵀ X K) ≤ ω ↔
      -ω • (1 : Matrix (Fin p) (Fin p) ℝ) + Xᵀ * (ω • 1 + K)⁻¹ * X ≤ Y ∧
      Y ≤ ω • (1 : Matrix (Fin p) (Fin p) ℝ) - Xᵀ * (ω • 1 - K)⁻¹ * X := by
  have hω : 0 ≤ ω := (chebyshev1.opNorm_nonneg K).trans hn.le
  have hs := strict_shifted_posDef K hK hn
  have hr : ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef →
      LinearMap.range X.mulVecLin ≤ LinearMap.range A.mulVecLin := by
    intro A hA z _
    refine ⟨A⁻¹ *ᵥ z, ?_⟩
    exact by change A *ᵥ (A⁻¹ *ᵥ z) = z; rw [mulVec_mulVec,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec]
  -- Positive definiteness discharges the singular compatibility conditions rather than hiding them.
  have h := block_completion_iff Y hY K hK X hω hn.le
  dsimp only at h
  rw [pseudoinverse_eq_inv _ _ (isUnit_iff_ne_zero.mpr hs.1.det_pos.ne'),
    pseudoinverse_eq_inv _ _ (isUnit_iff_ne_zero.mpr hs.2.det_pos.ne')] at h
  simpa only [hr _ hs.1, hr _ hs.2, true_and] using h

end
end krylov.LinearAlgebra
