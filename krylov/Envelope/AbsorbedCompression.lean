import krylov.Envelope.CanonicalAbsorption

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu and thm:select, genuine budget-preserving absorbed scenarios.
Use: construct the actual canonical absorbed increments by the true
complementary explored-flag projectors and derive genuine absorption,
symmetry and preservation of each actual spectral perturbation budget.
Source: real finite orthogonal projections, actual matrix/operator
identification and standard symmetric compression and operator norm bounds.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Secant Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine canonical absorbed scenario formed by actual complementary explored-flag compression.
Use: The genuine canonical absorbed scenario formed by actual complementary explored-flag compression.
Article: main_krylov, apB:lem:mu and thm:select, genuine budget-preserving absorbed scenarios.
Proof: Compress each real increment on both sides by its true complementary canonical CG flag projector and recover the genuine finite matrix. -/
def absorbedIncrements (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.symm
    ((exploredFlag base g (l+1))ᗮ.starProjection ∘L cgOperator (E l) ∘L
      (exploredFlag base g (l+1))ᗮ.starProjection)

/-- The actual matrix absorbed increment has exactly its genuine complementary-projector operator action.
Use: The actual matrix absorbed increment has exactly its genuine complementary-projector operator action.
Article: main_krylov, apB:lem:mu and thm:select, genuine budget-preserving absorbed scenarios.
Proof: Cancel the true finite matrix/operator equivalence. -/
theorem absorbedIncrements_operator (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    cgOperator (absorbedIncrements base g E l)=
      (exploredFlag base g (l+1))ᗮ.starProjection ∘L cgOperator (E l) ∘L
        (exploredFlag base g (l+1))ᗮ.starProjection :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.apply_symm_apply _

/-- Every actually compressed source scenario satisfies the genuine absorbed-increment property on the true canonical flags.
Use: Every actually compressed source scenario satisfies the genuine absorbed-increment property on the true canonical flags.
Article: main_krylov, apB:lem:mu and thm:select, genuine budget-preserving absorbed scenarios.
Proof: The real complementary orthogonal projector kills every actual old-flag vector before the genuine increment action. -/
theorem absorbedIncrements_absorbed (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    AbsorbedIncrements base g (absorbedIncrements base g E) N := by
  -- The genuine right complementary projector annihilates each actual old-flag vector.
  intro l _ v hv
  rw [absorbedIncrements_operator]
  change (exploredFlag base g (l+1))ᗮ.starProjection
    (cgOperator (E l) ((exploredFlag base g (l+1))ᗮ.starProjection v))=0
  have hz : (exploredFlag base g (l+1))ᗮ.starProjection v=0 :=
    (exploredFlag base g (l+1)).starProjection_orthogonal_apply_eq_zero hv
  rw [hz,map_zero,map_zero]

/-- Actual symmetric source increments remain genuinely symmetric after true complementary explored-flag compression.
Use: Actual symmetric source increments remain genuinely symmetric after true complementary explored-flag compression.
Article: main_krylov, apB:lem:mu and thm:select, genuine budget-preserving absorbed scenarios.
Proof: Move the real symmetric projector across the actual inner product on both sides and use genuine middle-increment symmetry. -/
theorem absorbedIncrements_symm (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ) (hE : (E l).IsSymm) :
    (absorbedIncrements base g E l).IsSymm := by
  -- Genuine symmetry is checked through the actual physical operator and true orthogonal projector pairings.
  apply Matrix.isHermitian_iff_isSymm.mp
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  change (cgOperator (absorbedIncrements base g E l)).toLinearMap.IsSymmetric
  rw [absorbedIncrements_operator]
  let P := (exploredFlag base g (l+1))ᗮ
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hE)
  intro u v
  change inner ℝ (P.starProjection (cgOperator (E l) (P.starProjection u))) v=
    inner ℝ u (P.starProjection (cgOperator (E l) (P.starProjection v)))
  rw [P.inner_starProjection_left_eq_right,← P.inner_starProjection_left_eq_right u]
  exact hs (P.starProjection u) (P.starProjection v)

/-- Actual absorbed compression preserves every genuine spectral operator-norm budget.
Use: Actual absorbed compression preserves every genuine spectral operator-norm budget.
Article: main_krylov, apB:lem:mu and thm:select, genuine budget-preserving absorbed scenarios.
Proof: Each true complementary orthogonal projector has genuine operator norm at most one; apply actual composition norm bounds and true spectral matrix/operator norm equality. -/
theorem absorbedIncrements_norm_le (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    ‖absorbedIncrements base g E l‖≤‖E l‖ := by
  -- Use actual Euclidean operator norms for both genuine complementary compression factors.
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  change ‖cgOperator (absorbedIncrements base g E l)‖≤‖E l‖
  rw [absorbedIncrements_operator]
  let P := (exploredFlag base g (l+1))ᗮ.starProjection
  have hp : ‖P‖≤1 := (exploredFlag base g (l+1))ᗮ.starProjection_norm_le
  have hn := ContinuousLinearMap.opNorm_comp_le (P ∘L cgOperator (E l)) P
  have hn' := ContinuousLinearMap.opNorm_comp_le P (cgOperator (E l))
  have h1 : ‖P ∘L cgOperator (E l)‖≤‖cgOperator (E l)‖ := by
    exact hn'.trans (by nlinarith [norm_nonneg (cgOperator (E l))])
  exact hn.trans ((mul_le_mul h1 hp (norm_nonneg _) (norm_nonneg _)).trans_eq (by
    rw [mul_one]
    exact Matrix.l2_opNorm_toEuclideanCLM _))
end
end krylov.Envelope
