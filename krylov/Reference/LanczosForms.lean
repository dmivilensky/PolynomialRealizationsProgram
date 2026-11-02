import krylov.Reference.Lanczos
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual Lanczos spectral window.
Use: derive the genuine finite compression quadratic form and both shifted positivity bounds from the actual physical reference operator.
Source: true computed normalized CG residuals, their proved orthonormality and genuine finite Gram compression.
-/

namespace krylov.Reference.CG
noncomputable section
open Matrix
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual Lanczos matrix quadratic form equals the true physical operator form on its computed residual synthesis.
Use: The actual Lanczos matrix quadratic form equals the true physical operator form on its computed residual synthesis.
Article: main_krylov, prop:phi(a), actual Lanczos spectral window.
Proof: Expand the actual finite Gram entries and commute the genuine finite sums. -/
theorem lanczosMatrix_form (Q : E →L[ℝ] E) (g : E) (m : ℕ) (v : Fin m → ℝ) :
    star v ⬝ᵥ lanczosMatrix Q g m *ᵥ v=
      inner ℝ (∑ i : Fin m,v i • residualUnit Q g i.val)
        (Q (∑ i : Fin m,v i • residualUnit Q g i.val)) := by
  simp only [dotProduct,Pi.star_apply,star_trivial,Matrix.mulVec,lanczosMatrix,
    map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual normalized CG residual synthesis preserves the genuine finite coefficient energy.
Use: The actual normalized CG residual synthesis preserves the genuine finite coefficient energy.
Article: main_krylov, prop:phi(a), actual Lanczos spectral window.
Proof: Use the actual proved orthonormal residual family. -/
theorem lanczosResidualSynthesis_norm_sq (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,gradient Q g i≠0) (v : Fin m → ℝ) :
    ‖∑ i : Fin m,v i • residualUnit Q g i.val‖^2=∑ i : Fin m,(v i)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [(residualUnit_orthonormal Q hQ hpos g m hpre).inner_sum]
  simp [pow_two]

/-- A genuine physical lower quadratic bound gives actual lower shifted positivity of the true computed Lanczos matrix.
Use: A genuine physical lower quadratic bound gives actual lower shifted positivity of the true computed Lanczos matrix.
Article: main_krylov, prop:phi(a), actual Lanczos spectral window.
Proof: Evaluate the physical bound on the genuine residual synthesis and use its actual Gram and norm identities. -/
theorem lanczosMatrix_shift_posSemidef (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,gradient Q g i≠0) (a : ℝ)
    (hbound : ∀ v : E,a*‖v‖^2≤ inner ℝ v (Q v)) :
    (lanczosMatrix Q g m-a • 1).PosSemidef := by
  -- Test the true physical bound on the actual orthonormal residual synthesis.
  have hT := lanczosMatrix_posDef Q hQ hpos g m hpre
  have hsym : (lanczosMatrix Q g m-a • 1).IsHermitian := hT.1.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint a from rfl))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsym
  intro v
  have h := hbound (∑ i : Fin m,v i • residualUnit Q g i.val)
  have hn := lanczosResidualSynthesis_norm_sq Q hQ hpos g m hpre v
  rw [hn] at h
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_smul,
    lanczosMatrix_form]
  simpa only [dotProduct,Pi.star_apply,star_trivial,pow_two,sub_nonneg,smul_eq_mul] using h
/-- A genuine physical upper quadratic bound gives actual upper shifted positivity of the true computed Lanczos matrix.
Use: A genuine physical upper quadratic bound gives actual upper shifted positivity of the true computed Lanczos matrix.
Article: main_krylov, prop:phi(a), actual Lanczos spectral window.
Proof: Evaluate the physical bound on the genuine residual synthesis and use its actual Gram and norm identities. -/
theorem lanczosMatrix_upper_shift_posSemidef (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,gradient Q g i≠0) (b : ℝ)
    (hbound : ∀ v : E,inner ℝ v (Q v)≤b*‖v‖^2) :
    (b • 1-lanczosMatrix Q g m).PosSemidef := by
  have hT := lanczosMatrix_posDef Q hQ hpos g m hpre
  -- The true upper form uses the same actual residual Gram matrix and genuine synthesis energy.
  have hsym : (b • 1-lanczosMatrix Q g m).IsHermitian :=
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint b from rfl)).sub hT.1
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsym
  intro v
  have h := hbound (∑ i : Fin m,v i • residualUnit Q g i.val)
  rw [lanczosResidualSynthesis_norm_sq Q hQ hpos g m hpre v] at h
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_smul,
    lanczosMatrix_form]
  simpa only [dotProduct,Pi.star_apply,star_trivial,pow_two,sub_nonneg,smul_eq_mul] using h

end
end krylov.Reference.CG
