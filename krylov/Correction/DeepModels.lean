import krylov.Correction.DeepAuxiliary
import krylov.Correction.DeepUnbounded

/-!
Article: main_krylov, prop:deep, genuine source model positivity.
Use: Prove positive definiteness of every original preterminal correction
model and the last model on the positive-determinant side, and recover the
printed genuine squared Hilbert--Schmidt defect bound on the whole interval.
Source: the completely checked original source minors and proved Sylvester
criterion; original exact observed-pair squared-defect identity.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate krylov.Methods krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- Every genuine original preterminal latest-probe correction model is positive definite throughout the true source interval.
Use: Complete the original printed model and defect certificate before taking the actual RFC singular limit.
Article: main_krylov, prop:deep, positive original correction models.
Proof: Apply the proved genuine leading-principal-determinant criterion to the completely checked original source minors.
-/
theorem deep_preterminal_models_posDef {s : ℝ}
    (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) (k : Fin 3) :
    (matrixValue (sourceModel k.val) (sourceData k.val s)).PosDef := by
  -- Use the true full preterminal determinant and checked first principal minor; the three-dimensional case uses its independently decoded second minor.
  have hd := deep_preterminal_det_positive hs k
  rw [termDet_value] at hd
  have h₁ := deep_leading_one_positive hs k.castSucc
  apply posDef_of_leading_determinants _ (sourceModel_hermitian _ _)
  intro m hm hmk
  fin_cases k <;> dsimp only at hmk
  · have he : m=1 := by omega
    subst m
    exact h₁
  · have he : m=1 ∨ m=2 := by omega
    rcases he with he | he
    · subst m; exact h₁
    · subst m; rw [leadingBlock_full]; exact hd
  · have he : m=1 ∨ m=2 ∨ m=3 := by omega
    rcases he with he | he | he
    · subst m; exact h₁
    · subst m
      have hp := deep_penultimate_leading_positive hs
      rw [sourcePenultimateLeading,termDet_value] at hp
      exact hp
    · subst m; rw [leadingBlock_full]; exact hd

/-- The genuine original terminal latest-probe correction model is positive definite at every positive-determinant member of the true source interval.
Use: Complete the original printed model and defect certificate before taking the actual RFC singular limit.
Article: main_krylov, prop:deep, positive original correction models.
Proof: Apply the proved genuine leading-principal-determinant criterion to the completely checked original source minors.
-/
theorem deep_final_model_posDef {s : ℝ}
    (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) (hd : 0<deepDeterminant s) :
    (matrixValue (sourceModel 3) (sourceData 3 s)).PosDef := by
  -- The first three genuine leading determinants stay positive on the whole interval, so the true whole determinant decides the final positive side.
  rw [deepDeterminant,termDet_value] at hd
  apply posDef_of_leading_determinants _ (sourceModel_hermitian _ _)
  intro m hm hmk
  have he : m=1 ∨ m=2 ∨ m=3 ∨ m=4 := by omega
  rcases he with he | he | he | he
  · subst m
    have hp := deep_leading_positive hs ⟨0,by decide⟩
    rw [sourceLeading,termDet_value] at hp
    exact hp
  · subst m
    have hp := deep_leading_positive hs ⟨1,by decide⟩
    rw [sourceLeading,termDet_value] at hp
    exact hp
  · subst m
    have hp := deep_leading_positive hs ⟨2,by decide⟩
    rw [sourceLeading,termDet_value] at hp
    exact hp
  · subst m
    rw [leadingBlock_full]
    exact hd

/-- Every genuine original augmented observed-pair squared Hilbert--Schmidt defect satisfies the printed strict one-millionth bound on the whole interval.
Use: Complete the original printed model and defect certificate before taking the actual RFC singular limit.
Article: main_krylov, prop:deep, positive original correction models.
Proof: Apply the proved genuine leading-principal-determinant criterion to the completely checked original source minors.
-/
theorem deep_augmented_defect_hsSq {s : ℝ}
    (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) (k : Fin 4) :
    chebyshev1.hsSq (pairDefect
      (fun i => euclideanValue (sourceAugSteps k.val i) (sourceData k.val s))
      (fun i => euclideanValue (sourceAugImages k.val i) (sourceData k.val s)))<(1 : ℝ)/(10^6) := by
  rw [pairDefect_hsSq]
  · simpa only [termDefectSquare_value] using deep_aug_defect_small hs k
  · intro i
    have hh := (deepEnclosure 0 k).enclosed deepScale_pos (deep_all_enclosed 0 hs k) (sourceEnergyIndex k i)
    rw [sourceOutputs_energy,termDot_inner] at hh
    exact Bounds.mem_pos deepScale_pos hh (deep_energy_checked 0 k i)

end
end krylov.Correction.Certificate
