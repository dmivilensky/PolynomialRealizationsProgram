import krylov.XR.RadauPrimitive

/-!
Article: main_krylov, apG:radau-adequate, actual Schur inverse domains.
Use: derive both strict old shifted pencils and genuinely new physical
direction from the primitive augmented gain. Source: positive principal
restrictions and injectivity of the actual physical synthesis matrix.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Convergence krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- Positive actual augmented gain puts the new direction strictly
outside the stored span. Article: main_krylov, apG:radau-adequate. -/
theorem radau_new_direction (s : Fin p → EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (gamma : ℝ) (hg : 0<gamma)
    (hgain : ∀ c : Fin (p+1) → ℝ,
      gamma*‖WithLp.toLp 2 c‖^2≤‖combine (Fin.snoc s d) c‖^2) :
    WithLp.ofLp d∉LinearMap.range (radauStepMatrix s).mulVecLin := by
  rintro ⟨c,hc⟩
  have hinj := radauStepMatrix_injective (Fin.snoc s d) gamma hg hgain
  let z : Fin (p+1) → ℝ := Fin.snoc c (-1)
  have hs : combine s c=d := by rw [←radauStepMatrix_combine]; exact congrArg (WithLp.toLp 2) hc
  have hz : combine (Fin.snoc s d) z=0 := by
    rw [combine_snoc_window]
    simp only [z,Fin.snoc_castSucc,Fin.snoc_last,hs,neg_smul,one_smul,add_neg_cancel]
  have hM : radauStepMatrix (Fin.snoc s d)*ᵥz=0 := by
    apply WithLp.toLp_injective 2
    rw [radauStepMatrix_combine,hz,WithLp.toLp_zero]
  have he := congrFun (hinj (hM.trans (Matrix.mulVec_zero _).symm)) (Fin.last p)
  norm_num [z] at he

/-- The old principal physical Gram is the same Gram computed directly
from the stored columns. Article: main_krylov, apG:radau-adequate. -/
theorem radau_gram_restrict (s : Fin p → EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) :
    ((radauStepMatrix (Fin.snoc s d))ᵀ*radauStepMatrix (Fin.snoc s d)).submatrix
      Fin.castSucc Fin.castSucc=(radauStepMatrix s)ᵀ*radauStepMatrix s := by
  ext i j
  simp only [submatrix_apply,Matrix.mul_apply,transpose_apply,radauStepMatrix,Fin.snoc_castSucc]

/-- The actual desired augmented positive pencils give both ordinary
old Schur inverse domains, including the empty old window.
Article: main_krylov, apG:radau-adequate. -/
theorem radau_pencil_restrict (s : Fin p → EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin p) (Fin p) ℝ) (c mu upper : ℝ)
    (hlo : (radauTarget T c-mu •
      ((radauStepMatrix (Fin.snoc s d))ᵀ*radauStepMatrix (Fin.snoc s d))).PosDef)
    (hhi : (upper • ((radauStepMatrix (Fin.snoc s d))ᵀ*radauStepMatrix (Fin.snoc s d))-
      radauTarget T c).PosDef) :
    (T-mu • ((radauStepMatrix s)ᵀ*radauStepMatrix s)).PosDef ∧
      (upper • ((radauStepMatrix s)ᵀ*radauStepMatrix s)-T).PosDef := by
  have hT : (radauTarget T c).submatrix Fin.castSucc Fin.castSucc=T := by
    ext i j
    simp only [submatrix_apply,radauTarget,Fin.lastCases_castSucc]
  have hl := hlo.submatrix (Fin.castSucc_injective p)
  have hh := hhi.submatrix (Fin.castSucc_injective p)
  change ((radauTarget T c).submatrix Fin.castSucc Fin.castSucc-mu •
    (((radauStepMatrix (Fin.snoc s d))ᵀ*radauStepMatrix (Fin.snoc s d)).submatrix
      Fin.castSucc Fin.castSucc)).PosDef at hl
  change (upper • (((radauStepMatrix (Fin.snoc s d))ᵀ*radauStepMatrix (Fin.snoc s d)).submatrix
    Fin.castSucc Fin.castSucc)-(radauTarget T c).submatrix Fin.castSucc Fin.castSucc).PosDef at hh
  rw [hT,radau_gram_restrict] at hl hh
  exact ⟨hl,hh⟩

end
end krylov.XR
