import krylov.Completion.WindowFrame
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, physical arbitrary-window completion.
Use: state the singular curvature interval on the original physical stored
matrix and actual new direction, deriving the augmented rank condition.
Source: Albert69 and the proved explicit physical spectral extension.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {n p : ℕ}

/-- The actual physical compression has exactly its measured Gram, conjugacy
and scalar curvature blocks.
Use: identify the constructed completion with all original window constraints.
Article: main_krylov, thm:radau.
Proof: multiply the actual partitioned frame; symmetry identifies the transpose
cross block, and the scalar block is the genuine directional quadratic form. -/
theorem curvature_frame_compression (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (curvatureFrame S d)ᵀ*A*curvatureFrame S d=
      fromBlocks (scalarCorner (d ⬝ᵥ (A*ᵥ d))) (crossColumn (Sᵀ*ᵥ (A*ᵥ d)))ᵀ
        (crossColumn (Sᵀ*ᵥ (A*ᵥ d))) (Sᵀ*A*S) := by
  rw [curvatureFrame,transpose_fromCols,fromRows_mul,fromRows_mul_fromCols,
    crossColumn_quadratic]
  have hc : Sᵀ*A*crossColumn d=crossColumn (Sᵀ*ᵥ (A*ᵥ d)) := by
    ext i j
    change ((Sᵀ*A)*ᵥ d) i=(Sᵀ*ᵥ (A*ᵥ d)) i
    rw [mulVec_mulVec]
  have ht : (crossColumn d)ᵀ*A*S=(Sᵀ*A*crossColumn d)ᵀ := by
    simp only [transpose_mul,transpose_transpose,hA.eq,Matrix.mul_assoc]
  rw [ht,hc]

/-- The augmented compression constraint is exactly the three original physical
window conditions, rather than a presumed coordinate representation.
Use: pass both directions of endpoint realization back to SᵀA'S, SᵀA'd and dᵀA'd.
Article: main_krylov, thm:radau.
Proof: read its three literal block entries; symmetry supplies the fourth block. -/
theorem curvature_frame_constraints (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (T : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) :
    (curvatureFrame S d)ᵀ*A*curvatureFrame S d=windowCurvatureForm T c ↔
      Sᵀ*A*S=T ∧ Sᵀ*ᵥ (A*ᵥ d)=0 ∧ d ⬝ᵥ (A*ᵥ d)=c := by
  rw [curvature_frame_compression S d A hA]
  constructor
  · intro he
    refine ⟨?_,?_,?_⟩
    · exact congrArg (fun M => M.submatrix Sum.inr Sum.inr) he
    · funext i
      exact congrArg (fun M => M (Sum.inr i) (Sum.inl 0)) he
    · exact congrArg (fun M => M (Sum.inl 0) (Sum.inl 0)) he
  · rintro ⟨hT,hc,hd⟩
    rw [hT,hc,hd]
    rfl

/-- The full singular Schur interval is necessary and sufficient for the
original physical arbitrary-window Gram and conjugacy constraints.
Use: every curvature between the printed unnormalized endpoints, including
both endpoints, is attained by a genuine symmetric matrix in the closed band.
Article: main_krylov, thm:radau, Gram-only completion.
Proof: derive the actual augmented positive Gram from independent S and d
outside its range, apply the constructed physical completion theorem, and
identify its exact physical compression constraints in both directions. -/
theorem window_curvature_completion_iff
    (S : Matrix (Fin n) (Fin p) ℝ) (hS : Function.Injective S.mulVec)
    (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L c : ℝ) (hmuL : mu≤L)
    (hlo : (T-mu • (Sᵀ*S)).PosSemidef) (hhi : (L • (Sᵀ*S)-T).PosSemidef) :
    (∃ A : Matrix (Fin n) (Fin n) ℝ,A.IsSymm ∧
      (A-mu • 1).PosSemidef ∧ (L • 1-A).PosSemidef ∧
        Sᵀ*A*S=T ∧ Sᵀ*ᵥ (A*ᵥ d)=0 ∧ d ⬝ᵥ (A*ᵥ d)=c) ↔
      (LinearMap.range ((-mu) • (Sᵀ*crossColumn d)).mulVecLin≤
        LinearMap.range (T-mu • (Sᵀ*S)).mulVecLin) ∧
      (LinearMap.range (L • (Sᵀ*crossColumn d)).mulVecLin≤
        LinearMap.range (L • (Sᵀ*S)-T).mulVecLin) ∧
      mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hlo.1*
        (Sᵀ*crossColumn d)) 0 0≤c ∧
      c≤L*(d ⬝ᵥ d)-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hhi.1*
        (Sᵀ*crossColumn d)) 0 0 := by
  have h := curvature_completion_iff (curvatureFrame S d) (curvature_frame_positive S hS d hd)
    (Sᵀ*S) T (Sᵀ*crossColumn d) (d ⬝ᵥ d) mu L c hmuL (curvature_frame_gram S d) hlo hhi
  rw [← h]
  constructor
  · rintro ⟨A,hA,hlo,hhi,hT,hcross,hcurv⟩
    exact ⟨A,hlo,hhi,(curvature_frame_constraints S d A hA T c).mpr ⟨hT,hcross,hcurv⟩⟩
  · rintro ⟨A,hlo,hhi,hcomp⟩
    have hmu : (mu • (1 : Matrix (Fin n) (Fin n) ℝ)).IsSymm := by
      simp only [Matrix.IsSymm,transpose_smul,transpose_one]
    have hA : A.IsSymm := by
      have hh := hlo.1.isSymm.add hmu
      simpa only [sub_add_cancel] using hh
    obtain ⟨hT,hcross,hcurv⟩ := (curvature_frame_constraints S d A hA T c).mp hcomp
    exact ⟨A,hA,hlo,hhi,hT,hcross,hcurv⟩

end
end krylov.Completion
