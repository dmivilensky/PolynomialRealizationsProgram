import krylov.OneGradient.PhysicalFibre
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(a), physical positive Jacobi coordinates.
Use: identify the original physical completion with a genuine orthogonal
coordinate change whose only free Jacobi entry is its last diagonal.
Source: the already constructed positive Lanczos polynomial frame and its
proved physical multiplication-matrix compression (Meurant06, GolubMeurant10).
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {n : ℕ}

/-- The actual full positively oriented Lanczos family, indexed by the original
physical dimension rather than an independently selected Jacobi chain.
Use: express square original-coordinate matrices without losing the actual
constructed gradient spectral measure.
Article: main_krylov, s5:fibre(a).
Proof: the genuine full-atom cardinality reindexes the existing physical vectors. -/
def physicalLanczosFrame
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (i : Fin (n+1)) :
    EuclideanSpace ℝ (Fin (n+1)) :=
  lanczosVector A hA g hg ⟨i.val,by rw [hc];exact i.isLt⟩

/-- The actual physical column matrix of the source's positive Lanczos frame.
Use: the Jacobi compression and completion conjugation use the original matrix Z.
Article: main_krylov, s5:fibre(a), Z. -/
def physicalLanczosColumns
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => physicalLanczosFrame A hA g hg hc j i

/-- The actual original-coordinate Lanczos columns are orthogonal.
Use: their transpose is the real inverse and no abstract frame assumption is required.
Article: main_krylov, s5:fibre(a).
Proof: the previously proved genuine Lanczos orthonormality applies entrywise
to the actual full-atom reindexing. -/
theorem physical_lanczos_orthogonal
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    (physicalLanczosColumns A hA g hg hc)ᵀ*physicalLanczosColumns A hA g hg hc=1 := by
  ext i j
  have ho := (orthonormal_iff_ite.mp (lanczosVector_orthonormal A hA g hg))
    ⟨i.val,by rw [hc];exact i.isLt⟩ ⟨j.val,by rw [hc];exact j.isLt⟩
  simpa only [physicalLanczosColumns,physicalLanczosFrame,Matrix.mul_apply,Matrix.transpose_apply,
    PiLp.inner_apply,Real.inner_apply,Matrix.one_apply,Fin.mk.injEq,Fin.val_inj] using ho

/-- Every physical matrix compresses in the actual Lanczos frame by the genuine
physical inner products of its original-coordinate column vectors.
Use: transfer inverse and rank-one identities to the same actual Jacobi coordinates.
Article: main_krylov, s5:fibre(a).
Proof: expand the two finite matrix products and the true Euclidean matrix action. -/
theorem physical_lanczos_compression
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (C : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i j : Fin (n+1)) :
    ((physicalLanczosColumns A hA g hg hc)ᵀ*C*physicalLanczosColumns A hA g hg hc) i j=
      inner ℝ (physicalLanczosFrame A hA g hg hc i)
        (cgOperator C (physicalLanczosFrame A hA g hg hc j)) := by
  rw [Matrix.mul_assoc]
  simp only [physicalLanczosColumns,Matrix.mul_apply,Matrix.transpose_apply,
    cgOperator,Matrix.inner_toEuclideanCLM,dotProduct,mulVec]

/-- The original physical Lanczos compression is exactly the actual gradient
measure's reconstructed positive Jacobi matrix under the full-atom reindexing.
Use: tridiagonality, positive couplings and spectral quadrature come from the
existing measure construction, not a chosen model with the same moments.
Article: main_krylov, s5:fibre(a).
Proof: the genuine physical compression theorem identifies every actual entry. -/
theorem physical_lanczos_jacobi
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (i j : Fin (n+1)) :
    ((physicalLanczosColumns A hA g hg hc)ᵀ*A*physicalLanczosColumns A hA g hg hc) i j=
      (gradientSpectralData A hA g hg).reconstructed.matrix
        ⟨i.val,by rw [hc];exact i.isLt⟩ ⟨j.val,by rw [hc];exact j.isLt⟩ := by
  rw [physical_lanczos_compression]
  exact lanczosVector_compression A hA g hg _ _

/-- The actual physical fibre changes precisely the last diagonal entry of
its original positive Jacobi compression, as asserted by the source.
Use: the physical rank-one and the literal J(b) information fibres are the same.
Article: main_krylov, s5:fibre(a), ZᵀA_b Z=J(b).
Proof: compress the genuine rank-one operator and use the actual orthonormal
Lanczos pairings to annihilate every entry except the last-last one. -/
theorem physical_lanczos_completion
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) (i j : Fin (n+1)) :
    ((physicalLanczosColumns A hA g hg hc)ᵀ*lanczosCompletion A hA g hg hc b*
      physicalLanczosColumns A hA g hg hc) i j=
      if i=Fin.last n ∧ j=Fin.last n then b else
        ((physicalLanczosColumns A hA g hg hc)ᵀ*A*physicalLanczosColumns A hA g hg hc) i j := by
  rw [physical_lanczos_compression,physical_lanczos_compression,lanczos_completion_operator]
  simp only [_root_.add_apply,_root_.smul_apply,InnerProductSpace.rankOne_apply,
    inner_add_right,real_inner_smul_right]
  have hpair (k : Fin (n+1)) :
      inner ℝ (lastLanczosVector A hA g hg hc) (physicalLanczosFrame A hA g hg hc k)=
        if k=Fin.last n then 1 else 0 := by
    have he := (orthonormal_iff_ite.mp (lanczosVector_orthonormal A hA g hg))
      ⟨n,by rw [hc];omega⟩ ⟨k.val,by rw [hc];exact k.isLt⟩
    change inner ℝ (lastLanczosVector A hA g hg hc) (physicalLanczosFrame A hA g hg hc k)=_
    simpa only [lastLanczosVector,physicalLanczosFrame,Fin.mk.injEq,Fin.ext_iff,Fin.val_last,eq_comm] using he
  rw [real_inner_comm (lastLanczosVector A hA g hg hc) (physicalLanczosFrame A hA g hg hc i),hpair,hpair]
  by_cases hi : i=Fin.last n <;> by_cases hj : j=Fin.last n
  · subst i
    subst j
    simp only [ite_true,mul_one,and_self]
    change lastJacobiPivot A hA g hg hc+(b-lastJacobiPivot A hA g hg hc)=b
    ring
  · simp [hi,hj]
  · simp [hi,hj]
  · simp [hi,hj]

end
end krylov.OneGradient
