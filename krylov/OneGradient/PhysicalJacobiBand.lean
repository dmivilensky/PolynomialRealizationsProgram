import krylov.OneGradient.JacobiPivot
import krylov.Completion.StrictJacobiBand
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), original physical spectral completion interval.
Use: transfer the actual leading inverse Schur endpoints to the original physical
last-Lanczos information fibre, including the two singular shifted endpoints.
Source: genuine physical orthogonal Lanczos compression, actual finite reindexing
and the proved closed positive-leading spectral Schur criterion.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.LinearAlgebra krylov.Completion
variable {n : ℕ}

/-- The actual original-coordinate Lanczos congruence preserves positive
semidefiniteness in both directions.
Use: endpoint spectral conditions on the real physical completion and its
actual Jacobi compression are exactly equivalent.
Article: main_krylov, s5:fibre(b).
Proof: the original physical frame's proved two-sided orthogonal inverse
transports each true nonnegative quadratic form back to its original coordinates. -/
theorem physical_lanczos_positive_iff
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (C : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    ((physicalLanczosColumns A hA g hg hc)ᵀ*C*physicalLanczosColumns A hA g hg hc).PosSemidef ↔
      C.PosSemidef := by
  let Z := physicalLanczosColumns A hA g hg hc
  have hZ : Z*Zᵀ=1 := mul_eq_one_comm.mp (physical_lanczos_orthogonal A hA g hg hc)
  constructor
  · intro h
    have hh := h.mul_mul_conjTranspose_same Z
    have he : Z*(Zᵀ*C*Z)*Zᵀ=C := by
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hZ,Matrix.one_mul,Matrix.mul_assoc,hZ,Matrix.mul_one]
    simp only [conjTranspose_eq_transpose_of_trivial] at hh
    change (Z*(Zᵀ*C*Z)*Zᵀ).PosSemidef at hh
    rwa [he] at hh
  · intro h
    simpa only [conjTranspose_eq_transpose_of_trivial] using h.conjTranspose_mul_mul_same Z

/-- Move the actual single unresolved last Jacobi site before its true leading
block; the physical completion becomes exactly the source scalar Schur matrix.
Use: the free diagonal and all known leading/coupling entries are computed
from the real physical information rather than assumed as a completion model.
Article: main_krylov, s5:fibre(b).
Proof: the genuine physical J(b) compression changes only the last diagonal;
its true symmetry identifies the transposed leading coupling row. -/
theorem physical_jacobi_last_first
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) :
    let Z := physicalLanczosColumns A hA g hg hc
    let J := physicalJacobi A hA g hg hc
    let e : (Fin 1⊕Fin n) ≃ Fin (n+1) := (Equiv.sumComm (Fin 1) (Fin n)).trans finSumFinEquiv
    (Zᵀ*lanczosCompletion A hA g hg hc b*Z).submatrix e e=
      fromBlocks (scalarCorner b) (crossColumn (lastCross J))ᵀ (crossColumn (lastCross J)) (lastLeading J) := by
  let Z := physicalLanczosColumns A hA g hg hc
  let J := physicalJacobi A hA g hg hc
  dsimp only
  ext i j
  cases i with
  | inl i =>
    fin_cases i
    cases j with
    | inl j =>
      fin_cases j
      change (Zᵀ*lanczosCompletion A hA g hg hc b*Z) (Fin.last n) (Fin.last n)=b
      rw [physical_lanczos_completion]
      simp
    | inr j =>
      change (Zᵀ*lanczosCompletion A hA g hg hc b*Z) (Fin.last n) (Fin.castSucc j)=J (Fin.castSucc j) (Fin.last n)
      rw [physical_lanczos_completion]
      simp only [Fin.castSucc_ne_last j,and_false,ite_false]
      exact congrFun (congrFun (physical_jacobi_positive A hA g hg hc).1.isSymm.eq (Fin.castSucc j)) (Fin.last n)
  | inr i =>
    cases j with
    | inl j =>
      fin_cases j
      change (Zᵀ*lanczosCompletion A hA g hg hc b*Z) (Fin.castSucc i) (Fin.last n)=J (Fin.castSucc i) (Fin.last n)
      rw [physical_lanczos_completion]
      simp only [Fin.castSucc_ne_last i,false_and,ite_false]
      rfl
    | inr j =>
      change (Zᵀ*lanczosCompletion A hA g hg hc b*Z) (Fin.castSucc i) (Fin.castSucc j)=J (Fin.castSucc i) (Fin.castSucc j)
      rw [physical_lanczos_completion]
      simp only [Fin.castSucc_ne_last i,false_and,ite_false]
      rfl

/-- The original physical information fibre lies in the closed spectral band
exactly on the two actual ordinary-inverse Schur endpoint inequalities.
Use: both real endpoint matrices are admitted whenever the resulting interval
is nonempty; neither whole shifted matrix is required to be invertible.
Article: main_krylov, s5:fibre(b).
Proof: the genuine orthogonal physical frame transfers both true spectral
forms. Actual finite last-site reindexing identifies the real scalar block;
the proved closed Schur theorem computes both endpoint inequalities. -/
theorem physical_fibre_spectral_iff
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (mu upper : ℝ)
    (hlo : (lastLeading (physicalJacobi A hA g hg hc)-mu • 1).PosDef)
    (hhi : (upper • 1-lastLeading (physicalJacobi A hA g hg hc)).PosDef) (b : ℝ) :
    let C := lanczosCompletion A hA g hg hc b
    let J := physicalJacobi A hA g hg hc
    let H := lastLeading J
    let x := lastCross J
    (C-mu • 1).PosSemidef ∧ (upper • 1-C).PosSemidef ↔
      mu+x ⬝ᵥ ((H-mu • 1)⁻¹*ᵥ x)≤b ∧ b≤upper-x ⬝ᵥ ((upper • 1-H)⁻¹*ᵥ x) := by
  let C := lanczosCompletion A hA g hg hc b
  let Z := physicalLanczosColumns A hA g hg hc
  let J := physicalJacobi A hA g hg hc
  let H := lastLeading J
  let x := lastCross J
  let e : (Fin 1⊕Fin n) ≃ Fin (n+1) := (Equiv.sumComm (Fin 1) (Fin n)).trans finSumFinEquiv
  let T := fromBlocks (scalarCorner b) (crossColumn x)ᵀ (crossColumn x) H
  have hZ : Zᵀ*Z=1 := physical_lanczos_orthogonal A hA g hg hc
  have hblock : (Zᵀ*C*Z).submatrix e e=T := physical_jacobi_last_first A hA g hg hc b
  have hl : (Zᵀ*(C-mu • 1)*Z).submatrix e e=T-mu • 1 := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
      hZ,Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,
      Matrix.submatrix_one_equiv,hblock]
  have hh : (Zᵀ*(upper • 1-C)*Z).submatrix e e=upper • 1-T := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
      hZ,Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,
      Matrix.submatrix_one_equiv,hblock]
  have hlo' : (C-mu • 1).PosSemidef ↔ (T-mu • 1).PosSemidef := by
    rw [← physical_lanczos_positive_iff A hA g hg hc,← Matrix.posSemidef_submatrix_equiv e,hl]
  have hhi' : (upper • 1-C).PosSemidef ↔ (upper • 1-T).PosSemidef := by
    rw [← physical_lanczos_positive_iff A hA g hg hc,← Matrix.posSemidef_submatrix_equiv e,hh]
  dsimp only
  rw [hlo',hhi']
  exact strict_scalar_band_iff H x b mu upper hlo hhi

end
end krylov.OneGradient
