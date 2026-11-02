import krylov.OneGradient.JacobiSpectralInterval
import krylov.Completion.SchurEndpoints
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), genuine endpoint spectral nodes.
Use: derive prescribed endpoint eigenvectors of the original physical
Gauss--Radau completions from actual shifted Schur determinants.
Source: actual orthogonal Lanczos determinant invariance, genuine physical
spectral shifts and the proved scalar Schur determinant/kernel theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.LinearAlgebra krylov.Completion
variable {n : ℕ}

/-- The genuine physical Lanczos change of coordinates preserves the actual determinant.
Use: singular shifted Jacobi endpoint pencils give singular original physical pencils.
Article: main_krylov, s5:fibre(b).
Proof: the actual orthogonal frame has determinant square one, so its two
coordinate-congruence determinant factors cancel exactly. -/
theorem physical_lanczos_determinant
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (C : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    ((physicalLanczosColumns A hA g hg hc)ᵀ*C*physicalLanczosColumns A hA g hg hc).det=C.det := by
  let Z := physicalLanczosColumns A hA g hg hc
  have he := congrArg Matrix.det (physical_lanczos_orthogonal A hA g hg hc)
  change (Zᵀ*Z).det=(1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ).det at he
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at he
  change (Zᵀ*C*Z).det=C.det
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  calc
    _ = (Z.det*Z.det)*C.det := by ring
    _ = C.det := by rw [he,one_mul]

/-- The true lower physical spectral pencil is exactly its scalar Schur pencil
in the original Lanczos coordinates with the last site placed first.
Use: endpoint determinant and feasibility arguments share the same actual pencil.
Article: main_krylov, s5:fibre(b).
Proof: the real orthogonal Gram cancels the shifted identity; the original
physical last-first compression and actual scalar-corner shift finish the identity. -/
theorem physical_fibre_lower_pencil
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b mu : ℝ) :
    let Z := physicalLanczosColumns A hA g hg hc
    let J := physicalJacobi A hA g hg hc
    let e : (Fin 1⊕Fin n) ≃ Fin (n+1) := (Equiv.sumComm (Fin 1) (Fin n)).trans finSumFinEquiv
    (Zᵀ*(lanczosCompletion A hA g hg hc b-mu • 1)*Z).submatrix e e=
      fromBlocks (scalarCorner (b-mu)) (crossColumn (lastCross J))ᵀ (crossColumn (lastCross J))
        (lastLeading J-mu • 1) := by
  have hZ := physical_lanczos_orthogonal A hA g hg hc
  dsimp only
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
    hZ,Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,
    Matrix.submatrix_one_equiv,physical_jacobi_last_first,scalar_corner_lower_shift]

/-- The actual upper physical spectral pencil has its genuine signed-cross
scalar Schur form in the same original Lanczos coordinates.
Use: the upper endpoint retains its actual prescribed spectral node.
Article: main_krylov, s5:fibre(b).
Proof: the true orthogonal Gram cancels the shifted identity, and the actual
upper scalar-corner shift negates the real cross column. -/
theorem physical_fibre_upper_pencil
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b upper : ℝ) :
    let Z := physicalLanczosColumns A hA g hg hc
    let J := physicalJacobi A hA g hg hc
    let e : (Fin 1⊕Fin n) ≃ Fin (n+1) := (Equiv.sumComm (Fin 1) (Fin n)).trans finSumFinEquiv
    (Zᵀ*(upper • 1-lanczosCompletion A hA g hg hc b)*Z).submatrix e e=
      fromBlocks (scalarCorner (upper-b)) (crossColumn (-lastCross J))ᵀ (crossColumn (-lastCross J))
        (upper • 1-lastLeading J) := by
  have hZ := physical_lanczos_orthogonal A hA g hg hc
  dsimp only
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
    hZ,Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,
    Matrix.submatrix_one_equiv,physical_jacobi_last_first,scalar_corner_upper_shift]

/-- The actual original physical lower spectral pencil has its literal last
Schur determinant factorization, with the true leading inverse on its proved domain.
Use: the lower endpoint's prescribed spectral node follows from its real determinant.
Article: main_krylov, s5:fibre(b).
Proof: transport the genuine physical determinant through the actual orthogonal
frame and finite reindexing, then apply the actual scalar Schur determinant. -/
theorem physical_fibre_lower_determinant
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b mu : ℝ)
    (hlo : (lastLeading (physicalJacobi A hA g hg hc)-mu • 1).PosDef) :
    let J := physicalJacobi A hA g hg hc
    let H := lastLeading J
    let x := lastCross J
    (lanczosCompletion A hA g hg hc b-mu • 1).det=
      (H-mu • 1).det*(b-mu-x ⬝ᵥ ((H-mu • 1)⁻¹*ᵥ x)) := by
  let e : (Fin 1⊕Fin n) ≃ Fin (n+1) := (Equiv.sumComm (Fin 1) (Fin n)).trans finSumFinEquiv
  rw [← physical_lanczos_determinant A hA g hg hc,← Matrix.det_submatrix_equiv_self e,
    physical_fibre_lower_pencil,strict_scalar_schur_det _ hlo]

/-- The actual upper physical spectral pencil has the corresponding literal
Schur determinant factorization, including its signed real cross column.
Use: the upper endpoint's prescribed node is derived for the original physical matrix.
Article: main_krylov, s5:fibre(b).
Proof: use the same genuine determinant transport and actual upper pencil;
negating both real cross factors leaves their inverse quadratic form unchanged. -/
theorem physical_fibre_upper_determinant
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b upper : ℝ)
    (hhi : (upper • 1-lastLeading (physicalJacobi A hA g hg hc)).PosDef) :
    let J := physicalJacobi A hA g hg hc
    let H := lastLeading J
    let x := lastCross J
    (upper • 1-lanczosCompletion A hA g hg hc b).det=
      (upper • 1-H).det*(upper-b-x ⬝ᵥ ((upper • 1-H)⁻¹*ᵥ x)) := by
  let e : (Fin 1⊕Fin n) ≃ Fin (n+1) := (Equiv.sumComm (Fin 1) (Fin n)).trans finSumFinEquiv
  rw [← physical_lanczos_determinant A hA g hg hc,← Matrix.det_submatrix_equiv_self e,
    physical_fibre_upper_pencil,strict_scalar_schur_det _ hhi]
  simp only [mulVec_neg,dotProduct_neg,neg_dotProduct,neg_neg]

/-- Both real Schur endpoint completions have their source-prescribed spectral
nodes as actual nonzero physical eigenvectors.
Use: construct the endpoint nodes of the original Gauss--Radau rules rather
than assuming an endpoint measure with the desired moments.
Article: main_krylov, s5:fibre(b).
Proof: genuine feasibility gives both strict leading inverse domains; the two
actual shifted Schur determinants vanish at their true endpoint pivots. The
standard determinant/kernel criterion supplies the actual nonzero physical vectors. -/
theorem physical_fibre_endpoint_eigenvectors
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (mu upper : ℝ)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-mu • 1).PosSemidef ∧
      (upper • 1-lanczosCompletion A hA g hg hc b).PosSemidef) :
    let J := physicalJacobi A hA g hg hc
    let H := lastLeading J
    let x := lastCross J
    let lo := mu+x ⬝ᵥ ((H-mu • 1)⁻¹*ᵥ x)
    let hi := upper-x ⬝ᵥ ((upper • 1-H)⁻¹*ᵥ x)
    (∃ v : Fin (n+1) → ℝ,v≠0 ∧ lanczosCompletion A hA g hg hc lo*ᵥ v=mu • v) ∧
      (∃ v : Fin (n+1) → ℝ,v≠0 ∧ lanczosCompletion A hA g hg hc hi*ᵥ v=upper • v) := by
  obtain ⟨b,hblo,hbhi⟩ := hne
  obtain ⟨hlo,hhi⟩ := physical_fibre_leading_strict A hA g hg hc mu upper b hblo hbhi
  dsimp only
  constructor
  · obtain ⟨v,hv,he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (show
        (lanczosCompletion A hA g hg hc (mu+lastCross (physicalJacobi A hA g hg hc) ⬝ᵥ
          ((lastLeading (physicalJacobi A hA g hg hc)-mu • 1)⁻¹*ᵥ lastCross (physicalJacobi A hA g hg hc)))-mu • 1).det=0 by
      rw [physical_fibre_lower_determinant A hA g hg hc _ mu hlo]
      simp only [add_sub_cancel_left,sub_self,mul_zero])
    refine ⟨v,hv,?_⟩
    simpa only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero] using he
  · obtain ⟨v,hv,he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (show
        (upper • 1-lanczosCompletion A hA g hg hc (upper-lastCross (physicalJacobi A hA g hg hc) ⬝ᵥ
          ((upper • 1-lastLeading (physicalJacobi A hA g hg hc))⁻¹*ᵥ lastCross (physicalJacobi A hA g hg hc)))).det=0 by
      rw [physical_fibre_upper_determinant A hA g hg hc _ upper hhi]
      simp only [sub_sub_cancel,sub_self,mul_zero])
    refine ⟨v,hv,?_⟩
    simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] at he
    exact (sub_eq_zero.mp he).symm

end
end krylov.OneGradient
