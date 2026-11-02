import krylov.OneGradient.JacobiCoordinates
import krylov.LinearAlgebra.LastSchurPivot
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(a), actual physical Schur threshold.
Use: identify the physical inverse-pivot positivity domain with the literal
Schur correction of the original positively oriented Jacobi compression.
Source: genuine orthogonal physical Lanczos coordinates and the proved actual
leading-block inverse formula; no Schur threshold is supplied as fibre data.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.LinearAlgebra
variable {n : ℕ}

/-- The real positive Jacobi matrix obtained by compressing the original
physical matrix in its actual full Lanczos frame.
Use: its leading block and coupling column are the source's known information.
Article: main_krylov, s5:fibre(a), J. -/
def physicalJacobi
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (physicalLanczosColumns A hA g hg hc)ᵀ*A*physicalLanczosColumns A hA g hg hc

/-- The actual positive Lanczos compression is positive definite.
Use: every true Schur inverse is applied on its proved original domain.
Article: main_krylov, s5:fibre(a).
Proof: the genuine physical frame is orthogonal, hence injective, and preserves
the original strictly positive quadratic form under congruence. -/
theorem physical_jacobi_positive
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) : (physicalJacobi A hA g hg hc).PosDef := by
  let Z := physicalLanczosColumns A hA g hg hc
  have hZ : Zᵀ*Z=1 := physical_lanczos_orthogonal A hA g hg hc
  have hinj : Function.Injective Z.mulVec := by
    intro v w hvw
    have he := congrArg (fun v => Zᵀ*ᵥ v) hvw
    simpa only [mulVec_mulVec,hZ,one_mulVec] using he
  simpa only [physicalJacobi,conjTranspose_eq_transpose_of_trivial] using
    hA.conjTranspose_mul_mul_same hinj

/-- The actual Jacobi inverse is the original physical inverse in the same
true orthogonal Lanczos coordinates.
Use: its last inverse entry is the original normal's physical inverse energy.
Article: main_krylov, s5:fibre(a).
Proof: true orthogonal coordinates give both inverse cancellations, and the
matrix inverse product theorem transports the genuine original inverse. -/
theorem physical_jacobi_inverse
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    (physicalJacobi A hA g hg hc)⁻¹=
      (physicalLanczosColumns A hA g hg hc)ᵀ*A⁻¹*physicalLanczosColumns A hA g hg hc := by
  let Z := physicalLanczosColumns A hA g hg hc
  have hZ : Zᵀ*Z=1 := physical_lanczos_orthogonal A hA g hg hc
  have hZi : Z⁻¹=Zᵀ := Matrix.inv_eq_left_inv hZ
  have hZti : Zᵀ⁻¹=Z := Matrix.inv_eq_left_inv (mul_eq_one_comm.mp hZ)
  change (Zᵀ*A*Z)⁻¹=Zᵀ*A⁻¹*Z
  rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,hZi,hZti,Matrix.mul_assoc]

/-- The derived physical inverse pivot is exactly the last entry of the
inverse of the original positive Jacobi compression.
Use: identify the source's concrete Schur pivot with the original physical
information fibre and its actual CG last line.
Article: main_krylov, s5:fibre(a).
Proof: transport the actual inverse by the genuine physical frame and read
the last diagonal via its true inner-product compression identity. -/
theorem physical_jacobi_inverse_last
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    (physicalJacobi A hA g hg hc)⁻¹ (Fin.last n) (Fin.last n)=lastInversePivot A hA g hg hc := by
  rw [physical_jacobi_inverse,physical_lanczos_compression]
  change inner ℝ (lastLanczosVector A hA g hg hc) (cgOperator A⁻¹ (lastLanczosVector A hA g hg hc))=_
  simp only [cgOperator,Matrix.inner_toEuclideanCLM,lastInversePivot]

/-- The entire original positive information fibre's threshold equals the
actual leading-block Schur correction of its original positive Jacobi matrix.
Use: the physical half-line and actual last CG reciprocal pivot are now in
literal source Schur coordinates, derived from real matrices.
Article: main_krylov, s5:fibre(a), sigma=b_A-alpha_(n-1)^{-1}.
Proof: compare the actual Jacobi last inverse entry with the genuine leading
Schur inverse formula and invert only the proved positive physical inverse pivot. -/
theorem physical_jacobi_schur_threshold
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    lastSchurCorrection (physicalJacobi A hA g hg hc)=
      lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹ := by
  have he := last_schur_inverse (physicalJacobi A hA g hg hc) (physical_jacobi_positive A hA g hg hc)
  rw [physical_jacobi_inverse_last] at he
  have hdiag : physicalJacobi A hA g hg hc (Fin.last n) (Fin.last n)=lastJacobiPivot A hA g hg hc := by
    rw [physicalJacobi,physical_lanczos_compression]
    rfl
  rw [hdiag] at he
  have hi := congrArg (fun x : ℝ => x⁻¹) he
  rw [inv_inv] at hi
  linarith

end
end krylov.OneGradient
