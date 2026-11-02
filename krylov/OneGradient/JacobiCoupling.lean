import krylov.OneGradient.JacobiPivot
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(a), literal beta-squared Schur coordinate.
Use: finish the physical threshold dictionary with the source's actual last
positive Jacobi coupling and actual leading inverse entry.
Source: genuine finite Lanczos--Stieltjes tridiagonality and the proved true
physical leading-block Schur inverse identity (Meurant06, GolubMeurant10).
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.LinearAlgebra
variable {n : ℕ}

/-- Tridiagonality specializes the actual last-column Schur correction to the
last coupling squared times the actual final entry of any real quadratic form.
Use: the source's beta-squared e-transpose-J0-inverse-e formula has no assumed
Schur data and uses the original matrix entries.
Article: main_krylov, s5:fibre(a).
Proof: the actual cross column is beta times the last coordinate vector;
linearity and the singleton contraction give the literal quadratic correction. -/
theorem tridiagonal_last_cross_quadratic
    (J : Matrix (Fin (n+2)) (Fin (n+2)) ℝ)
    (hfar : ∀ i : Fin (n+1),i≠Fin.last n → J (Fin.castSucc i) (Fin.last (n+1))=0)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    lastCross J ⬝ᵥ (M*ᵥ lastCross J)=J (Fin.castSucc (Fin.last n)) (Fin.last (n+1))^2*
      M (Fin.last n) (Fin.last n) := by
  let e : Fin (n+1) → ℝ := Pi.single (Fin.last n) 1
  let beta := J (Fin.castSucc (Fin.last n)) (Fin.last (n+1))
  have hx : lastCross J=beta • e := by
    funext i
    by_cases hi : i=Fin.last n
    · subst i
      simp only [lastCross,e,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one,beta]
    · simp only [lastCross,hfar i hi,e,Pi.smul_apply,Pi.single_eq_of_ne hi,smul_eq_mul,mul_zero]
  have he : e ⬝ᵥ (M*ᵥ e)=M (Fin.last n) (Fin.last n) := by
    simp only [e,dotProduct,mulVec,Pi.single_apply,ite_mul,one_mul,zero_mul,
      mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [hx,mulVec_smul,smul_dotProduct,dotProduct_smul,he]
  dsimp only [beta]
  ring

/-- The true tridiagonal last Schur correction has the printed beta-squared
leading-inverse-entry formula.
Use: identify the physical positive-fibre threshold using actual original entries.
Article: main_krylov, s5:fibre(a).
Proof: apply the genuine singleton cross-column contraction to the real leading inverse. -/
theorem tridiagonal_last_schur
    (J : Matrix (Fin (n+2)) (Fin (n+2)) ℝ)
    (hfar : ∀ i : Fin (n+1),i≠Fin.last n → J (Fin.castSucc i) (Fin.last (n+1))=0) :
    lastSchurCorrection J=J (Fin.castSucc (Fin.last n)) (Fin.last (n+1))^2*
      (lastLeading J)⁻¹ (Fin.last n) (Fin.last n) :=
  tridiagonal_last_cross_quadratic J hfar (lastLeading J)⁻¹

/-- The actual original positive Jacobi compression has the source's literal
beta-squared leading-inverse Schur threshold.
Use: close the physical information-fibre positivity and genuine last CG step
formulas in the printed Jacobi coordinates, for every full-atom reference of
at least two active sites.
Article: main_krylov, s5:fibre(a), sigma=beta^2 e_(n-2)^T J0^{-1} e_(n-2).
Proof: derive the actual compressed cross-column sparsity from the reconstructed
gradient measure's proved tridiagonality, then insert the genuine physical
Schur-threshold identity and its singleton quadratic-form calculation. -/
theorem physical_jacobi_coupling_threshold
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+2) :
    let J := physicalJacobi A hA g hg hc
    lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹=
      J (Fin.castSucc (Fin.last n)) (Fin.last (n+1))^2*
        (lastLeading J)⁻¹ (Fin.last n) (Fin.last n) := by
  rw [← physical_jacobi_schur_threshold]
  apply tridiagonal_last_schur
  intro i hi
  rw [physicalJacobi,physical_lanczos_jacobi,(gradientSpectralData A hA g hg).reconstructed_matrix]
  apply (gradientSpectralData A hA g hg).multiplication_tridiagonal
  left
  have hin : i.val<n := by
    have hi' : i.val≠n := by intro he;apply hi;exact Fin.ext he
    omega
  simpa only [Fin.val_castSucc,Fin.val_last] using (show i.val+1<n+1 by omega)

end
end krylov.OneGradient
