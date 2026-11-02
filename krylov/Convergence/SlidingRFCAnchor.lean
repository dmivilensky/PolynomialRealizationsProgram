import krylov.Convergence.SlidingRFCExecution
import krylov.Secant.Correction

/-!
Article: main_krylov, apA:galerkin(a) and thm:Ip.
Use: identify the original RFC line-quotient/predicted-gradient correction
with the actual anchored full observed secant solve. The line scalar is
arbitrary, including zero, and need not equal the evaluated probe length.
Source: the exact current-column anchor identity already proved in Secant.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original RFC predicted line step and actual full correction have
the same anchored output for every real line scalar. This connects the
bounded evaluated-probe executor with the original RFC coefficient rule. -/
theorem rfc_model_line_anchor
    (s y : Fin (n+1) → EuclideanSpace ℝ (Fin (n+2)))
    (d z g x : EuclideanSpace ℝ (Fin (n+2)))
    (hM : IsUnit (ss1Model (Fin.snoc s d) (Fin.snoc y z)).det) (α : ℝ) :
    x+α • d+combine (Fin.snoc s d) (modelCoefficients (Fin.snoc s d)
      (ss1Model (Fin.snoc s d) (Fin.snoc y z)) (g+α • z))=
      ss1Point (Fin.snoc s d) (Fin.snoc y z) g x := by
  let U : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) := Fin.snoc s d
  let V := windowMatrix U
  let M := ss1Model U (Fin.snoc y z)
  let e : Fin (n+2) → ℝ := Pi.single (Fin.last (n+1)) 1
  have hd : V*ᵥe=WithLp.ofLp d := by
    ext a
    simp only [e,mulVec_single_one,Matrix.col_apply,V,windowMatrix,U,Fin.snoc_last]
  have hz : M*ᵥe=Vᵀ*ᵥWithLp.ofLp z := by
    rw [←coordinates_windowMatrix U z]
    exact ss1Model_snoc_current_column s y d z
  have hh := correction_anchor V M hM (WithLp.ofLp g) (WithLp.ofLp z)
    (WithLp.ofLp d) e hd hz α
  have he := congrArg (WithLp.toLp 2) hh
  change α • d-WithLp.toLp 2 (V*ᵥ(M⁻¹*ᵥ(Vᵀ*ᵥWithLp.ofLp (g+α • z))))=
    -(WithLp.toLp 2 (V*ᵥ(M⁻¹*ᵥ(Vᵀ*ᵥWithLp.ofLp g)))) at he
  change x+α • d+combine U (modelCoefficients U M (g+α • z))=ss1Point U (Fin.snoc y z) g x
  rw [ss1Point]
  simp only [modelCoefficients,combine_windowMatrix,coordinates_windowMatrix,mulVec_neg]
  change x+α • d-WithLp.toLp 2 (V*ᵥ(M⁻¹*ᵥ(Vᵀ*ᵥWithLp.ofLp (g+α • z))))=
    x-WithLp.toLp 2 (V*ᵥ(M⁻¹*ᵥ(Vᵀ*ᵥWithLp.ofLp g)))
  have h := congrArg (fun v=>x+v) he
  simpa only [add_sub_assoc,sub_eq_add_neg,add_assoc] using h

end
end krylov.Convergence
