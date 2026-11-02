import krylov.Convergence.VirtualDirectionOutputFields
import krylov.Convergence.VirtualDirectionInputs

/-!
Article: main_krylov, thm:V and lem:cycle-transfer.
Use: identify the true scalar XRFC output gradient with the positively
rescaled independent finite operator output on its actual full source.
Source: exact segment FTC, causal finite prefixes and primitive cone homogeneity.
-/
namespace krylov.Convergence
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Functions krylov.Stability
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual scalar output gradient is exactly the rescaled genuine
finite semantic map. The displayed semantic equality follows from the
true scalar FTC once native localization has been proved.
Article: main_krylov, lem:cycle-transfer and thm:V. -/
theorem xrfcDFunction_scaled_output
    (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (ε : ℝ) (hε : 0<ε) (u : E)
    (hsemantic : G (xrfcDFunctionOutput trial G (ε • u))=
      (xrfcDMethod fullMemory trial).outputGradient (oneGradientFunctionOutputOperator
        (xrfcDMethod fullMemory trial) G H (ε • u) n)
        (oneGradientRun (xrfcDMethod fullMemory trial)
          (oneGradientFunctionOperator (xrfcDMethod fullMemory trial) G H (ε • u)) (G (ε • u)) n)) :
    G (xrfcDFunctionOutput trial G (ε • u))=
      ε • oneGradientFiniteOutput (xrfcDMethod fullMemory trial) Q n
        ((Q u,0)+oneGradientFunctionInput (xrfcDMethod fullMemory trial) G H Q ε u n) := by
  let m := xrfcDMethod fullMemory trial
  let A := oneGradientFunctionOperator m G H (ε • u)
  let B := oneGradientFunctionOutputOperator m G H (ε • u) n
  have hg : Q u+(ε⁻¹ • G (ε • u)-Q u)=ε⁻¹ • G (ε • u) := by abel
  have hpref : ∀ i<n,fcFiniteOperatorPath Q n (fun i : Fin n=>A i.val-Q) i=A i := by
    intro i hi
    simp only [fcFiniteOperatorPath,dite_eq_left hi]
    exact add_sub_cancel _ _
  rw [oneGradientFiniteOutput]
  simp only [oneGradientFunctionInput,Prod.mk_add_mk,zero_add]
  rw [hg,add_sub_cancel]
  rw [oneGradientRun_congr_prefix m _ A _ n hpref]
  have hscale := (xrfcD_scalar_output trial hhom A B (ε⁻¹ • G (ε • u)) ε hε n).2
  rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul] at hscale
  exact hsemantic.trans hscale

end
end krylov.Convergence
