import krylov.Methods.OneGradientChronological
import krylov.Methods.VirtualTrajectory
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, exact actual virtual injection and output balances.
Use: connect genuine XRFC effective gradients and semantic unevaluated output gradients with actual observed steps, native virtual coefficients and physical operator defects.
Source: true one-gradient oracle telescoping and exact computed chronological virtual-solve coordinates.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual effective-gradient injection sum formed from genuine executed step and native virtual-solve coefficient data.
Use: The actual effective-gradient injection sum formed from genuine executed step and native virtual-solve coefficient data.
Article: main_krylov, thm:E1, exact actual virtual injection and output balances.
Proof: Weight each true segment defect action by one plus its actual computed chronological virtual coefficient. -/
def virtualInjectionSum (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  ∑ i : Fin k,(1+oneGradientVirtualCoefficients m A g k i) • ((A i.val-Q) (oneGradientStep m A g i.val))

/-- The actual unevaluated output defect formed from genuine executed step and native virtual-solve data.
Use: The actual unevaluated output defect formed from genuine executed step and native virtual-solve data.
Article: main_krylov, thm:E1, exact actual virtual injection and output balances.
Proof: Weight each real output-minus-segment operator action by its genuine computed chronological virtual coefficient. -/
def virtualOutputDefect (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (B : E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  ∑ i : Fin k,oneGradientVirtualCoefficients m A g k i • ((B-A i.val) (oneGradientStep m A g i.val))

/-- Every actual one-gradient returned gradient equals its original observation plus the genuine chronological sum of evaluated segment actions.
Use: Every actual one-gradient returned gradient equals its original observation plus the genuine chronological sum of evaluated segment actions.
Article: main_krylov, thm:E1, exact actual virtual injection and output balances.
Proof: Telescope the real returned-gradient recursion over the actual finite transcript. -/
theorem oneGradient_gradient_sum (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    oneGradientGradient m A g k=g+∑ i : Fin k,A i.val (oneGradientStep m A g i.val) := by
  induction k with
  | zero => simp [oneGradientGradient,oneGradientRun,History.gradient]
  | succ k ih =>
    rw [oneGradientGradient_succ,ih,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    abel

/-- The genuine XRFC effective gradient equals the original affine quadratic gradient at its actual virtual point plus the true executed injection sum.
Use: The genuine XRFC effective gradient equals the original affine quadratic gradient at its actual virtual point plus the true executed injection sum.
Article: main_krylov, thm:E1, exact actual virtual injection and output balances.
Proof: Use both actual chronological virtual combinations and telescope all genuinely evaluated operator actions. -/
theorem xrfc_virtual_gradient_balance (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    xrfcVirtualGradient trial A g k=g+Q (xrfcVirtualPoint trial A g k)+
      virtualInjectionSum (xrfcMethod fullMemory trial) A Q g k := by
  -- Telescope the true evaluated oracle actions before replacing the actual computed chronological virtual sums.
  let m := xrfcMethod fullMemory trial (E := E)
  have hv := oneGradient_chronological_virtual m A g k
  dsimp only at hv
  have hgrad := oneGradient_gradient_sum m A g k
  change (oneGradientRun m A g k).gradient=g+_ at hgrad
  change virtualGradient (selectedWindow fullMemory (oneGradientRun m A g k)) (oneGradientRun m A g k).gradient=_
  rw [hv.2,xrfcVirtualPoint,OneGradientMethod.outputDisplacement,map_add]
  change _=g+(Q ((oneGradientRun m A g k).displacement)+Q (m.output (oneGradientRun m A g k)))+_
  rw [show m.output (oneGradientRun m A g k)=_ from hv.1,oneGradientRun_displacement_sum]
  rw [← Fin.sum_univ_eq_sum_range (oneGradientStep m A g) k]
  rw [hgrad]
  simp only [map_sum,map_smul,virtualInjectionSum,_root_.sub_apply,smul_sub,add_smul,one_smul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  abel

/-- The actual semantic unevaluated XRFC output gradient equals its genuine effective gradient plus the true executed output-segment defect.
Use: The actual semantic unevaluated XRFC output gradient equals its genuine effective gradient plus the true executed output-segment defect.
Article: main_krylov, thm:E1, exact actual virtual injection and output balances.
Proof: Apply the real output operator to the actual computed virtual correction and subtract the original observed secant extrapolation. -/
theorem xrfc_virtual_output_balance (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E)
    (B : E →L[ℝ] E) (g : E) (k : ℕ) :
    let m := xrfcMethod fullMemory trial (E := E)
    m.outputGradient B (oneGradientRun m A g k)=xrfcVirtualGradient trial A g k+virtualOutputDefect m A B g k := by
  let m := xrfcMethod fullMemory trial (E := E)
  have hv := oneGradient_chronological_virtual m A g k
  dsimp only at hv ⊢
  change (oneGradientRun m A g k).gradient+B (m.output _)=_
  -- The real unevaluated output uses its actual operator on the genuine computed correction, with no new observed query.
  have hc : m.output (oneGradientRun m A g k)=_ := hv.1
  rw [hc]
  change _=virtualGradient (selectedWindow fullMemory (oneGradientRun m A g k)) (oneGradientRun m A g k).gradient+_
  rw [hv.2]
  simp only [map_sum,map_smul,virtualOutputDefect,_root_.sub_apply,smul_sub,Finset.sum_sub_distrib]
  abel
end
end krylov.Methods
