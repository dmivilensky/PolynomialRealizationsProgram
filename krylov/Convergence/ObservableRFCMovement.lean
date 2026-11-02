import krylov.Convergence.ObservableRFCGate
import krylov.Convergence.ObservableRFCAlgebra

/-!
Article: main_krylov, apG:Dunif, proposed RFC movement before acceptance.
Use: bound the true proposed correction even on the failed-energy branch.
Source: actual normalized model conditioning and exact-search residuals;
neither a successful value gate nor a relative accepted-step bound enters.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- All actual proposed corrections satisfy the true projected incoming
gradient estimate before their observable energy test. Article: apG:Dunif. -/
theorem observable_rfc_proposed_movement {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {x₀ : E} {B : History E} {N : ℕ} {epsilon bar : ℝ}
    (I : ObservableRFCInvariant T f G x₀ N epsilon bar B)
    (P : ObservableRFCPrepared T f G H r x₀ B epsilon)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (hn : 1≤N) (hsize : B.records.length<N) (he : 0≤epsilon) (hb : 0≤bar)
    (hsmall : (N:ℝ)*epsilon≤1/128) (hbar : (N:ℝ)*bar≤1/16) :
    ‖T (rfcFunctionCorrectionStep T f G fullMemory r x₀ B)‖≤
      4*(‖projectedResidual (unitWindow (observablePrimal T B)) (T.symm B.gradient)‖+
        Real.sqrt N*((3*epsilon)*‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖)) := by
  let d := T (rfcFunctionDirection fullMemory B)
  let A := observableRFCSearchOperator T f H r x₀ B
  have hd := P.direction
  have hu (i : Fin (B.pairs.length+1)) : observableRFCModelSteps T B i≠0 := Fin.cases hd I.steps i
  have hy (i : Fin (B.pairs.length+1)) :
      ‖observableRFCModelImages T f H r x₀ B i-observableRFCModelSteps T B i‖≤
        (2*epsilon)*‖observableRFCModelSteps T B i‖ := by
    refine Fin.cases ?_ I.pairs i
    have hh := ((A-ContinuousLinearMap.id ℝ E).le_opNorm d).trans
      (mul_le_mul_of_nonneg_right P.operator (norm_nonneg d))
    simp only [_root_.sub_apply,ContinuousLinearMap.id_apply] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : epsilon≤2*epsilon) (norm_nonneg d))
  have hdim : B.pairs.length+1≤N := by rw [History.pairs_length];omega
  have hdim' : ((B.pairs.length+1:ℕ):ℝ)≤N := by exact_mod_cast hdim
  have hmodel := normalized_pairModel_identity_distance
    (observableRFCModelSteps T B) (observableRFCModelImages T f H r x₀ B) hu
    (by positivity : 0≤2*epsilon) hy P.gram
  have hmodel' : ‖rescaleModel
      (pairModel (observableRFCModelSteps T B) (observableRFCModelImages T f H r x₀ B))
      (fun i=>‖observableRFCModelSteps T B i‖⁻¹)-1‖≤1/2 := hmodel.trans (by
    have hh := mul_le_mul_of_nonneg_right hdim' he
    nlinarith only [hh,hsmall])
  have hmove := near_identity_model_movement (observableRFCModelSteps T B)
    (observableRFCModelImages T f H r x₀ B) hu (observableRFCLineGradient T f G r x₀ B)
    hmodel' (P.gram.trans (by norm_num))
  have hdomains := I.domains hT hn hsize.le he hb hsmall hbar
  have ho (i : Fin B.pairs.length) : inner ℝ (observableDual T B i) d=0 :=
    observable_direction_conjugate T hT B hdomains.1 i
  have hN : (1:ℝ)≤N := by exact_mod_cast hn
  have hep : epsilon≤1/8 := by nlinarith only [mul_le_mul_of_nonneg_right hN he,hsmall]
  have hcurv : inner ℝ d (A d)≠0 := by
    have hh := observable_operator_form A epsilon P.operator d
    have hp := norm_pos_iff.mpr P.direction
    have hh' : 0 < inner ℝ d (A d) := by nlinarith only [hh.1,hep,sq_pos_of_pos hp]
    exact hh'.ne'
  have hsearch := normalizedSearch_residual_bound (observablePrimal T B) (observableDual T B)
    I.steps A (T.symm B.gradient) d he (by positivity : 0≤2*epsilon) P.operator I.pairs ho hcurv
  rw [←P.searched,←P.line] at hsearch
  rw [P.correction]
  have hforcing : Real.sqrt ((B.pairs.length:ℝ)+1)*
      ((epsilon+2*epsilon)*‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖)≤
      Real.sqrt N*((3*epsilon)*‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖) := by
    rw [show epsilon+2*epsilon=3*epsilon by ring]
    apply mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by positivity)
    exact_mod_cast hdim
  exact hmove.trans (mul_le_mul_of_nonneg_left
    (hsearch.trans (add_le_add le_rfl hforcing)) (by norm_num))

/-- The literal failed-energy branch has a short actual searched step
with no minimum-length hypothesis. Article: main_krylov, apG:Dunif. -/
theorem observable_rfc_failed_line {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {x₀ : E} {B : History E} {N : ℕ} {epsilon bar : ℝ}
    (I : ObservableRFCInvariant T f G x₀ N epsilon bar B)
    (P : ObservableRFCPrepared T f G H r x₀ B epsilon)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (hn : 1≤N) (hsize : B.records.length<N) (he : 0≤epsilon) (hb : 0<bar)
    (hsmall : (N:ℝ)*epsilon≤1/128) (hbar : (N:ℝ)*bar≤1/16)
    (hfailed : bar<observableCorrectionRatio T f G r x₀ B)
    (hshort : 12*Real.sqrt N*epsilon≤bar/4) :
    ‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖≤
      16*‖projectedResidual (unitWindow (observablePrimal T B)) (T.symm B.gradient)‖/bar := by
  have hN : (1:ℝ)≤N := by exact_mod_cast hn
  have hep : epsilon≤1/8 := by nlinarith only [mul_le_mul_of_nonneg_right hN he,hsmall]
  exact observable_rfc_failed_short _ _ _ _ _ N hb (norm_nonneg _)
    (P.failed hT hep hb.le hfailed)
    (observable_rfc_proposed_movement I P hT hn hsize he hb.le hsmall hbar) hshort

end
end krylov.Convergence
