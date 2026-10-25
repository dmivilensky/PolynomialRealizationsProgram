import polyak.Boundary.Classification.SwitchSource
import polyak.Numerics.KernelDecide

/-! Five-decimal switching values, proved by exact rational arithmetic and algebraic square bounds. -/
namespace polyak.Boundary.Classification
open LeanCert.Core LeanCert.Engine Numerics Numerics.Parametric SwitchData SwitchSource

private theorem gSucceeded (i : Fin 3) : succeeded (gResult i)=true := by
  fin_cases i <;> kernel_decide
private theorem uSucceeded (i : Fin 3) : succeeded (uResult i)=true := by
  fin_cases i <;> kernel_decide
private theorem radialChecked (i : Fin 3) : sqrtIntervalCheck (radialSquareI i) (radialI i)=true := by
  fin_cases i <;> kernel_decide
private theorem twistChecked (i : Fin 3) : sqrtIntervalCheck (twistSquareI i) (twistRootI i)=true := by
  fin_cases i <;> kernel_decide
private theorem decimalsChecked (i : Fin 5) : decimalCheck i=true := by
  fin_cases i <;> kernel_decide

noncomputable section

private theorem g_mem (i : Fin 3) : pointG i∈gI i := by
  have hm := dyadicValue_mem (gExpr i) (fun _ => parameterI i) {precision:=-80}
    (by norm_num) (fun _ => parameter i) (fun _ => parameter_mem i) (gSucceeded i)
  rwa [gExpr_eval i (fun _ => parameter i) rfl] at hm
private theorem u_mem (i : Fin 3) : pointU i∈uI i := by
  have hm := dyadicValue_mem (uExpr i) (fun _ => parameterI i) {precision:=-80}
    (by norm_num) (fun _ => parameter i) (fun _ => parameter_mem i) (uSucceeded i)
  rwa [uExpr_eval i (fun _ => parameter i) rfl] at hm
private theorem radial_mem (i : Fin 3) : Real.sqrt (pointG i^2-1)∈radialI i := by
  apply sqrtIntervalCheck_sound (radialChecked i)
  simpa only [radialSquareI,pow_two,Rat.cast_one] using IntervalRat.mem_sub
    (IntervalRat.mem_mul (g_mem i) (g_mem i)) (IntervalRat.mem_singleton 1)
private theorem twist_mem (i : Fin 3) : Real.sqrt (1+pointU i^2)∈twistRootI i := by
  apply sqrtIntervalCheck_sound (twistChecked i)
  simpa only [twistSquareI,pow_two,Rat.cast_one] using IntervalRat.mem_add
    (IntervalRat.mem_singleton 1) (IntervalRat.mem_mul (u_mem i) (u_mem i))

private theorem kappaExpr_eval (plus : Bool) (ρ : ℕ → ℝ) :
    Expr.eval ρ (kappaExpr plus)=conditionNumberOfQ
      ((ρ 0+(if plus then 1 else -1)*ρ 2)*(ρ 3-ρ 1)) := by
  cases plus <;> norm_num [kappaExpr,qExpr,Expr.eval,conditionNumberOfQ,
    div_eq_mul_inv,sub_eq_add_neg,pow_two]

/-- Each of the five printed decimal values is correctly rounded to five places. -/
theorem switchingKappa_decimal_bounds (i : Fin 5) :
    ((printedI i).lo : ℝ)<switchingKappa i ∧ switchingKappa i<(printedI i).hi := by
  let j:=sourceIndex i
  let ρ : ℕ → ℝ := fun k => if k=0 then pointG j else if k=1 then pointU j
    else if k=2 then Real.sqrt (pointG j^2-1) else if k=3 then Real.sqrt (1+pointU j^2) else 0
  have hρ : ∀ k,ρ k∈endpointEnv i k := by
    intro k
    by_cases h0 : k=0
    · simpa [ρ,endpointEnv,h0,j] using g_mem j
    · by_cases h1 : k=1
      · simpa [ρ,endpointEnv,h0,h1,j] using u_mem j
      · by_cases h2 : k=2
        · simpa [ρ,endpointEnv,h0,h1,h2,j] using radial_mem j
        · by_cases h3 : k=3
          · simpa [ρ,endpointEnv,h0,h1,h2,h3,j] using twist_mem j
          · simpa [ρ,endpointEnv,h0,h1,h2,h3] using IntervalRat.mem_singleton 0
  have hc := decimalsChecked i
  simp only [decimalCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hm := dyadicValue_mem (kappaExpr (positive i)) (endpointEnv i) {precision:=-80}
    (by norm_num) ρ hρ hc.1
  rw [kappaExpr_eval] at hm
  have hphysical : (ρ 0+(if positive i then 1 else -1)*ρ 2)*(ρ 3-ρ 1)=qPhysical i := by
    simp [ρ,qPhysical,j]
  rw [hphysical,← switchingQ_formula] at hm
  have hlo : ((printedI i).lo : ℝ)<(outcome (kappaResult i)).lo := by exact_mod_cast hc.2.1
  have hhi : ((outcome (kappaResult i)).hi : ℝ)<(printedI i).hi := by exact_mod_cast hc.2.2
  exact ⟨hlo.trans_le hm.1,hm.2.trans_lt hhi⟩

end
end polyak.Boundary.Classification
