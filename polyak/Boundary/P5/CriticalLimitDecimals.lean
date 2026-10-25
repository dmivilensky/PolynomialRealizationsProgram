import polyak.Boundary.P5.CriticalDecimals
import polyak.Numerics.Parametric.Dyadic
import polyak.Numerics.ShiftedCode
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The four printed first-order local-limit constants in Appendix B,
with exact interval checks linked to their actual algebraic source formulas. -/
namespace polyak.Boundary.P5.CriticalLimitDecimals
open Polynomial Numerics Certificates.P5 LeanCert.Core LeanCert.Engine Numerics.Parametric

private def aExpr : Expr := polynomialExpr ACode.code (.var 0)
private def bExpr : Expr := polynomialExpr BCode.code (.var 0)
private def pExpr : Expr := polynomialExpr PCode.code (.var 0)

private def sourceExpr : Fin 4 → Expr := ![
  .add bExpr (.neg aExpr),
  .add (.add bExpr (.neg aExpr))
    (.mul pExpr (.add (.const (1/4)) (.neg (.mul (.var 0) (.var 0))))),
  .add (.mul (.var 1) aExpr) (.mul bExpr (.inv (.var 1))),
  .mul (.mul (.const (-2)) bExpr) (.inv (.var 1))]

private def sqrt3Interval : IntervalRat :=
  ⟨173205080756887/100000000000000,173205080756888/100000000000000,by norm_num⟩
private def env (i : ℕ) : IntervalRat :=
  if i=0 then criticalFineInterval else if i=1 then sqrt3Interval else IntervalRat.singleton 0
private def result (i : Fin 4) := dyadicValue (sourceExpr i) env {precision:=-80}
private def printed : Fin 4 → IntervalRat := ![
  ⟨-774/1000,-773/1000,by norm_num⟩,⟨-268/1000,-267/1000,by norm_num⟩,
  ⟨742/1000,743/1000,by norm_num⟩,⟨298/1000,299/1000,by norm_num⟩]
private def checked (i : Fin 4) : Bool := succeeded (result i) &&
  decide ((printed i).lo<(outcome (result i)).lo ∧ (outcome (result i)).hi<(printed i).hi)
private theorem accepted (i : Fin 4) : checked i=true := by fin_cases i <;> kernel_decide

noncomputable section

/-- The actual four source expressions, in their printed order. -/
def sourceValue : Fin 4 → ℝ := ![
  B₀-A₀,B₀-A₀+P₀*(1/4-y₀^2),Real.sqrt 3*A₀+B₀/Real.sqrt 3,-2*B₀/Real.sqrt 3]

private theorem aExpr_eval (ρ : ℕ → ℝ) (he : ρ 0=y₀) : Expr.eval ρ aExpr=A₀ := by
  rw [aExpr,polynomialExpr_value,ACode.exact,Expr.eval,he]
  rfl
private theorem bExpr_eval (ρ : ℕ → ℝ) (he : ρ 0=y₀) : Expr.eval ρ bExpr=B₀ := by
  rw [bExpr,polynomialExpr_value,BCode.exact,Expr.eval,he]
  rfl
private theorem pExpr_eval (ρ : ℕ → ℝ) (he : ρ 0=y₀) : Expr.eval ρ pExpr=P₀ := by
  rw [pExpr,polynomialExpr_value,PCode.exact,Expr.eval,he]
  rfl

private theorem sourceExpr_eval (i : Fin 4) (ρ : ℕ → ℝ) (he : ρ 0=y₀) (hs : ρ 1=Real.sqrt 3) :
    Expr.eval ρ (sourceExpr i)=sourceValue i := by
  fin_cases i <;> simp [sourceExpr,sourceValue,Expr.eval,aExpr_eval ρ he,bExpr_eval ρ he,
    pExpr_eval ρ he,he,hs,div_eq_mul_inv,sub_eq_add_neg,pow_two]

private theorem sqrt3_mem : Real.sqrt (3 : ℝ)∈sqrt3Interval := by
  have hs:=Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  have hn:=Real.sqrt_nonneg (3 : ℝ)
  norm_num [sqrt3Interval,IntervalRat.mem_def]
  constructor <;> nlinarith

/-- All four displayed three-place prefixes enclose the actual local-limit constants. -/
theorem sourceValue_displayed_bounds (i : Fin 4) :
    ((printed i).lo : ℝ)<sourceValue i ∧ sourceValue i<(printed i).hi := by
  let ρ : ℕ → ℝ := fun n => if n=0 then y₀ else if n=1 then Real.sqrt 3 else 0
  have hρ : ∀ n,ρ n∈env n := by
    intro n
    by_cases h0 : n=0
    · simpa [ρ,env,h0] using y₀_fine_mem
    · by_cases h1 : n=1
      · simpa [ρ,env,h0,h1] using sqrt3_mem
      · simpa [ρ,env,h0,h1] using IntervalRat.mem_singleton 0
  have hc:=accepted i
  simp only [checked,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hm:=dyadicValue_mem (sourceExpr i) env {precision:=-80} (by norm_num) ρ hρ hc.1
  rw [sourceExpr_eval i ρ (by simp [ρ]) (by simp [ρ])] at hm
  have hlo : ((printed i).lo : ℝ)<(outcome (result i)).lo := by exact_mod_cast hc.2.1
  have hhi : ((outcome (result i)).hi : ℝ)<(printed i).hi := by exact_mod_cast hc.2.2
  exact ⟨hlo.trans_le hm.1,hm.2.trans_lt hhi⟩

/-- Source-facing form of the four printed local-limit decimal enclosures. -/
theorem critical_local_limits_displayed :
    ((-774/1000 : ℝ)<B₀-A₀ ∧ B₀-A₀< -773/1000) ∧
    ((-268/1000 : ℝ)<B₀-A₀+P₀*(1/4-y₀^2) ∧ B₀-A₀+P₀*(1/4-y₀^2)< -267/1000) ∧
    ((742/1000 : ℝ)<Real.sqrt 3*A₀+B₀/Real.sqrt 3 ∧ Real.sqrt 3*A₀+B₀/Real.sqrt 3<743/1000) ∧
    ((298/1000 : ℝ)< -2*B₀/Real.sqrt 3 ∧ -2*B₀/Real.sqrt 3<299/1000) := by
  have h0:=sourceValue_displayed_bounds 0
  have h1:=sourceValue_displayed_bounds 1
  have h2:=sourceValue_displayed_bounds 2
  have h3:=sourceValue_displayed_bounds 3
  norm_num [printed,sourceValue] at h0 h1 h2 h3 ⊢
  exact ⟨h0,h1,h2,h3⟩

end
end polyak.Boundary.P5.CriticalLimitDecimals
