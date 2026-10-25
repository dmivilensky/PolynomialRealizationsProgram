import polyak.Boundary.P5.LagCode
import polyak.Numerics.Parametric.Bounds

/-! Exact finite-lag arithmetic graphs. The cancellation at h=0 is performed
algebraically before interval evaluation, including for all inactive critical lags. -/
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics Numerics.Parametric

private def hE : Expr := .var 0
private def aE : Expr := .var 1
private def bE : Expr := .var 2
private def yE : Expr := .var 3
private def pE : Expr := .var 4
private def dE : Expr := .var 5
private def addE := Expr.add
private def mulE := Expr.mul
private def subE (a b : Expr) : Expr := .add a (.neg b)
private def sqE (a : Expr) : Expr := .mul a a
local infixl:65 " +ₑ " => addE
local infixl:65 " -ₑ " => subE
local infixl:70 " *ₑ " => mulE
private def uE : Expr := .const (1/2) +ₑ hE *ₑ aE
private def xE : Expr := .const (-1/2) +ₑ hE *ₑ bE
private def gapE (c : Expr) : Expr := .const 1 -ₑ sqE c -ₑ sqE uE
private def amplitudeE (c : Expr) : Expr := .const 2 *ₑ uE *ₑ (.const 1 -ₑ sqE c)
private def gapDivE : Expr := bE -ₑ aE -ₑ hE *ₑ (sqE aE +ₑ sqE bE)
private def amplitudeDivE : Expr :=
  .const (3/2) *ₑ aE +ₑ bE +ₑ hE *ₑ (.const 2 *ₑ aE *ₑ bE -ₑ sqE bE) -ₑ
    .const 2 *ₑ sqE hE *ₑ aE *ₑ sqE bE

def dividedSlackExpr (n : ℕ) (code : LagCode n) (σ : ℚ) : Expr :=
  let tg := polynomialExpr code.TGdiv hE
  let tx := polynomialExpr code.TXdiv (hE *ₑ bE)
  let ux := polynomialExpr code.UXdiv (hE *ₑ bE)
  let ug := polynomialExpr code.UG hE
  let ty := polynomialExpr code.TY yE
  let uy := polynomialExpr code.UY yE
  let main := gapDivE *ₑ (.const 1 -ₑ .const code.tCentre) +ₑ
    gapE xE *ₑ (tg -ₑ bE *ₑ tx) +ₑ
    .const σ *ₑ (amplitudeDivE *ₑ .const code.uCentre +ₑ amplitudeE xE *ₑ bE *ₑ ux)
  let rawMain := gapE xE *ₑ (.const 1 +ₑ hE *ₑ tg -ₑ
      (.const code.tCentre +ₑ hE *ₑ bE *ₑ tx)) +ₑ
    .const σ *ₑ amplitudeE xE *ₑ (.const code.uCentre +ₑ hE *ₑ bE *ₑ ux)
  let rawAux := gapE yE *ₑ (.const 1 +ₑ hE *ₑ tg -ₑ ty) +ₑ
    .const σ *ₑ amplitudeE yE *ₑ uy
  main +ₑ pE *ₑ (rawAux -ₑ rawMain) -ₑ .const σ *ₑ dE *ₑ ug

noncomputable section

theorem dividedSlackExpr_eval (n : ℕ) (code : LagCode n) (σ : ℚ)
    (h : ℝ) (Z : Coordinates) :
    eval (dividedSlackExpr n code σ) h Z=dividedSlack n code h Z σ := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have h1 : finEnv (embed h Z) 1=Z 0 := rfl
  have h2 : finEnv (embed h Z) 2=Z 1 := rfl
  have h3 : finEnv (embed h Z) 3=Z 2 := rfl
  have h4 : finEnv (embed h Z) 4=Z 3 := rfl
  have h5 : finEnv (embed h Z) 5=Z 4 := rfl
  have ht := code.TX_exact (h*Z 1)
  have hu := code.UX_exact (h*Z 1)
  change Spectral.chebT n (branchX h Z)=_ at ht
  change Spectral.chebU (n-1) (branchX h Z)=_ at hu
  simp only [dividedSlackExpr,eval,evalFin,addE,subE,mulE,Expr.eval,polynomialExpr_value,
    hE,aE,bE,yE,pE,dE,sqE,uE,xE,gapE,amplitudeE,gapDivE,amplitudeDivE,h0,h1,h2,h3,h4,h5]
  change _=dividedSlack n code h Z σ
  unfold dividedSlack mainDivided mainAmplitudeCoefficient mainGapCoefficient actualRaw Spectral.lagB lagDenominator
  rw [code.TG_exact,ht,hu,← code.TY_exact (Z 2),← code.UY_exact (Z 2),← code.UG_exact]
  unfold branchU branchX Spectral.g
  norm_num only [Rat.cast_one,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_div]
  ring

end
end polyak.Boundary.P5
