import polyak.Boundary.P5.ContinuationTail
import polyak.Boundary.P5.ContinuationDual
import polyak.Numerics.Parametric.Bounds
import polyak.Numerics.Parametric.Weighted

/-! Source-linked polynomial reserves on the entire central continuation.
The potentially vanishing fifth multiplier is handled by endpoint analysis separately. -/
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

private def addE := Expr.add
private def mulE := Expr.mul
private def subE (a b : Expr) : Expr := .add a (.neg b)
private def sqE (a : Expr) : Expr := .mul a a
local infixl:65 " +ₑ " => addE
local infixl:65 " -ₑ " => subE
local infixl:70 " *ₑ " => mulE
private def hE : Expr := .var 0
private def aE : Expr := .var 1
private def bE : Expr := .var 2
private def yE : Expr := .var 3
private def pE : Expr := .var 4
private def dE : Expr := .var 5
private def w2E : Expr := .var 6
private def w3E : Expr := .var 7
private def uE : Expr := .const (1/2) +ₑ hE *ₑ aE
private def xE : Expr := .const (-1/2) +ₑ hE *ₑ bE
private def gE : Expr := .const 1 +ₑ hE
private def gapE (c : Expr) : Expr := .const 1 -ₑ sqE c -ₑ sqE uE
private def mainE : Expr := bE -ₑ aE -ₑ hE *ₑ (sqE aE +ₑ sqE bE)
private def meanE : Expr := mainE +ₑ pE *ₑ (gapE yE -ₑ gapE xE)
private def averageE : Expr := (.const 1 -ₑ hE *ₑ pE) *ₑ gapE xE +ₑ hE *ₑ pE *ₑ gapE yE
private def coefficientE : Expr := (.const 1 -ₑ w2E -ₑ w3E) *ₑ
  (gE *ₑ (.const 4 *ₑ sqE gE -ₑ .const 1))
private def thirdE : Expr := w3E *ₑ (gE *ₑ
  (.const 16 *ₑ sqE (sqE gE) -ₑ .const 12 *ₑ sqE gE +ₑ .const 1))
private def c6E : Expr := .const 16 *ₑ coefficientE
private def c5E : Expr := .const (-16) *ₑ coefficientE *ₑ (.neg gE +ₑ .const 2 *ₑ uE)
private def c4E : Expr := .const 4 *ₑ (thirdE +ₑ .const 4 *ₑ coefficientE *ₑ sqE gE -ₑ
  .const 8 *ₑ coefficientE *ₑ gE *ₑ uE +ₑ .const 4 *ₑ coefficientE *ₑ sqE uE -ₑ .const 9 *ₑ coefficientE)
private def r1E : Expr := c5E +ₑ .const 2 *ₑ (xE +ₑ yE) *ₑ c6E
private def r0E : Expr := c4E +ₑ .const 2 *ₑ (xE +ₑ yE) *ₑ c5E +ₑ
  (.const 3 *ₑ sqE xE +ₑ .const 4 *ₑ xE *ₑ yE +ₑ .const 3 *ₑ sqE yE) *ₑ c6E

def continuationGeometryExpr : Fin 25 → Expr := ![
  aE,.const (11/20) -ₑ aE,bE +ₑ .const (27/100),.neg bE,
  pE,.const 3 -ₑ pE,dE,.const (11/5) -ₑ dE,
  xE +ₑ .const 1,.const 1 -ₑ xE,yE +ₑ .const 1,.const 1 -ₑ yE,
  averageE -ₑ .const (49/100),.const 1 +ₑ mainE,.const 1 -ₑ mainE,
  .const 2 +ₑ meanE,.const 2 -ₑ meanE,yE -ₑ xE,.const 1 -ₑ hE *ₑ pE,
  w2E,w3E,r0E +ₑ r1E +ₑ c6E,r0E +ₑ r1E -ₑ c6E,
  r0E -ₑ r1E +ₑ c6E,r0E -ₑ r1E -ₑ c6E]

def continuationGeometryCheck (I : IntervalRat) (cert : WeightedCertificate 7)
    (cfg : DyadicConfig) : Bool :=
  decide (∀ i, boundCheck (continuationGeometryExpr i) I
    (coordinateBox cert.center cert.radius) cfg true=true)

noncomputable section

def continuationGeometryValue (h : ℝ) (Z : Coordinates) : Fin 25 → ℝ := ![
  Z 0,11/20-Z 0,Z 1+27/100,-Z 1,Z 3,3-Z 3,Z 4,11/5-Z 4,
  branchX h Z+1,1-branchX h Z,Z 2+1,1-Z 2,branchGap h Z-49/100,
  1+mainGapCoefficient h Z,1-mainGapCoefficient h Z,
  2+meanGapCoefficient h Z,2-meanGapCoefficient h Z,Z 2-branchX h Z,1-h*Z 3,
  Z 5,Z 6,residual₀ h Z+residual₁ h Z+residual₂ h Z,
  residual₀ h Z+residual₁ h Z-residual₂ h Z,
  residual₀ h Z-residual₁ h Z+residual₂ h Z,
  residual₀ h Z-residual₁ h Z-residual₂ h Z]

private theorem geometry_eval00 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 0) h Z=Z 0 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]

private theorem geometry_eval01 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 1) h Z=11/20-Z 0 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval02 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 2) h Z=Z 1+27/100 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]

private theorem geometry_eval03 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 3) h Z=-Z 1 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]

private theorem geometry_eval04 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 4) h Z=Z 3 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]

private theorem geometry_eval05 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 5) h Z=3-Z 3 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval06 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 6) h Z=Z 4 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]

private theorem geometry_eval07 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 7) h Z=11/5-Z 4 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval08 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 8) h Z=branchX h Z+1 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]

private theorem geometry_eval09 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 9) h Z=1-branchX h Z := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval10 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 10) h Z=Z 2+1 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]

private theorem geometry_eval11 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 11) h Z=1-Z 2 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval12 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 12) h Z=branchGap h Z-49/100 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval13 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 13) h Z=1+mainGapCoefficient h Z := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval14 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 14) h Z=1-mainGapCoefficient h Z := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval15 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 15) h Z=2+meanGapCoefficient h Z := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval16 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 16) h Z=2-meanGapCoefficient h Z := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval17 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 17) h Z=Z 2-branchX h Z := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval18 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 18) h Z=1-h*Z 3 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval19 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 19) h Z=Z 5 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]

private theorem geometry_eval20 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 20) h Z=Z 6 := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]

private theorem geometry_eval21 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 21) h Z=residual₀ h Z+residual₁ h Z+residual₂ h Z := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval22 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 22) h Z=residual₀ h Z+residual₁ h Z-residual₂ h Z := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval23 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 23) h Z=residual₀ h Z-residual₁ h Z+residual₂ h Z := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

private theorem geometry_eval24 (h : ℝ) (Z : Coordinates) :
    eval (continuationGeometryExpr 24) h Z=residual₀ h Z-residual₁ h Z-residual₂ h Z := by
  have h0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  have e2 : finEnv (embed h Z) 2=Z 1 := rfl
  have e3 : finEnv (embed h Z) 3=Z 2 := rfl
  have e4 : finEnv (embed h Z) 4=Z 3 := rfl
  have e5 : finEnv (embed h Z) 5=Z 4 := rfl
  have e6 : finEnv (embed h Z) 6=Z 5 := rfl
  have e7 : finEnv (embed h Z) 7=Z 6 := rfl
  norm_num [continuationGeometryExpr,eval,evalFin,addE,mulE,subE,Expr.eval,sqE,
    hE,aE,bE,yE,pE,dE,w2E,w3E,uE,xE,gE,gapE,mainE,meanE,averageE,
    c4E,c5E,c6E,r0E,r1E,coefficientE,thirdE,h0,e1,e2,e3,e4,e5,e6,e7,
    branchU,branchX,branchGap,mainGapCoefficient,meanGapCoefficient,
    residual₀,residual₁,residual₂,dualReal_closed,dualClosed_generic,
    dualGeneric_coeff4,dualGeneric_coeff5,dualGeneric_coeff6,
    genericCoefficient4,genericCoefficient5,genericCoefficient6,Spectral.g]
  ring

theorem continuationGeometryExpr_eval (h : ℝ) (Z : Coordinates) (i : Fin 25) :
    eval (continuationGeometryExpr i) h Z=continuationGeometryValue h Z i := by
  fin_cases i
  · exact geometry_eval00 h Z
  · exact geometry_eval01 h Z
  · exact geometry_eval02 h Z
  · exact geometry_eval03 h Z
  · exact geometry_eval04 h Z
  · exact geometry_eval05 h Z
  · exact geometry_eval06 h Z
  · exact geometry_eval07 h Z
  · exact geometry_eval08 h Z
  · exact geometry_eval09 h Z
  · exact geometry_eval10 h Z
  · exact geometry_eval11 h Z
  · exact geometry_eval12 h Z
  · exact geometry_eval13 h Z
  · exact geometry_eval14 h Z
  · exact geometry_eval15 h Z
  · exact geometry_eval16 h Z
  · exact geometry_eval17 h Z
  · exact geometry_eval18 h Z
  · exact geometry_eval19 h Z
  · exact geometry_eval20 h Z
  · exact geometry_eval21 h Z
  · exact geometry_eval22 h Z
  · exact geometry_eval23 h Z
  · exact geometry_eval24 h Z

structure ContinuationGeometry (h : ℝ) (Z : Coordinates) : Prop where
  tail : ContinuationTailBounds h Z
  mass_lt_one : h*Z 3<1
  atoms_ordered : branchX h Z<Z 2
  weight2 : 0<Z 5
  weight3 : 0<Z 6
  residual : 0<residual₀ h Z-|residual₁ h Z|-|residual₂ h Z|

theorem continuationGeometryCheck_sound (I : IntervalRat) (cert : WeightedCertificate 7)
    (cfg : DyadicConfig) (hc : continuationGeometryCheck I cert cfg=true)
    {h : ℝ} {Z : Coordinates} (hh : 0<h) (hmax : h≤59/2500) (hs : h∈I)
    (hX : FinBoxMem Z (coordinateBox cert.center cert.radius)) : ContinuationGeometry h Z := by
  simp only [continuationGeometryCheck,decide_eq_true_eq] at hc
  have hp (i : Fin 25) : 0<continuationGeometryValue h Z i := by
    have hi := boundCheck_sound (continuationGeometryExpr i) I _ cfg true (hc i) hs hX
    change 0<eval (continuationGeometryExpr i) h Z at hi
    rwa [continuationGeometryExpr_eval] at hi
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  have h6 := hp 6
  have h7 := hp 7
  have h8 := hp 8
  have h9 := hp 9
  have h10 := hp 10
  have h11 := hp 11
  have h12 := hp 12
  have h13 := hp 13
  have h14 := hp 14
  have h15 := hp 15
  have h16 := hp 16
  have h17 := hp 17
  have h18 := hp 18
  have h19 := hp 19
  have h20 := hp 20
  have h21 := hp 21
  have h22 := hp 22
  have h23 := hp 23
  have h24 := hp 24
  change 0<Z 0 at h0
  change 0<11/20-Z 0 at h1
  change 0<Z 1+27/100 at h2
  change 0 < -Z 1 at h3
  change 0<Z 3 at h4
  change 0<3-Z 3 at h5
  change 0<Z 4 at h6
  change 0<11/5-Z 4 at h7
  change 0<branchX h Z+1 at h8
  change 0<1-branchX h Z at h9
  change 0<Z 2+1 at h10
  change 0<1-Z 2 at h11
  change 0<branchGap h Z-49/100 at h12
  change 0<1+mainGapCoefficient h Z at h13
  change 0<1-mainGapCoefficient h Z at h14
  change 0<2+meanGapCoefficient h Z at h15
  change 0<2-meanGapCoefficient h Z at h16
  change 0<Z 2-branchX h Z at h17
  change 0<1-h*Z 3 at h18
  change 0<Z 5 at h19
  change 0<Z 6 at h20
  change 0<residual₀ h Z+residual₁ h Z+residual₂ h Z at h21
  change 0<residual₀ h Z+residual₁ h Z-residual₂ h Z at h22
  change 0<residual₀ h Z-residual₁ h Z+residual₂ h Z at h23
  change 0<residual₀ h Z-residual₁ h Z-residual₂ h Z at h24
  refine ⟨⟨hh,hmax,⟨h0,by linarith⟩,⟨by linarith,by linarith⟩,
    ⟨h4,by linarith⟩,⟨h6,by linarith⟩,⟨by linarith,by linarith⟩,
    ⟨by linarith,by linarith⟩,by linarith,abs_lt.mpr ⟨by linarith,by linarith⟩,
    abs_lt.mpr ⟨by linarith,by linarith⟩⟩,by linarith,by linarith,h19,h20,?_⟩
  rcases le_total 0 (residual₁ h Z) with h1 | h1 <;>
    rcases le_total 0 (residual₂ h Z) with h2 | h2
  · rw [abs_of_nonneg h1,abs_of_nonneg h2]; exact h24
  · rw [abs_of_nonneg h1,abs_of_nonpos h2]; linarith
  · rw [abs_of_nonpos h1,abs_of_nonneg h2]; linarith
  · rw [abs_of_nonpos h1,abs_of_nonpos h2]; linarith

end
end polyak.Boundary.P5
