import polyak.CertifiedExamples.Exact313.GeometryCode

/-! Executable source formulas for the coefficient-chart inverse. -/
namespace polyak.CertifiedExamples.Exact313.Code
open LeanCert.Core LeanCert.Engine

def secularAt (d : Expr) : Expr :=
  .sub (.sub (.add d (.div (.pow linear 2) d))
    (.mul (.const 2) (.sub (.neg quadratic) constant)))
    (.inv (.add d (.mul (.const 2) quadratic)))
def normalizedB : Expr := .inv (.add (.var 2) (.mul (.const 2) quadratic))
def normalizedU : Expr := .var 3
def normalizedA : Expr := .div (.mul linear normalizedB) normalizedU

def beta : Expr := .div (.sub normalizedU (.const 1)) (.add normalizedU (.const 1))
def sourceA : Expr := .mul (.sub (.const 1) beta) normalizedA
def sourceB : Expr := .mul (.sub (.const 1) beta) normalizedB
def sourceX : Expr := .sub (.sub (.add (.const 1) beta) sourceA) sourceB
def sourceY : Expr := .add (.sub (.add (.const 1) beta) sourceA) sourceB
def sourceKappa : Expr := .div sourceY sourceX

def locationReserves : Fin 6→Expr := ![
  .sub sourceKappa (.const (1670685/20000)),
  .sub (.const (1670687/20000)) sourceKappa,
  .sub sourceY (.const (4437817/2000000)),
  .sub (.const (4437819/2000000)) sourceY,
  .sub beta (.const (1245535/2000000)),
  .sub (.const (1245537/2000000)) beta]

end polyak.CertifiedExamples.Exact313.Code
