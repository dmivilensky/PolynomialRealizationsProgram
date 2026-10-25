import polyak.Certificates.Continuation.P5EndpointGraphs
import polyak.Numerics.Parametric.Dyadic
import polyak.Numerics.SqrtInterval

/-! Exact rational witnesses for the five printed switching condition numbers.
Every enclosure is checked against the source formulas in SwitchDecimals. -/
namespace polyak.Boundary.Classification.SwitchData
open LeanCert.Core LeanCert.Engine Numerics Numerics.Parametric

def half (e : Expr) : Expr := .mul (.const (1/2)) e
def spiralU (e : Expr) : Expr := .add (.const 1) (.neg (.inv (.mul (.const 2) e)))
def gwE : Expr := half (.add (.const 1) (.var 0))

def parameterI : Fin 3 → IntervalRat := ![
  ⟨173205080756887/100000000000000,173205080756888/100000000000000,by norm_num⟩,
  ⟨10332964166603/10000000000000,10332964166604/10000000000000,by norm_num⟩,
  ⟨16989316152393/10000000000000,16989316152394/10000000000000,by norm_num⟩]

def gExpr : Fin 3 → Expr := ![gwE,.var 0,Certificates.Continuation.P5EndpointGraphs.G]
def uExpr : Fin 3 → Expr := ![spiralU gwE,spiralU (.var 0),Certificates.Continuation.P5EndpointGraphs.u]

def gResult (i : Fin 3) := dyadicValue (gExpr i) (fun _ => parameterI i) {precision:=-80}
def uResult (i : Fin 3) := dyadicValue (uExpr i) (fun _ => parameterI i) {precision:=-80}
def gI (i : Fin 3) : IntervalRat := outcome (gResult i)
def uI (i : Fin 3) : IntervalRat := outcome (uResult i)

def radialI : Fin 3 → IntervalRat := ![
  ⟨9306048590/10000000000,9306048592/10000000000,by norm_num⟩,
  ⟨2601950895/10000000000,2601950898/10000000000,by norm_num⟩,
  ⟨2184466471/10000000000,2184466475/10000000000,by norm_num⟩]

def twistRootI : Fin 3 → IntervalRat := ![
  ⟨11840286264/10000000000,11840286269/10000000000,by norm_num⟩,
  ⟨11253316545/10000000000,11253316551/10000000000,by norm_num⟩,
  ⟨11232533225/10000000000,11232533230/10000000000,by norm_num⟩]

def radialSquareI (i : Fin 3) := ((gI i).mul (gI i)).sub (IntervalRat.singleton 1)
def twistSquareI (i : Fin 3) := (IntervalRat.singleton 1).add ((uI i).mul (uI i))
def sourceIndex : Fin 5 → Fin 3 := ![0,1,2,2,1]
def positive : Fin 5 → Bool := ![false,false,false,true,true]

def qExpr (plus : Bool) : Expr := .mul
  (.add (.var 0) (.mul (.const (if plus then 1 else -1)) (.var 2)))
  (.add (.var 3) (.neg (.var 1)))
def kappaExpr (plus : Bool) : Expr :=
  let q:=qExpr plus
  let r:=.mul (.add (.const 1) q) (.inv (.add (.const 1) (.neg q)))
  .mul r r

def endpointEnv (i : Fin 5) (j : ℕ) : IntervalRat :=
  if j=0 then gI (sourceIndex i) else if j=1 then uI (sourceIndex i)
  else if j=2 then radialI (sourceIndex i) else if j=3 then twistRootI (sourceIndex i)
  else IntervalRat.singleton 0

def kappaResult (i : Fin 5) := dyadicValue (kappaExpr (positive i)) (endpointEnv i) {precision:=-80}

def printedI : Fin 5 → IntervalRat := ![
  ⟨531291/200000,531293/200000,by norm_num⟩,
  ⟨1546389/200000,1546391/200000,by norm_num⟩,
  ⟨1729689/200000,1729691/200000,by norm_num⟩,
  ⟨10728605/200000,10728607/200000,by norm_num⟩,
  ⟨14229463/200000,14229465/200000,by norm_num⟩]

def decimalCheck (i : Fin 5) : Bool := succeeded (kappaResult i) &&
  decide ((printedI i).lo<(outcome (kappaResult i)).lo ∧
    (outcome (kappaResult i)).hi<(printedI i).hi)

end polyak.Boundary.Classification.SwitchData
