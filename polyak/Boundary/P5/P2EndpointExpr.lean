import polyak.Boundary.P5.P2Lift
import polyak.Boundary.P2.Physical
import polyak.Certificates.Continuation.P5EndpointGraphs
import polyak.Numerics.RationalExpr

/-! Exact expression graph of the algebraic P2 endpoint in the P5 source coordinates. -/
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics Numerics.Parametric

private def addE := Expr.add
private def mulE := Expr.mul
private def subE (a b : Expr) : Expr := .add a (.neg b)
private def divE (a b : Expr) : Expr := .mul a (.inv b)
private def sqE (a : Expr) : Expr := .mul a a
local infixl:65 " +ₑ " => addE
local infixl:65 " -ₑ " => subE
local infixl:70 " *ₑ " => mulE
local infixl:70 " /ₑ " => divE
def p2DiscriminantExpr : Expr := (sqE Certificates.Continuation.P5EndpointGraphs.atomA -ₑ .const 4 *ₑ Certificates.Continuation.P5EndpointGraphs.atomB)
private def rootE : Expr := .var 1
private def xE : Expr := (.neg Certificates.Continuation.P5EndpointGraphs.atomA -ₑ rootE) *ₑ .const (1/2)
private def yE : Expr := (.neg Certificates.Continuation.P5EndpointGraphs.atomA +ₑ rootE) *ₑ .const (1/2)
private def hE : Expr := Certificates.Continuation.P5EndpointGraphs.G -ₑ .const 1
private def probabilityE : Expr := (Certificates.Continuation.P5EndpointGraphs.meanCosine -ₑ xE) /ₑ (yE -ₑ xE)

def p2LiftExpr : Fin 7 → Expr := ![
  (Certificates.Continuation.P5EndpointGraphs.u -ₑ .const (1/2)) /ₑ hE,
  (xE +ₑ .const (1/2)) /ₑ hE,yE,probabilityE /ₑ hE,
  Certificates.Continuation.P5EndpointGraphs.d /ₑ hE,Certificates.Continuation.P5EndpointGraphs.W,.const 1 -ₑ Certificates.Continuation.P5EndpointGraphs.W]

def p2ParameterInterval : IntervalRat :=
  ⟨16989316152/10000000000,16989316153/10000000000,by norm_num⟩

noncomputable section

theorem p2LiftExpr_eval {z : ℝ} (hz : z∈P2.parameterInterval) (ρ : ℕ → ℝ)
    (hρ : ρ 0=z) (hr : ρ 1=Real.sqrt (P2.atomA z^2-4*P2.atomB z)) (i : Fin 7) : Expr.eval ρ (p2LiftExpr i)=p2Lift z i := by
  have he {f : ℝ → ℝ} (code : P2.RationalCode P2.parameterInterval f) :
      Expr.eval ρ code.expression=f z := by
    rw [code.expression_eval ρ (by rwa [hρ]),hρ]
  fin_cases i <;>
    norm_num [p2LiftExpr,Expr.eval,addE,mulE,subE,divE,sqE,rootE,xE,yE,hE,probabilityE,he,hr,Certificates.Continuation.P5EndpointGraphs.G_exact,Certificates.Continuation.P5EndpointGraphs.u_exact,Certificates.Continuation.P5EndpointGraphs.atomA_exact,Certificates.Continuation.P5EndpointGraphs.atomB_exact,Certificates.Continuation.P5EndpointGraphs.meanCosine_exact,Certificates.Continuation.P5EndpointGraphs.d_exact,Certificates.Continuation.P5EndpointGraphs.W_exact,
      p2Lift,P2.x,P2.y,P2.p,div_eq_mul_inv,sub_eq_add_neg,pow_two]

theorem p2DiscriminantExpr_eval {z : ℝ} (hz : z∈P2.parameterInterval) (ρ : ℕ → ℝ)
    (hρ : ρ 0=z) : Expr.eval ρ p2DiscriminantExpr=P2.atomA z^2-4*P2.atomB z := by
  have ha := P2.atomACode.expression_eval ρ (show ρ 0∈P2.parameterInterval by rwa [hρ])
  have hb := P2.atomBCode.expression_eval ρ (show ρ 0∈P2.parameterInterval by rwa [hρ])
  rw [hρ] at ha hb
  simp only [p2DiscriminantExpr,sqE,subE,mulE,Expr.eval,
    Certificates.Continuation.P5EndpointGraphs.atomA_exact,
    Certificates.Continuation.P5EndpointGraphs.atomB_exact]
  rw [ha,hb]
  norm_num
  ring

/-- The independently isolated root lies in the exact graph evaluation domain. -/
theorem zetaA_mem_p2ParameterInterval : P2.zetaA∈p2ParameterInterval := by
  norm_num [IntervalRat.mem_def,p2ParameterInterval]
  constructor <;> linarith [P2.zetaA_fine_bounds.1,P2.zetaA_fine_bounds.2]

end
end polyak.Boundary.P5
