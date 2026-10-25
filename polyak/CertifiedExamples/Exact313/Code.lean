import polyak.CertifiedExamples.Exact313.Source

/-! Executable polynomial and trigonometric code for the fixed source equation.
The only input parameter is π, retained as a real parameter to use the globally
smooth AD fragment; division has already been cleared from the source. -/
namespace polyak.CertifiedExamples.Exact313
open LeanCert.Core LeanCert.Engine Numerics.Parametric
namespace Code

def cosine (n : ℚ) : Expr := .cos (.mul (.const (n/13)) (.var 0))
def numerator (r c : Expr) : Expr :=
  .mul (.add (.const 1) c)
    (.sub (.const 1) (.mul r (.sub (.mul (.const 8) (.pow c 3)) (.mul (.const 4) c))))
def denominator (r c : Expr) : Expr :=
  .add (.const 1) (.mul (.mul (.mul (.const 8) r) (.pow c 2)) (.add (.const 1) c))
def numeratorD (r c : Expr) : Expr :=
  .sub (.const 1) (.mul r (.sub (.sub (.add (.mul (.const 32) (.pow c 3))
    (.mul (.const 24) (.pow c 2))) (.mul (.const 8) c)) (.const 4)))
def denominatorD (r c : Expr) : Expr :=
  .mul (.mul (.mul (.const 8) r) c) (.add (.const 2) (.mul (.const 3) c))
def derivativeNumerator (r c : Expr) : Expr :=
  .sub (.mul (numeratorD r c) (denominator r c))
    (.mul (numerator r c) (denominatorD r c))
def compatibility (r : Expr) : Expr :=
  let u := cosine 6
  let v := cosine 4
  .sub (.mul (.sub u v)
    (.add (.mul (derivativeNumerator r u) (.pow (denominator r v) 2))
      (.mul (derivativeNumerator r v) (.pow (denominator r u) 2))))
    (.mul (.mul (.mul (.const 2)
      (.sub (.mul (numerator r u) (denominator r v))
        (.mul (numerator r v) (denominator r u)))) (denominator r u)) (denominator r v))
def equations : Fin 1 → Expr := ![compatibility (.var 1)]

theorem supported : ∀i,ADSupported (equations i) := by
  intro i
  apply (Expr.checkADSupported_eq_true_iff _).mp
  fin_cases i
  rfl

noncomputable section

theorem eval_compatibility (r : ℝ) :
    system equations Real.pi ![r] 0=Exact313.compatibility r := by
  simp only [system,eval,evalFin,equations,compatibility,
    numerator,denominator,numeratorD,denominatorD,derivativeNumerator,cosine,
    Expr.eval_add,Expr.eval_mul,Expr.eval_sub,Expr.eval_pow,Expr.eval_cos,Expr.eval_const,
    Expr.eval_var,finEnv,embed,Fin.cons_zero,Fin.isValue,
    Matrix.cons_val_fin_one,Fin.zero_eta]
  norm_num [Exact313.compatibility,Exact313.numerator,Exact313.denominator,
    Exact313.numeratorD,Exact313.denominatorD,Exact313.derivativeNumerator,
    c₁,c₂,u,v]
  ring

end
end Code
end polyak.CertifiedExamples.Exact313
