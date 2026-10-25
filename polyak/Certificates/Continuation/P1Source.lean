import polyak.Boundary.P1.Source
import LeanCert.Engine.RootFinding.Krawczyk
import polyak.Numerics.KernelDecide
import polyak.Numerics.Parametric.Basic

/-! Article: (p1blowup), source-linked executable P1 continuation equations. -/
namespace polyak.Certificates.Continuation.P1
open LeanCert.Core LeanCert.Engine

/-- Exact executable divided P1 equation 0. -/
def F0 : Expr := (.add (.add (.add (.add (.const ((-1/2))) (.add (.mul (.const (4)) (.var 1)) (.mul (.const (1)) (.var 0)))) (.add (.mul (.const ((-1/4))) (.mul (.var 0) (.var 0))) (.add (.mul (.mul (.const (1)) (.var 0)) (.mul (.var 0) (.var 2))) (.mul (.mul (.const (2)) (.var 0)) (.mul (.var 0) (.mul (.var 2) (.var 2))))))) (.add (.add (.mul (.mul (.const (-2)) (.var 0)) (.mul (.var 0) (.var 1))) (.add (.mul (.mul (.const (2)) (.var 0)) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.mul (.mul (.const ((-3/4))) (.var 0)) (.mul (.var 0) (.mul (.var 0) (.var 2)))))) (.add (.add (.mul (.mul (.const (-2)) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.mul (.mul (.const (1)) (.var 0)) (.mul (.var 0) (.mul (.var 0) (.var 1))))) (.add (.mul (.mul (.const (2)) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 1) (.var 2)))) (.mul (.mul (.const (1)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))))))) (.add (.add (.add (.mul (.mul (.const (-1)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))) (.add (.mul (.mul (.mul (.const (-1)) (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2)))) (.mul (.mul (.mul (.const (1)) (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.mul (.var 2) (.var 2))))))) (.add (.mul (.mul (.mul (.const (-2)) (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 2))))) (.add (.mul (.mul (.mul (.const (1)) (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 1) (.var 2))))) (.mul (.mul (.mul (.const ((1/4))) (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.mul (.var 2) (.var 2)))))))) (.add (.add (.mul (.mul (.mul (.const (-2)) (.var 0)) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.mul (.var 2) (.var 2))))) (.add (.mul (.mul (.mul (.const (2)) (.var 0)) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 2))))) (.mul (.mul (.mul (.const (1)) (.var 0)) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 0) (.mul (.var 0) (.var 0))) (.mul (.var 2) (.mul (.var 2) (.var 2))))))) (.add (.add (.mul (.mul (.mul (.const (-1)) (.var 0)) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 0) (.mul (.var 0) (.var 0))) (.mul (.var 1) (.mul (.var 2) (.var 2))))) (.mul (.mul (.mul (.const (1)) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 0) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 2) (.var 2)))))) (.add (.mul (.mul (.mul (.const (-2)) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 0) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 2))))) (.mul (.mul (.mul (.const (1)) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 0) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))))))))))

/-- Exact bridge to the independent P1 source, valid also at z=0. -/
theorem eval_F0 (z : Fin 3 → ℝ) :
    evalFin F0 z = Boundary.P1.regularEquation0 (z 0) (z 1) (z 2) := by
  norm_num [F0,evalFin,finEnv,Expr.eval,Boundary.P1.regularEquation0,
    Boundary.P1.uLinear,Boundary.P1.gapLinear,Boundary.P1.atomProductLinear,
    Boundary.P1.contactQuadratic,Boundary.P1.branchU]
  ring

/-- Exact executable divided P1 equation 1. -/
def F1 : Expr := (.add (.add (.add (.add (.const (1)) (.mul (.const (4)) (.var 2))) (.add (.mul (.const ((-3/4))) (.var 0)) (.mul (.const (-4)) (.mul (.var 0) (.var 2))))) (.add (.add (.mul (.const (2)) (.mul (.var 0) (.var 1))) (.mul (.mul (.const (1)) (.var 0)) (.mul (.var 0) (.var 1)))) (.add (.mul (.mul (.const (-2)) (.var 0)) (.mul (.var 0) (.mul (.var 0) (.var 2)))) (.add (.mul (.mul (.const (3)) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.mul (.mul (.const (-4)) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 1) (.var 2)))))))) (.add (.add (.add (.mul (.mul (.const (1)) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.mul (.mul (.const ((1/2))) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 0) (.var 2))))) (.add (.mul (.mul (.const (-6)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2)))) (.mul (.mul (.const (4)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))))) (.add (.add (.mul (.mul (.mul (.const (3)) (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2)))) (.mul (.mul (.mul (.const (-2)) (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))))) (.add (.mul (.mul (.mul (.const (4)) (.var 0)) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.mul (.var 2) (.var 2))))) (.add (.mul (.mul (.mul (.const (-6)) (.var 0)) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 2))))) (.mul (.mul (.mul (.const (2)) (.var 0)) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 1) (.var 2))))))))))

/-- Exact bridge to the independent P1 source, valid also at z=0. -/
theorem eval_F1 (z : Fin 3 → ℝ) :
    evalFin F1 z = Boundary.P1.regularEquation1 (z 0) (z 1) (z 2) := by
  norm_num [F1,evalFin,finEnv,Expr.eval,Boundary.P1.regularEquation1,
    Boundary.P1.uLinear,Boundary.P1.gapLinear,Boundary.P1.atomProductLinear,
    Boundary.P1.contactQuadratic,Boundary.P1.branchU]
  ring

/-- The two divided equations with parameter first. -/
def system : Fin 2 → Expr := ![F0,F1]

/-- All expression operations admit verified automatic differentiation. -/
theorem check_supported : ∀ i, (system i).checkADSupported = true := by kernel_decide

/-- Source system equality, preserving the parameter/unknown ordering. -/
theorem source_system (z : ℝ) (x : Boundary.P1.Coordinates) :
    Numerics.Parametric.system system z x = Boundary.P1.regularSystem (z,x) := by
  ext i
  fin_cases i
  · change evalFin F0 (Fin.cons z x) = _
    exact eval_F0 (Fin.cons z x)
  · change evalFin F1 (Fin.cons z x) = _
    exact eval_F1 (Fin.cons z x)

end polyak.Certificates.Continuation.P1
