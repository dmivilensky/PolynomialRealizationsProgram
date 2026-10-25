import polyak.CertifiedExamples.Plateaus.CoordinateCode

/-! Independent finite arithmetic sources for inactive primal residues and the
strict minimizer moment. -/
namespace polyak.CertifiedExamples.Plateaus
open chebyshev2.Numerics

def primalLag2Expr {d:ℕ} (X:Fin 3→E d) (c p:Fin 2→E d) (n:ℤ) : E d :=
  plus (times (p 0) (coordinateCodeExpr X n 0 (c 0)))
    (times (p 1) (coordinateCodeExpr X n 0 (c 1)))

def primalLag3Expr {d:ℕ} (X:Fin 3→E d) (c p:Fin 3→E d) (n:ℤ) : E d :=
  plus (plus (times (p 0) (coordinateCodeExpr X n 0 (c 0)))
    (times (p 1) (coordinateCodeExpr X n 0 (c 1))))
    (times (p 2) (coordinateCodeExpr X n 0 (c 2)))

def primalMin2Expr {d:ℕ} (X:Fin 3→E d) (c p:Fin 2→E d) : E d :=
  plus (times (p 0) (coefficientValueExpr X (c 0)))
    (times (p 1) (coefficientValueExpr X (c 1)))

def primalMin3Expr {d:ℕ} (X:Fin 3→E d) (c p:Fin 3→E d) : E d :=
  plus (plus (times (p 0) (coefficientValueExpr X (c 0)))
    (times (p 1) (coefficientValueExpr X (c 1))))
    (times (p 2) (coefficientValueExpr X (c 2)))

noncomputable section
open scoped BigOperators

theorem primalLag2Expr_value {d:ℕ} (X:Fin 3→E d) (c p:Fin 2→E d) (n:ℤ) (v:Fin d→ℝ) :
    (primalLag2Expr X c p n).value v=
      ∑i,(p i).value v*coordinateLag (fun j=>(X j).value v) n ((c i).value v) := by
  simp only [primalLag2Expr,plus,times,IntervalExpr.value,coordinateCodeExpr_value,
    coordinateCodeValue_zero,Fin.sum_univ_two]

theorem primalLag3Expr_value {d:ℕ} (X:Fin 3→E d) (c p:Fin 3→E d) (n:ℤ) (v:Fin d→ℝ) :
    (primalLag3Expr X c p n).value v=
      ∑i,(p i).value v*coordinateLag (fun j=>(X j).value v) n ((c i).value v) := by
  simp only [primalLag3Expr,plus,times,IntervalExpr.value,coordinateCodeExpr_value,
    coordinateCodeValue_zero,Fin.sum_univ_three]

theorem primalMin2Expr_value {d:ℕ} (X:Fin 3→E d) (c p:Fin 2→E d) (v:Fin d→ℝ) :
    (primalMin2Expr X c p).value v=
      ∑i,(p i).value v*coefficientValue (fun j=>(X j).value v) ((c i).value v) := by
  simp only [primalMin2Expr,plus,times,IntervalExpr.value,coefficientValueExpr_value,Fin.sum_univ_two]

theorem primalMin3Expr_value {d:ℕ} (X:Fin 3→E d) (c p:Fin 3→E d) (v:Fin d→ℝ) :
    (primalMin3Expr X c p).value v=
      ∑i,(p i).value v*coefficientValue (fun j=>(X j).value v) ((c i).value v) := by
  simp only [primalMin3Expr,plus,times,IntervalExpr.value,coefficientValueExpr_value,Fin.sum_univ_three]

end
end polyak.CertifiedExamples.Plateaus
