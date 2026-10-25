import polyak.CertifiedExamples.Plateaus.Coordinates

/-! The adjugate and normalized kernels are reflected from fixed formulae.
The archive cannot substitute a different kernel or mathematical graph. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open chebyshev2.Numerics Matrix

def matrixVariables (d : ℕ) : Fin d → Fin d → E (d*d) := fun i j =>
  .variable (finProdFinEquiv (i,j))

def matrixPoint {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : Fin (d*d) → ℝ :=
  fun z => M (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2

theorem matrixVariables_value {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    (matrixVariables d i j).value (matrixPoint M)=M i j := by
  simp only [matrixVariables,matrixPoint,IntervalExpr.value,Equiv.symm_apply_apply]

theorem matrixVariables_values {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.of (fun i j=>(matrixVariables d i j).value (matrixPoint M))=M := by
  ext i j
  exact matrixVariables_value M i j

def adj2Expr {d : ℕ} (m : Fin 2 → Fin 2 → E d) : Fin 2 → Fin 2 → E d :=
  ![![m 1 1,.neg (m 0 1)],![.neg (m 1 0),m 0 0]]

def adj3Expr {d : ℕ} (m : Fin 3 → Fin 3 → E d) : Fin 3 → Fin 3 → E d :=
  ![![minus (times (m 1 1) (m 2 2)) (times (m 1 2) (m 2 1)),
      minus (times (m 0 2) (m 2 1)) (times (m 0 1) (m 2 2)),
      minus (times (m 0 1) (m 1 2)) (times (m 0 2) (m 1 1))],
    ![minus (times (m 1 2) (m 2 0)) (times (m 1 0) (m 2 2)),
      minus (times (m 0 0) (m 2 2)) (times (m 0 2) (m 2 0)),
      minus (times (m 0 2) (m 1 0)) (times (m 0 0) (m 1 2))],
    ![minus (times (m 1 0) (m 2 1)) (times (m 1 1) (m 2 0)),
      minus (times (m 0 1) (m 2 0)) (times (m 0 0) (m 2 1)),
      minus (times (m 0 0) (m 1 1)) (times (m 0 1) (m 1 0))]]

theorem adj2Expr_value {d : ℕ} (m : Fin 2 → Fin 2 → E d) (v : Fin d → ℝ)
    (i j : Fin 2) :
    (adj2Expr m i j).value v=(Matrix.of (fun r c=>(m r c).value v)).adjugate i j := by
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [adj2Expr,IntervalExpr.value]

theorem adj3Expr_value {d : ℕ} (m : Fin 3 → Fin 3 → E d) (v : Fin d → ℝ)
    (i j : Fin 3) :
    (adj3Expr m i j).value v=(Matrix.of (fun r c=>(m r c).value v)).adjugate i j := by
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp [adj3Expr,minus,times,IntervalExpr.value] <;> ring

def normalized2Expr {d : ℕ} (v : Fin 2 → E d) (i : Fin 2) : E d :=
  divideE (v i) (plus (v 0) (v 1))

def normalized3Expr {d : ℕ} (v : Fin 3 → E d) (i : Fin 3) : E d :=
  divideE (v i) (plus (plus (v 0) (v 1)) (v 2))

theorem normalized2Expr_value {d : ℕ} (u : Fin 2 → E d) (v : Fin d → ℝ)
    (i : Fin 2) : (normalized2Expr u i).value v=
      normalizeVector (fun j=>(u j).value v) i := by
  simp only [normalized2Expr,divideE,plus,IntervalExpr.value,normalizeVector,
    Fin.sum_univ_two,div_eq_mul_inv]

theorem normalized3Expr_value {d : ℕ} (u : Fin 3 → E d) (v : Fin d → ℝ)
    (i : Fin 3) : (normalized3Expr u i).value v=
      normalizeVector (fun j=>(u j).value v) i := by
  simp only [normalized3Expr,divideE,plus,IntervalExpr.value,normalizeVector,
    Fin.sum_univ_three,div_eq_mul_inv]

def left2Expr {d : ℕ} (m : Fin 2 → Fin 2 → E d) : Fin 2 → E d :=
  normalized2Expr (fun i=>adj2Expr m 0 i)

def right2Expr {d : ℕ} (m : Fin 2 → Fin 2 → E d) : Fin 2 → E d :=
  normalized2Expr (fun i=>adj2Expr m i 0)

def left3Expr {d : ℕ} (m : Fin 3 → Fin 3 → E d) : Fin 3 → E d :=
  normalized3Expr (fun i=>adj3Expr m 0 i)

def right3Expr {d : ℕ} (m : Fin 3 → Fin 3 → E d) : Fin 3 → E d :=
  normalized3Expr (fun i=>adj3Expr m i 0)

theorem left2Expr_value {d : ℕ} (m : Fin 2 → Fin 2 → E d) (v : Fin d → ℝ) (i : Fin 2) :
    (left2Expr m i).value v=positiveDual (Matrix.of (fun r c=>(m r c).value v)) 0 i := by
  rw [left2Expr,normalized2Expr_value]
  unfold positiveDual
  congr 1
  funext j
  exact adj2Expr_value m v 0 j

theorem right2Expr_value {d : ℕ} (m : Fin 2 → Fin 2 → E d) (v : Fin d → ℝ) (i : Fin 2) :
    (right2Expr m i).value v=positivePrimal (Matrix.of (fun r c=>(m r c).value v)) 0 i := by
  rw [right2Expr,normalized2Expr_value]
  unfold positivePrimal
  congr 1
  funext j
  exact adj2Expr_value m v j 0

theorem left3Expr_value {d : ℕ} (m : Fin 3 → Fin 3 → E d) (v : Fin d → ℝ) (i : Fin 3) :
    (left3Expr m i).value v=positiveDual (Matrix.of (fun r c=>(m r c).value v)) 0 i := by
  rw [left3Expr,normalized3Expr_value]
  unfold positiveDual
  congr 1
  funext j
  exact adj3Expr_value m v 0 j

theorem right3Expr_value {d : ℕ} (m : Fin 3 → Fin 3 → E d) (v : Fin d → ℝ) (i : Fin 3) :
    (right3Expr m i).value v=positivePrimal (Matrix.of (fun r c=>(m r c).value v)) 0 i := by
  rw [right3Expr,normalized3Expr_value]
  unfold positivePrimal
  congr 1
  funext j
  exact adj3Expr_value m v j 0

def moments2Expr {d : ℕ} (m : Fin 2 → Fin 2 → E d) (t : Fin 2 → E d) (i : Fin 2) : E d :=
  divideE (plus (times (adj2Expr m i 0) (t 0)) (times (adj2Expr m i 1) (t 1)))
    (det2Expr m)

def moments3Expr {d : ℕ} (m : Fin 3 → Fin 3 → E d) (t : Fin 3 → E d) (i : Fin 3) : E d :=
  divideE (plus (plus (times (adj3Expr m i 0) (t 0)) (times (adj3Expr m i 1) (t 1)))
    (times (adj3Expr m i 2) (t 2))) (det3Expr m)

theorem moments2Expr_value {d : ℕ} (m : Fin 2 → Fin 2 → E d) (t : Fin 2 → E d)
    (v : Fin d → ℝ) (i : Fin 2) : (moments2Expr m t i).value v=
      slopeMoments (Matrix.of (fun r c=>(m r c).value v)) (fun j=>(t j).value v) i := by
  simp only [moments2Expr,divideE,plus,times,IntervalExpr.value,adj2Expr_value,
    det2Expr_value,slopeMoments,Matrix.mulVec,dotProduct,Fin.sum_univ_two,div_eq_mul_inv]

theorem moments3Expr_value {d : ℕ} (m : Fin 3 → Fin 3 → E d) (t : Fin 3 → E d)
    (v : Fin d → ℝ) (i : Fin 3) : (moments3Expr m t i).value v=
      slopeMoments (Matrix.of (fun r c=>(m r c).value v)) (fun j=>(t j).value v) i := by
  simp only [moments3Expr,divideE,plus,times,IntervalExpr.value,adj3Expr_value,
    det3Expr_value,slopeMoments,Matrix.mulVec,dotProduct,Fin.sum_univ_three,div_eq_mul_inv]

end polyak.CertifiedExamples.Plateaus
