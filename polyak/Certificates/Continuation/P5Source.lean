import polyak.Boundary.P5.System
import LeanCert.Engine.RootFinding.Krawczyk
import polyak.Numerics.KernelDecide
import polyak.Numerics.Parametric.Basic

/-!
Article: (blowup), executable central equations for parameter-dependent checks.
Use: variable 0 is h; variables 1..7 are A,B,y,P,D,w2,w3.
Proof: every expression chunk equals the already source-linked polynomial chunk.
No interval outcome or external verification report is a mathematical premise.
-/
namespace polyak.Certificates.Continuation.P5
open LeanCert.Core LeanCert.Engine

/-- Exact executable coefficient chunk 0 of equation 0. -/
def F0Part0 : Expr := (.add (.add (.add (.add (.add (.const ((1/2))) (.mul (.var 5) (.const (1)))) (.mul (.var 4) (.const ((-1/4))))) (.mul (.var 3) (.add (.mul (.var 4) (.const ((-3/4)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (1)))))))) (.mul (.var 1) (.const (-3)))) (.mul (.var 0) (.add (.add (.add (.mul (.var 4) (.const ((1/4)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-1)))))) (.mul (.var 2) (.add (.const (1)) (.mul (.var 2) (.const ((-3/2))))))) (.mul (.var 1) (.add (.const (-1)) (.mul (.var 3) (.mul (.var 4) (.const (1)))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F0Part0 (z : Fin 8 → ℝ) :
    evalFin F0Part0 z = Boundary.P5.sourceEval z Certificates.P5.F0Part0 := by
  norm_num [F0Part0,evalFin,finEnv,Expr.eval,Certificates.P5.F0Part0,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 1 of equation 0. -/
def F0Part1 : Expr := (.mul (.var 0) (.add (.mul (.var 1) (.add (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (2))))) (.mul (.var 2) (.const (-1)))) (.mul (.var 1) (.const ((-3/2)))))) (.mul (.var 0) (.add (.mul (.var 2) (.add (.mul (.var 4) (.const (-1))) (.mul (.var 2) (.add (.add (.const (-1)) (.mul (.var 4) (.const ((3/2))))) (.mul (.var 2) (.const (1))))))) (.mul (.var 1) (.add (.mul (.var 2) (.add (.mul (.var 4) (.const (1))) (.mul (.var 2) (.const (2))))) (.mul (.var 1) (.add (.add (.const (-1)) (.mul (.var 4) (.const ((1/2))))) (.mul (.var 3) (.mul (.var 4) (.const (1))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F0Part1 (z : Fin 8 → ℝ) :
    evalFin F0Part1 z = Boundary.P5.sourceEval z Certificates.P5.F0Part1 := by
  norm_num [F0Part1,evalFin,finEnv,Expr.eval,Certificates.P5.F0Part1,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 2 of equation 0. -/
def F0Part2 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 2) (.const (1))))) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (1))) (.mul (.var 2) (.mul (.var 4) (.const (-1))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-2))))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.const (-1))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F0Part2 (z : Fin 8 → ℝ) :
    evalFin F0Part2 z = Boundary.P5.sourceEval z Certificates.P5.F0Part2 := by
  norm_num [F0Part2,evalFin,finEnv,Expr.eval,Certificates.P5.F0Part2,
    Boundary.P5.sourceEval]
  ring

/-- Executable regularized central equation 0. -/
def F0 : Expr := (.add F0Part0 (.add F0Part1 F0Part2))

/-- Exact source bridge for equation 0, including h=0. -/
theorem eval_F0 (z : Fin 8 → ℝ) :
    evalFin F0 z = Boundary.P5.sourceEval z Certificates.P5.F0 := by
  change (evalFin F0Part0 z + (evalFin F0Part1 z + evalFin F0Part2 z)) = _
  rw [eval_F0Part0, eval_F0Part1, eval_F0Part2]
  simp only [Certificates.P5.F0,map_add]
  ring

/-- Compact exact Horner form of equation 0. -/
def F0Horner : Expr := (.add (.add (.add (.add (.add (.const ((1/2))) (.mul (.var 5) (.const (1)))) (.mul (.var 4) (.const ((-1/4))))) (.mul (.var 3) (.add (.mul (.var 4) (.const ((-3/4)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (1)))))))) (.mul (.var 1) (.const (-3)))) (.mul (.var 0) (.add (.add (.add (.add (.mul (.var 4) (.const ((1/4)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-1)))))) (.mul (.var 2) (.add (.const (1)) (.mul (.var 2) (.const ((-3/2))))))) (.mul (.var 1) (.add (.add (.add (.const (-1)) (.mul (.var 3) (.add (.mul (.var 4) (.const (1))) (.mul (.var 3) (.mul (.var 4) (.const (2))))))) (.mul (.var 2) (.const (-1)))) (.mul (.var 1) (.const ((-3/2))))))) (.mul (.var 0) (.add (.add (.mul (.var 2) (.add (.mul (.var 4) (.const (-1))) (.mul (.var 2) (.add (.add (.const (-1)) (.mul (.var 4) (.const ((3/2))))) (.mul (.var 2) (.const (1))))))) (.mul (.var 1) (.add (.mul (.var 2) (.add (.mul (.var 4) (.const (1))) (.mul (.var 2) (.const (2))))) (.mul (.var 1) (.add (.add (.add (.const (-1)) (.mul (.var 4) (.const ((1/2))))) (.mul (.var 3) (.mul (.var 4) (.const (1))))) (.mul (.var 2) (.const (1)))))))) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (1))) (.mul (.var 2) (.mul (.var 4) (.const (-1))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-2))))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.const (-1))))))))))))))

theorem eval_F0Horner (z : Fin 8 → ℝ) : evalFin F0Horner z=evalFin F0 z := by
  norm_num [F0Horner,F0,F0Part0,F0Part1,F0Part2,evalFin,finEnv,Expr.eval]
  ring

/-- Exact executable coefficient chunk 0 of equation 1. -/
def F1Part0 : Expr := (.add (.add (.add (.add (.add (.add (.const (4)) (.mul (.var 5) (.const (-4)))) (.mul (.var 4) (.const (3)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (4))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-7))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-4))) (.mul (.var 3) (.mul (.var 4) (.const (4))))))))))) (.mul (.var 2) (.const (6)))) (.mul (.var 1) (.const (-6)))) (.mul (.var 0) (.add (.add (.const (2)) (.mul (.var 5) (.const (-4)))) (.mul (.var 4) (.const (2))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F1Part0 (z : Fin 8 → ℝ) :
    evalFin F1Part0 z = Boundary.P5.sourceEval z Certificates.P5.F1Part0 := by
  norm_num [F1Part0,evalFin,finEnv,Expr.eval,Certificates.P5.F1Part0,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 1 of equation 1. -/
def F1Part1 : Expr := (.mul (.var 0) (.add (.add (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-8))))) (.mul (.var 2) (.add (.add (.const (8)) (.mul (.var 4) (.const (-6)))) (.mul (.var 2) (.const (5)))))) (.mul (.var 1) (.add (.add (.add (.add (.const (-8)) (.mul (.var 4) (.const (2)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (8))) (.mul (.var 3) (.add (.mul (.var 4) (.const (4))) (.mul (.var 3) (.mul (.var 4) (.const (-8))))))))) (.mul (.var 2) (.const (-2)))) (.mul (.var 1) (.const (-3)))))) (.mul (.var 0) (.mul (.var 4) (.const (1))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F1Part1 (z : Fin 8 → ℝ) :
    evalFin F1Part1 z = Boundary.P5.sourceEval z Certificates.P5.F1Part1 := by
  norm_num [F1Part1,evalFin,finEnv,Expr.eval,Certificates.P5.F1Part1,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 2 of equation 1. -/
def F1Part2 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-4))))) (.mul (.var 2) (.add (.add (.const (4)) (.mul (.var 4) (.const (-8)))) (.mul (.var 2) (.add (.add (.const (-8)) (.mul (.var 4) (.const (-5)))) (.mul (.var 2) (.const (-12)))))))) (.mul (.var 1) (.add (.add (.const (-4)) (.mul (.var 2) (.add (.mul (.var 4) (.const (2))) (.mul (.var 2) (.const (16)))))) (.mul (.var 1) (.add (.add (.const (-8)) (.mul (.var 4) (.const (-1)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (4))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F1Part2 (z : Fin 8 → ℝ) :
    evalFin F1Part2 z = Boundary.P5.sourceEval z Certificates.P5.F1Part2 := by
  norm_num [F1Part2,evalFin,finEnv,Expr.eval,Certificates.P5.F1Part2,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 3 of equation 1. -/
def F1Part3 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 2) (.const (-4))))) (.mul (.var 0) (.add (.add (.mul (.var 2) (.add (.mul (.var 4) (.const (-4))) (.mul (.var 2) (.add (.add (.const (-4)) (.mul (.var 4) (.const (8)))) (.mul (.var 2) (.add (.mul (.var 4) (.const (12))) (.mul (.var 2) (.const (4))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-16))) (.mul (.var 2) (.const (-8)))))) (.mul (.var 1) (.add (.const (-4)) (.mul (.var 2) (.add (.mul (.var 4) (.const (4))) (.mul (.var 2) (.const (4)))))))))) (.mul (.var 0) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (4)))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F1Part3 (z : Fin 8 → ℝ) :
    evalFin F1Part3 z = Boundary.P5.sourceEval z Certificates.P5.F1Part3 := by
  norm_num [F1Part3,evalFin,finEnv,Expr.eval,Certificates.P5.F1Part3,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 4 of equation 1. -/
def F1Part4 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-4))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (8)))))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-4)))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F1Part4 (z : Fin 8 → ℝ) :
    evalFin F1Part4 z = Boundary.P5.sourceEval z Certificates.P5.F1Part4 := by
  norm_num [F1Part4,evalFin,finEnv,Expr.eval,Certificates.P5.F1Part4,
    Boundary.P5.sourceEval]
  ring

/-- Executable regularized central equation 1. -/
def F1 : Expr := (.add (.add F1Part0 F1Part1) (.add F1Part2 (.add F1Part3 F1Part4)))

/-- Exact source bridge for equation 1, including h=0. -/
theorem eval_F1 (z : Fin 8 → ℝ) :
    evalFin F1 z = Boundary.P5.sourceEval z Certificates.P5.F1 := by
  change ((evalFin F1Part0 z + evalFin F1Part1 z) + (evalFin F1Part2 z + (evalFin F1Part3 z + evalFin F1Part4 z))) = _
  rw [eval_F1Part0, eval_F1Part1, eval_F1Part2, eval_F1Part3, eval_F1Part4]
  simp only [Certificates.P5.F1,map_add]
  ring

/-- Compact exact Horner form of equation 1. -/
def F1Horner : Expr := (.add (.add (.add (.add (.add (.add (.const (4)) (.mul (.var 5) (.const (-4)))) (.mul (.var 4) (.const (3)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (4))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-7))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-4))) (.mul (.var 3) (.mul (.var 4) (.const (4))))))))))) (.mul (.var 2) (.const (6)))) (.mul (.var 1) (.const (-6)))) (.mul (.var 0) (.add (.add (.add (.add (.add (.add (.const (2)) (.mul (.var 5) (.const (-4)))) (.mul (.var 4) (.const (2)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-8)))))) (.mul (.var 2) (.add (.add (.const (8)) (.mul (.var 4) (.const (-6)))) (.mul (.var 2) (.const (5)))))) (.mul (.var 1) (.add (.add (.add (.add (.const (-8)) (.mul (.var 4) (.const (2)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (8))) (.mul (.var 3) (.add (.mul (.var 4) (.const (4))) (.mul (.var 3) (.mul (.var 4) (.const (-8))))))))) (.mul (.var 2) (.const (-2)))) (.mul (.var 1) (.const (-3)))))) (.mul (.var 0) (.add (.add (.add (.add (.mul (.var 4) (.const (1))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-4)))))) (.mul (.var 2) (.add (.add (.const (4)) (.mul (.var 4) (.const (-8)))) (.mul (.var 2) (.add (.add (.const (-8)) (.mul (.var 4) (.const (-5)))) (.mul (.var 2) (.const (-12)))))))) (.mul (.var 1) (.add (.add (.const (-4)) (.mul (.var 2) (.add (.mul (.var 4) (.const (2))) (.mul (.var 2) (.const (16)))))) (.mul (.var 1) (.add (.add (.add (.const (-8)) (.mul (.var 4) (.const (-1)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (4)))))) (.mul (.var 2) (.const (-4)))))))) (.mul (.var 0) (.add (.add (.mul (.var 2) (.add (.mul (.var 4) (.const (-4))) (.mul (.var 2) (.add (.add (.const (-4)) (.mul (.var 4) (.const (8)))) (.mul (.var 2) (.add (.mul (.var 4) (.const (12))) (.mul (.var 2) (.const (4))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-16))) (.mul (.var 2) (.const (-8)))))) (.mul (.var 1) (.add (.const (-4)) (.mul (.var 2) (.add (.mul (.var 4) (.const (4))) (.mul (.var 2) (.const (4)))))))))) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (4))) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-4)))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (8)))))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-4)))))))))))))))))

theorem eval_F1Horner (z : Fin 8 → ℝ) : evalFin F1Horner z=evalFin F1 z := by
  norm_num [F1Horner,F1,F1Part0,F1Part1,F1Part2,F1Part3,F1Part4,evalFin,finEnv,Expr.eval]
  ring

/-- Exact executable coefficient chunk 0 of equation 2. -/
def F2Part0 : Expr := (.add (.add (.add (.add (.add (.const (18)) (.mul (.var 5) (.const (-12)))) (.mul (.var 4) (.const (-1)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (9))) (.mul (.var 3) (.add (.mul (.var 4) (.const (16))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-24))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-16))) (.mul (.var 3) (.mul (.var 4) (.const (16))))))))))))) (.mul (.var 2) (.const (-12)))) (.mul (.var 0) (.add (.add (.const (24)) (.mul (.var 5) (.const (-32)))) (.mul (.var 4) (.const (9))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F2Part0 (z : Fin 8 → ℝ) :
    evalFin F2Part0 z = Boundary.P5.sourceEval z Certificates.P5.F2Part0 := by
  norm_num [F2Part0,evalFin,finEnv,Expr.eval,Certificates.P5.F2Part0,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 1 of equation 2. -/
def F2Part1 : Expr := (.mul (.var 0) (.add (.add (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-36))))) (.mul (.var 2) (.add (.add (.const (36)) (.mul (.var 4) (.const (12)))) (.mul (.var 2) (.const (8)))))) (.mul (.var 1) (.add (.add (.add (.const (-36)) (.mul (.var 4) (.const (-12)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-12))) (.mul (.var 3) (.add (.mul (.var 4) (.const (40))) (.mul (.var 3) (.add (.mul (.var 4) (.const (16))) (.mul (.var 3) (.mul (.var 4) (.const (-32))))))))))) (.mul (.var 2) (.const (-24)))))) (.mul (.var 0) (.const (8)))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F2Part1 (z : Fin 8 → ℝ) :
    evalFin F2Part1 z = Boundary.P5.sourceEval z Certificates.P5.F2Part1 := by
  norm_num [F2Part1,evalFin,finEnv,Expr.eval,Certificates.P5.F2Part1,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 2 of equation 2. -/
def F2Part2 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.add (.add (.add (.mul (.var 5) (.const (-16))) (.mul (.var 4) (.const (12)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-48)))))) (.mul (.var 2) (.add (.add (.const (48)) (.mul (.var 4) (.const (-36)))) (.mul (.var 2) (.add (.add (.const (-36)) (.mul (.var 4) (.const (-8)))) (.mul (.var 2) (.const (48)))))))) (.mul (.var 1) (.add (.add (.const (-48)) (.mul (.var 2) (.add (.mul (.var 4) (.const (24))) (.mul (.var 2) (.const (-32)))))) (.mul (.var 1) (.const (-36))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F2Part2 (z : Fin 8 → ℝ) :
    evalFin F2Part2 z = Boundary.P5.sourceEval z Certificates.P5.F2Part2 := by
  norm_num [F2Part2,evalFin,finEnv,Expr.eval,Certificates.P5.F2Part2,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 3 of equation 2. -/
def F2Part3 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.add (.mul (.var 4) (.const (-4))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-12))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (16)))))))))) (.mul (.var 0) (.add (.add (.add (.mul (.var 4) (.const (4))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-16)))))) (.mul (.var 2) (.add (.add (.const (16)) (.mul (.var 4) (.const (-48)))) (.mul (.var 2) (.add (.add (.const (-48)) (.mul (.var 4) (.const (36)))) (.mul (.var 2) (.add (.mul (.var 4) (.const (-48))) (.mul (.var 2) (.const (-56)))))))))) (.mul (.var 1) (.const (-16))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F2Part3 (z : Fin 8 → ℝ) :
    evalFin F2Part3 z = Boundary.P5.sourceEval z Certificates.P5.F2Part3 := by
  norm_num [F2Part3,evalFin,finEnv,Expr.eval,Certificates.P5.F2Part3,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 4 of equation 2. -/
def F2Part4 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (32))) (.mul (.var 2) (.const (80)))))) (.mul (.var 1) (.add (.const (-48)) (.mul (.var 2) (.mul (.var 2) (.const (-24)))))))) (.mul (.var 0) (.add (.mul (.var 2) (.add (.mul (.var 4) (.const (-16))) (.mul (.var 2) (.add (.add (.const (-16)) (.mul (.var 4) (.const (48)))) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (56))) (.mul (.var 2) (.const (16)))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-80))) (.mul (.var 2) (.const (-32))))))) (.mul (.var 1) (.const (-16)))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F2Part4 (z : Fin 8 → ℝ) :
    evalFin F2Part4 z = Boundary.P5.sourceEval z Certificates.P5.F2Part4 := by
  norm_num [F2Part4,evalFin,finEnv,Expr.eval,Certificates.P5.F2Part4,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 5 of equation 2. -/
def F2Part5 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (24))) (.mul (.var 2) (.const (16)))))))) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (16))) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-16))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (32))))))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-16))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F2Part5 (z : Fin 8 → ℝ) :
    evalFin F2Part5 z = Boundary.P5.sourceEval z Certificates.P5.F2Part5 := by
  norm_num [F2Part5,evalFin,finEnv,Expr.eval,Certificates.P5.F2Part5,
    Boundary.P5.sourceEval]
  ring

/-- Executable regularized central equation 2. -/
def F2 : Expr := (.add (.add F2Part0 (.add F2Part1 F2Part2)) (.add F2Part3 (.add F2Part4 F2Part5)))

/-- Exact source bridge for equation 2, including h=0. -/
theorem eval_F2 (z : Fin 8 → ℝ) :
    evalFin F2 z = Boundary.P5.sourceEval z Certificates.P5.F2 := by
  change ((evalFin F2Part0 z + (evalFin F2Part1 z + evalFin F2Part2 z)) + (evalFin F2Part3 z + (evalFin F2Part4 z + evalFin F2Part5 z))) = _
  rw [eval_F2Part0, eval_F2Part1, eval_F2Part2, eval_F2Part3, eval_F2Part4, eval_F2Part5]
  simp only [Certificates.P5.F2,map_add]
  ring

/-- Compact exact Horner form of equation 2. -/
def F2Horner : Expr := (.add (.add (.add (.add (.add (.const (18)) (.mul (.var 5) (.const (-12)))) (.mul (.var 4) (.const (-1)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (9))) (.mul (.var 3) (.add (.mul (.var 4) (.const (16))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-24))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-16))) (.mul (.var 3) (.mul (.var 4) (.const (16))))))))))))) (.mul (.var 2) (.const (-12)))) (.mul (.var 0) (.add (.add (.add (.add (.add (.add (.const (24)) (.mul (.var 5) (.const (-32)))) (.mul (.var 4) (.const (9)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-36)))))) (.mul (.var 2) (.add (.add (.const (36)) (.mul (.var 4) (.const (12)))) (.mul (.var 2) (.const (8)))))) (.mul (.var 1) (.add (.add (.add (.const (-36)) (.mul (.var 4) (.const (-12)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-12))) (.mul (.var 3) (.add (.mul (.var 4) (.const (40))) (.mul (.var 3) (.add (.mul (.var 4) (.const (16))) (.mul (.var 3) (.mul (.var 4) (.const (-32))))))))))) (.mul (.var 2) (.const (-24)))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.add (.const (8)) (.mul (.var 5) (.const (-16)))) (.mul (.var 4) (.const (12)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-48)))))) (.mul (.var 2) (.add (.add (.const (48)) (.mul (.var 4) (.const (-36)))) (.mul (.var 2) (.add (.add (.const (-36)) (.mul (.var 4) (.const (-8)))) (.mul (.var 2) (.const (48)))))))) (.mul (.var 1) (.add (.add (.const (-48)) (.mul (.var 2) (.add (.mul (.var 4) (.const (24))) (.mul (.var 2) (.const (-32)))))) (.mul (.var 1) (.add (.add (.const (-36)) (.mul (.var 4) (.const (-4)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-12))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (16)))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.mul (.var 4) (.const (4))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-16)))))) (.mul (.var 2) (.add (.add (.const (16)) (.mul (.var 4) (.const (-48)))) (.mul (.var 2) (.add (.add (.const (-48)) (.mul (.var 4) (.const (36)))) (.mul (.var 2) (.add (.mul (.var 4) (.const (-48))) (.mul (.var 2) (.const (-56)))))))))) (.mul (.var 1) (.add (.add (.const (-16)) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (32))) (.mul (.var 2) (.const (80))))))) (.mul (.var 1) (.add (.const (-48)) (.mul (.var 2) (.mul (.var 2) (.const (-24))))))))) (.mul (.var 0) (.add (.add (.mul (.var 2) (.add (.mul (.var 4) (.const (-16))) (.mul (.var 2) (.add (.add (.const (-16)) (.mul (.var 4) (.const (48)))) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (56))) (.mul (.var 2) (.const (16)))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-80))) (.mul (.var 2) (.const (-32))))))) (.mul (.var 1) (.add (.const (-16)) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (24))) (.mul (.var 2) (.const (16))))))))))) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (16))) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-16))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (32))))))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-16))))))))))))))))))))

theorem eval_F2Horner (z : Fin 8 → ℝ) : evalFin F2Horner z=evalFin F2 z := by
  norm_num [F2Horner,F2,F2Part0,F2Part1,F2Part2,F2Part3,F2Part4,F2Part5,evalFin,finEnv,Expr.eval]
  ring

/-- Exact executable coefficient chunk 0 of equation 3. -/
def F3Part0 : Expr := (.add (.add (.add (.add (.add (.const (50)) (.mul (.var 5) (.const (-20)))) (.mul (.var 4) (.const (7)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-15))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-56))) (.mul (.var 3) (.add (.mul (.var 4) (.const (80))) (.mul (.var 3) (.add (.mul (.var 4) (.const (112))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-128))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-64))) (.mul (.var 3) (.mul (.var 4) (.const (64))))))))))))))))) (.mul (.var 2) (.const (24)))) (.mul (.var 1) (.const (-12))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F3Part0 (z : Fin 8 → ℝ) :
    evalFin F3Part0 z = Boundary.P5.sourceEval z Certificates.P5.F3Part0 := by
  norm_num [F3Part0,evalFin,finEnv,Expr.eval,Certificates.P5.F3Part0,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 1 of equation 3. -/
def F3Part1 : Expr := (.mul (.var 0) (.add (.add (.add (.add (.add (.const (200)) (.mul (.var 5) (.const (-160)))) (.mul (.var 4) (.const (25)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-100)))))) (.mul (.var 2) (.add (.add (.const (100)) (.mul (.var 4) (.const (-24)))) (.mul (.var 2) (.const (50)))))) (.mul (.var 1) (.add (.add (.const (-100)) (.mul (.var 4) (.const (16)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (20))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-104))) (.mul (.var 3) (.mul (.var 4) (.const (-80))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F3Part1 (z : Fin 8 → ℝ) :
    evalFin F3Part1 z = Boundary.P5.sourceEval z Certificates.P5.F3Part1 := by
  norm_num [F3Part1,evalFin,finEnv,Expr.eval,Certificates.P5.F3Part1,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 2 of equation 3. -/
def F3Part2 : Expr := (.mul (.var 0) (.add (.mul (.var 1) (.add (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.mul (.var 4) (.const (224))) (.mul (.var 3) (.add (.mul (.var 4) (.const (64))) (.mul (.var 3) (.mul (.var 4) (.const (-128))))))))))) (.mul (.var 2) (.const (-4)))) (.mul (.var 1) (.const (-6))))) (.mul (.var 0) (.add (.add (.add (.add (.const (280)) (.mul (.var 5) (.const (-336)))) (.mul (.var 4) (.const (100)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-400)))))) (.mul (.var 2) (.add (.add (.const (400)) (.mul (.var 4) (.const (-100)))) (.mul (.var 2) (.const (-100)))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F3Part2 (z : Fin 8 → ℝ) :
    evalFin F3Part2 z = Boundary.P5.sourceEval z Certificates.P5.F3Part2 := by
  norm_num [F3Part2,evalFin,finEnv,Expr.eval,Certificates.P5.F3Part2,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 3 of equation 3. -/
def F3Part3 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-50))) (.mul (.var 2) (.const (-164)))))) (.mul (.var 1) (.add (.add (.const (-400)) (.mul (.var 2) (.add (.mul (.var 4) (.const (4))) (.mul (.var 2) (.const (152)))))) (.mul (.var 1) (.add (.add (.add (.const (-100)) (.mul (.var 4) (.const (2)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (20))) (.mul (.var 3) (.mul (.var 3) (.add (.mul (.var 4) (.const (-80))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (64))))))))))) (.mul (.var 2) (.const (-20)))))))) (.mul (.var 0) (.const (160))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F3Part3 (z : Fin 8 → ℝ) :
    evalFin F3Part3 z = Boundary.P5.sourceEval z Certificates.P5.F3Part3 := by
  norm_num [F3Part3,evalFin,finEnv,Expr.eval,Certificates.P5.F3Part3,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 4 of equation 3. -/
def F3Part4 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.add (.add (.add (.mul (.var 5) (.const (-256))) (.mul (.var 4) (.const (140)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-560)))))) (.mul (.var 2) (.add (.add (.const (560)) (.mul (.var 4) (.const (-400)))) (.mul (.var 2) (.add (.add (.const (-400)) (.mul (.var 4) (.const (100)))) (.mul (.var 2) (.add (.mul (.var 4) (.const (164))) (.mul (.var 2) (.const (-88)))))))))) (.mul (.var 1) (.add (.const (-560)) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-152))) (.mul (.var 2) (.const (-48))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F3Part4 (z : Fin 8 → ℝ) :
    evalFin F3Part4 z = Boundary.P5.sourceEval z Certificates.P5.F3Part4 := by
  norm_num [F3Part4,evalFin,finEnv,Expr.eval,Certificates.P5.F3Part4,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 5 of equation 3. -/
def F3Part5 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.add (.const (-400)) (.mul (.var 2) (.add (.mul (.var 4) (.const (20))) (.mul (.var 2) (.const (40)))))))) (.mul (.var 0) (.add (.add (.add (.add (.const (32)) (.mul (.var 5) (.const (-64)))) (.mul (.var 4) (.const (80)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-320)))))) (.mul (.var 2) (.add (.add (.const (320)) (.mul (.var 4) (.const (-560)))) (.mul (.var 2) (.add (.add (.const (-560)) (.mul (.var 4) (.const (400)))) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (88)))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F3Part5 (z : Fin 8 → ℝ) :
    evalFin F3Part5 z = Boundary.P5.sourceEval z Certificates.P5.F3Part5 := by
  norm_num [F3Part5,evalFin,finEnv,Expr.eval,Certificates.P5.F3Part5,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 6 of equation 3. -/
def F3Part6 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.const (400))))))) (.mul (.var 1) (.add (.add (.const (-320)) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (48))) (.mul (.var 2) (.const (-416)))))))) (.mul (.var 1) (.add (.const (-560)) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-40))) (.mul (.var 2) (.const (80))))))))))) (.mul (.var 0) (.add (.add (.mul (.var 4) (.const (16))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-64)))))) (.mul (.var 2) (.add (.add (.const (64)) (.mul (.var 4) (.const (-320)))) (.mul (.var 2) (.const (-320))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F3Part6 (z : Fin 8 → ℝ) :
    evalFin F3Part6 z = Boundary.P5.sourceEval z Certificates.P5.F3Part6 := by
  norm_num [F3Part6,evalFin,finEnv,Expr.eval,Certificates.P5.F3Part6,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 7 of equation 3. -/
def F3Part7 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (560))) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-400))) (.mul (.var 2) (.const (-288)))))))))) (.mul (.var 1) (.add (.add (.const (-64)) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (416))) (.mul (.var 2) (.const (448))))))))) (.mul (.var 1) (.add (.const (-320)) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-80))) (.mul (.var 2) (.const (-160)))))))))))) (.mul (.var 0) (.mul (.var 2) (.add (.mul (.var 4) (.const (-64))) (.mul (.var 2) (.add (.const (-64)) (.mul (.var 4) (.const (320))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F3Part7 (z : Fin 8 → ℝ) :
    evalFin F3Part7 z = Boundary.P5.sourceEval z Certificates.P5.F3Part7 := by
  norm_num [F3Part7,evalFin,finEnv,Expr.eval,Certificates.P5.F3Part7,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 8 of equation 3. -/
def F3Part8 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (288))) (.mul (.var 2) (.const (64)))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-448))) (.mul (.var 2) (.const (-128))))))))) (.mul (.var 1) (.add (.const (-64)) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (160))) (.mul (.var 2) (.const (64))))))))))))) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (64))) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-64))))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (128))))))))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-64))))))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F3Part8 (z : Fin 8 → ℝ) :
    evalFin F3Part8 z = Boundary.P5.sourceEval z Certificates.P5.F3Part8 := by
  norm_num [F3Part8,evalFin,finEnv,Expr.eval,Certificates.P5.F3Part8,
    Boundary.P5.sourceEval]
  ring

/-- Executable regularized central equation 3. -/
def F3 : Expr := (.add (.add (.add F3Part0 F3Part1) (.add F3Part2 F3Part3)) (.add (.add F3Part4 F3Part5) (.add F3Part6 (.add F3Part7 F3Part8))))

/-- Exact source bridge for equation 3, including h=0. -/
theorem eval_F3 (z : Fin 8 → ℝ) :
    evalFin F3 z = Boundary.P5.sourceEval z Certificates.P5.F3 := by
  change (((evalFin F3Part0 z + evalFin F3Part1 z) + (evalFin F3Part2 z + evalFin F3Part3 z)) + ((evalFin F3Part4 z + evalFin F3Part5 z) + (evalFin F3Part6 z + (evalFin F3Part7 z + evalFin F3Part8 z)))) = _
  rw [eval_F3Part0, eval_F3Part1, eval_F3Part2, eval_F3Part3, eval_F3Part4, eval_F3Part5, eval_F3Part6, eval_F3Part7, eval_F3Part8]
  simp only [Certificates.P5.F3,map_add]
  ring

/-- Compact exact Horner form of equation 3. -/
def F3Horner : Expr := (.add (.add (.add (.add (.add (.add (.const (50)) (.mul (.var 5) (.const (-20)))) (.mul (.var 4) (.const (7)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-15))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-56))) (.mul (.var 3) (.add (.mul (.var 4) (.const (80))) (.mul (.var 3) (.add (.mul (.var 4) (.const (112))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-128))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-64))) (.mul (.var 3) (.mul (.var 4) (.const (64))))))))))))))))) (.mul (.var 2) (.const (24)))) (.mul (.var 1) (.const (-12)))) (.mul (.var 0) (.add (.add (.add (.add (.add (.add (.const (200)) (.mul (.var 5) (.const (-160)))) (.mul (.var 4) (.const (25)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-100)))))) (.mul (.var 2) (.add (.add (.const (100)) (.mul (.var 4) (.const (-24)))) (.mul (.var 2) (.const (50)))))) (.mul (.var 1) (.add (.add (.add (.add (.const (-100)) (.mul (.var 4) (.const (16)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (20))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-104))) (.mul (.var 3) (.add (.mul (.var 4) (.const (-80))) (.mul (.var 3) (.add (.mul (.var 4) (.const (224))) (.mul (.var 3) (.add (.mul (.var 4) (.const (64))) (.mul (.var 3) (.mul (.var 4) (.const (-128))))))))))))))) (.mul (.var 2) (.const (-4)))) (.mul (.var 1) (.const (-6)))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.add (.const (280)) (.mul (.var 5) (.const (-336)))) (.mul (.var 4) (.const (100)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-400)))))) (.mul (.var 2) (.add (.add (.const (400)) (.mul (.var 4) (.const (-100)))) (.mul (.var 2) (.add (.add (.const (-100)) (.mul (.var 4) (.const (-50)))) (.mul (.var 2) (.const (-164)))))))) (.mul (.var 1) (.add (.add (.const (-400)) (.mul (.var 2) (.add (.mul (.var 4) (.const (4))) (.mul (.var 2) (.const (152)))))) (.mul (.var 1) (.add (.add (.add (.const (-100)) (.mul (.var 4) (.const (2)))) (.mul (.var 3) (.add (.mul (.var 4) (.const (20))) (.mul (.var 3) (.mul (.var 3) (.add (.mul (.var 4) (.const (-80))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (64))))))))))) (.mul (.var 2) (.const (-20)))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.add (.const (160)) (.mul (.var 5) (.const (-256)))) (.mul (.var 4) (.const (140)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-560)))))) (.mul (.var 2) (.add (.add (.const (560)) (.mul (.var 4) (.const (-400)))) (.mul (.var 2) (.add (.add (.const (-400)) (.mul (.var 4) (.const (100)))) (.mul (.var 2) (.add (.mul (.var 4) (.const (164))) (.mul (.var 2) (.const (-88)))))))))) (.mul (.var 1) (.add (.add (.const (-560)) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-152))) (.mul (.var 2) (.const (-48))))))) (.mul (.var 1) (.add (.const (-400)) (.mul (.var 2) (.add (.mul (.var 4) (.const (20))) (.mul (.var 2) (.const (40)))))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.add (.const (32)) (.mul (.var 5) (.const (-64)))) (.mul (.var 4) (.const (80)))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-320)))))) (.mul (.var 2) (.add (.add (.const (320)) (.mul (.var 4) (.const (-560)))) (.mul (.var 2) (.add (.add (.const (-560)) (.mul (.var 4) (.const (400)))) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (88))) (.mul (.var 2) (.const (400))))))))))) (.mul (.var 1) (.add (.add (.const (-320)) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (48))) (.mul (.var 2) (.const (-416)))))))) (.mul (.var 1) (.add (.const (-560)) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-40))) (.mul (.var 2) (.const (80))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.mul (.var 4) (.const (16))) (.mul (.var 3) (.mul (.var 3) (.mul (.var 4) (.const (-64)))))) (.mul (.var 2) (.add (.add (.const (64)) (.mul (.var 4) (.const (-320)))) (.mul (.var 2) (.add (.add (.const (-320)) (.mul (.var 4) (.const (560)))) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-400))) (.mul (.var 2) (.const (-288)))))))))))) (.mul (.var 1) (.add (.add (.const (-64)) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (416))) (.mul (.var 2) (.const (448))))))))) (.mul (.var 1) (.add (.const (-320)) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-80))) (.mul (.var 2) (.const (-160)))))))))))) (.mul (.var 0) (.add (.add (.mul (.var 2) (.add (.mul (.var 4) (.const (-64))) (.mul (.var 2) (.add (.add (.const (-64)) (.mul (.var 4) (.const (320)))) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (288))) (.mul (.var 2) (.const (64)))))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (-448))) (.mul (.var 2) (.const (-128))))))))) (.mul (.var 1) (.add (.const (-64)) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (160))) (.mul (.var 2) (.const (64))))))))))))) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 4) (.const (64))) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-64))))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (128))))))))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 4) (.const (-64))))))))))))))))))))))))))

theorem eval_F3Horner (z : Fin 8 → ℝ) : evalFin F3Horner z=evalFin F3 z := by
  norm_num [F3Horner,F3,F3Part0,F3Part1,F3Part2,F3Part3,F3Part4,F3Part5,F3Part6,F3Part7,F3Part8,evalFin,finEnv,Expr.eval]
  ring

/-- Exact executable coefficient chunk 0 of equation 4. -/
def F4Part0 : Expr := (.add (.add (.add (.const ((-3/2))) (.mul (.var 7) (.const ((13/2))))) (.mul (.var 6) (.const (-6)))) (.mul (.var 3) (.add (.add (.add (.const (21)) (.mul (.var 7) (.const (-16)))) (.mul (.var 6) (.const ((-129/4))))) (.mul (.var 3) (.add (.add (.add (.const (63)) (.mul (.var 7) (.const (-78)))) (.mul (.var 6) (.const (-48)))) (.mul (.var 3) (.add (.add (.const (-12)) (.mul (.var 7) (.const (12)))) (.mul (.var 6) (.const (27))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part0 (z : Fin 8 → ℝ) :
    evalFin F4Part0 z = Boundary.P5.sourceEval z Certificates.P5.F4Part0 := by
  norm_num [F4Part0,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part0,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 1 of equation 4. -/
def F4Part1 : Expr := (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (-96)) (.mul (.var 7) (.const (116)))) (.mul (.var 6) (.const (96)))) (.mul (.var 3) (.mul (.var 3) (.add (.add (.const (48)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (-48))))))))))) (.mul (.var 0) (.add (.add (.add (.const ((-83/2))) (.mul (.var 7) (.const ((93/2))))) (.mul (.var 6) (.const (-61)))) (.mul (.var 3) (.add (.add (.const (110)) (.mul (.var 7) (.const (-80)))) (.mul (.var 6) (.const (-230))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part1 (z : Fin 8 → ℝ) :
    evalFin F4Part1 z = Boundary.P5.sourceEval z Certificates.P5.F4Part1 := by
  norm_num [F4Part1,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part1,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 2 of equation 4. -/
def F4Part2 : Expr := (.mul (.var 0) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (291)) (.mul (.var 7) (.const (-366)))) (.mul (.var 6) (.const (-101)))) (.mul (.var 3) (.add (.add (.add (.const (-92)) (.mul (.var 7) (.const (112)))) (.mul (.var 6) (.const (252)))) (.mul (.var 3) (.add (.add (.add (.const (-304)) (.mul (.var 7) (.const (484)))) (.mul (.var 6) (.const (304)))) (.mul (.var 3) (.add (.add (.const (48)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (-48)))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part2 (z : Fin 8 → ℝ) :
    evalFin F4Part2 z = Boundary.P5.sourceEval z Certificates.P5.F4Part2 := by
  norm_num [F4Part2,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part2,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 3 of equation 4. -/
def F4Part3 : Expr := (.mul (.var 0) (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.const (176)) (.mul (.var 7) (.const (-176)))) (.mul (.var 6) (.const (-176)))))))))) (.mul (.var 1) (.add (.add (.add (.const (42)) (.mul (.var 7) (.const (18)))) (.mul (.var 6) (.const (18)))) (.mul (.var 3) (.add (.add (.add (.const (12)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (3)))) (.mul (.var 3) (.add (.add (.const (60)) (.mul (.var 7) (.const (-80)))) (.mul (.var 6) (.const (-90)))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part3 (z : Fin 8 → ℝ) :
    evalFin F4Part3 z = Boundary.P5.sourceEval z Certificates.P5.F4Part3 := by
  norm_num [F4Part3,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part3,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 4 of equation 4. -/
def F4Part4 : Expr := (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (120)) (.mul (.var 7) (.const (-160)))) (.mul (.var 6) (.const (-120)))) (.mul (.var 3) (.add (.add (.add (.const (-48)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (48)))) (.mul (.var 3) (.add (.add (.const (-96)) (.mul (.var 7) (.const (96)))) (.mul (.var 6) (.const (96)))))))))))) (.mul (.var 0) (.add (.add (.const (-354)) (.mul (.var 7) (.const (88)))) (.mul (.var 6) (.const (-182)))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part4 (z : Fin 8 → ℝ) :
    evalFin F4Part4 z = Boundary.P5.sourceEval z Certificates.P5.F4Part4 := by
  norm_num [F4Part4,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part4,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 5 of equation 4. -/
def F4Part5 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 3) (.add (.add (.add (.const (145)) (.mul (.var 7) (.const (-156)))) (.mul (.var 6) (.const (-589)))) (.mul (.var 3) (.add (.add (.add (.const (772)) (.mul (.var 7) (.const (-564)))) (.mul (.var 6) (.const (140)))) (.mul (.var 3) (.add (.add (.add (.const (-128)) (.mul (.var 7) (.const (308)))) (.mul (.var 6) (.const (720)))) (.mul (.var 3) (.add (.add (.const (-160)) (.mul (.var 7) (.const (656)))) (.mul (.var 6) (.const (160)))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part5 (z : Fin 8 → ℝ) :
    evalFin F4Part5 z = Boundary.P5.sourceEval z Certificates.P5.F4Part5 := by
  norm_num [F4Part5,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part5,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 6 of equation 4. -/
def F4Part6 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (176)) (.mul (.var 7) (.const (-176)))) (.mul (.var 6) (.const (-176)))) (.mul (.var 3) (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192))))))))))) (.mul (.var 1) (.add (.add (.add (.const (562)) (.mul (.var 7) (.const (98)))) (.mul (.var 6) (.const (108)))) (.mul (.var 3) (.add (.add (.const (320)) (.mul (.var 7) (.const (240)))) (.mul (.var 6) (.const (-160))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part6 (z : Fin 8 → ℝ) :
    evalFin F4Part6 z = Boundary.P5.sourceEval z Certificates.P5.F4Part6 := by
  norm_num [F4Part6,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part6,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 7 of equation 4. -/
def F4Part7 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (196)) (.mul (.var 7) (.const (-416)))) (.mul (.var 6) (.const (-516)))) (.mul (.var 3) (.add (.add (.add (.const (296)) (.mul (.var 7) (.const (-656)))) (.mul (.var 6) (.const (-296)))) (.mul (.var 3) (.add (.add (.add (.const (-272)) (.mul (.var 7) (.const (272)))) (.mul (.var 6) (.const (272)))) (.mul (.var 3) (.add (.add (.const (-352)) (.mul (.var 7) (.const (352)))) (.mul (.var 6) (.const (352)))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part7 (z : Fin 8 → ℝ) :
    evalFin F4Part7 z = Boundary.P5.sourceEval z Certificates.P5.F4Part7 := by
  norm_num [F4Part7,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part7,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 8 of equation 4. -/
def F4Part8 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.add (.add (.add (.const (18)) (.mul (.var 7) (.const (2)))) (.mul (.var 6) (.const (12)))) (.mul (.var 3) (.add (.add (.add (.const (-12)) (.mul (.var 7) (.const (32)))) (.mul (.var 6) (.const (27)))) (.mul (.var 3) (.add (.add (.add (.const (-12)) (.mul (.var 7) (.const (32)))) (.mul (.var 6) (.const (12)))) (.mul (.var 3) (.add (.add (.const (48)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (-48))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part8 (z : Fin 8 → ℝ) :
    evalFin F4Part8 z = Boundary.P5.sourceEval z Certificates.P5.F4Part8 := by
  norm_num [F4Part8,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part8,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 9 of equation 4. -/
def F4Part9 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.const (48)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (-48)))))))))) (.mul (.var 0) (.add (.add (.add (.const (-1178)) (.mul (.var 7) (.const (64)))) (.mul (.var 6) (.const (-222)))) (.mul (.var 3) (.add (.add (.add (.const (-96)) (.mul (.var 7) (.const (-128)))) (.mul (.var 6) (.const (-672)))) (.mul (.var 3) (.add (.add (.const (1760)) (.mul (.var 7) (.const (-356)))) (.mul (.var 6) (.const (448))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part9 (z : Fin 8 → ℝ) :
    evalFin F4Part9 z = Boundary.P5.sourceEval z Certificates.P5.F4Part9 := by
  norm_num [F4Part9,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part9,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 10 of equation 4. -/
def F4Part10 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (192)) (.mul (.var 7) (.const (304)))) (.mul (.var 6) (.const (832)))) (.mul (.var 3) (.add (.add (.add (.const (240)) (.mul (.var 7) (.const (352)))) (.mul (.var 6) (.const (-240)))) (.mul (.var 3) (.add (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192)))) (.mul (.var 3) (.add (.add (.const (64)) (.mul (.var 7) (.const (-64)))) (.mul (.var 6) (.const (-64))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part10 (z : Fin 8 → ℝ) :
    evalFin F4Part10 z = Boundary.P5.sourceEval z Certificates.P5.F4Part10 := by
  norm_num [F4Part10,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part10,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 11 of equation 4. -/
def F4Part11 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.add (.add (.const (2432)) (.mul (.var 7) (.const (176)))) (.mul (.var 6) (.const (256)))) (.mul (.var 3) (.add (.add (.add (.const (1300)) (.mul (.var 7) (.const (368)))) (.mul (.var 6) (.const (-708)))) (.mul (.var 3) (.add (.add (.add (.const (-88)) (.mul (.var 7) (.const (-768)))) (.mul (.var 6) (.const (-1096)))) (.mul (.var 3) (.add (.add (.const (-144)) (.mul (.var 7) (.const (-848)))) (.mul (.var 6) (.const (144))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part11 (z : Fin 8 → ℝ) :
    evalFin F4Part11 z = Boundary.P5.sourceEval z Certificates.P5.F4Part11 := by
  norm_num [F4Part11,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part11,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 12 of equation 4. -/
def F4Part12 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (-544)) (.mul (.var 7) (.const (544)))) (.mul (.var 6) (.const (544)))) (.mul (.var 3) (.add (.add (.const (-384)) (.mul (.var 7) (.const (384)))) (.mul (.var 6) (.const (384)))))))))) (.mul (.var 1) (.add (.add (.add (.const (258)) (.mul (.var 7) (.const (2)))) (.mul (.var 6) (.const (92)))) (.mul (.var 3) (.add (.add (.const (40)) (.mul (.var 7) (.const (160)))) (.mul (.var 6) (.const (120))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part12 (z : Fin 8 → ℝ) :
    evalFin F4Part12 z = Boundary.P5.sourceEval z Certificates.P5.F4Part12 := by
  norm_num [F4Part12,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part12,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 13 of equation 4. -/
def F4Part13 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (52)) (.mul (.var 7) (.const (128)))) (.mul (.var 6) (.const (-52)))) (.mul (.var 3) (.add (.add (.add (.const (224)) (.mul (.var 7) (.const (-224)))) (.mul (.var 6) (.const (-224)))) (.mul (.var 3) (.add (.add (.const (176)) (.mul (.var 7) (.const (-176)))) (.mul (.var 6) (.const (-176)))))))))))) (.mul (.var 0) (.add (.add (.const (-1864)) (.mul (.var 7) (.const (16)))) (.mul (.var 6) (.const (-120)))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part13 (z : Fin 8 → ℝ) :
    evalFin F4Part13 z = Boundary.P5.sourceEval z Certificates.P5.F4Part13 := by
  norm_num [F4Part13,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part13,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 14 of equation 4. -/
def F4Part14 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 3) (.add (.add (.add (.const (-328)) (.mul (.var 7) (.const (-36)))) (.mul (.var 6) (.const (-344)))) (.mul (.var 3) (.add (.add (.add (.const (2608)) (.mul (.var 7) (.const (-80)))) (.mul (.var 6) (.const (336)))) (.mul (.var 3) (.add (.add (.add (.const (496)) (.mul (.var 7) (.const (96)))) (.mul (.var 6) (.const (400)))) (.mul (.var 3) (.add (.add (.const (256)) (.mul (.var 7) (.const (64)))) (.mul (.var 6) (.const (-256)))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part14 (z : Fin 8 → ℝ) :
    evalFin F4Part14 z = Boundary.P5.sourceEval z Certificates.P5.F4Part14 := by
  norm_num [F4Part14,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part14,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 15 of equation 4. -/
def F4Part15 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.const (64)) (.mul (.var 7) (.const (-64)))) (.mul (.var 6) (.const (-64))))))))) (.mul (.var 1) (.add (.add (.add (.const (4984)) (.mul (.var 7) (.const (128)))) (.mul (.var 6) (.const (296)))) (.mul (.var 3) (.add (.add (.add (.const (2048)) (.mul (.var 7) (.const (224)))) (.mul (.var 6) (.const (-1024)))) (.mul (.var 3) (.add (.add (.const (-992)) (.mul (.var 7) (.const (-592)))) (.mul (.var 6) (.const (-1056))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part15 (z : Fin 8 → ℝ) :
    evalFin F4Part15 z = Boundary.P5.sourceEval z Certificates.P5.F4Part15 := by
  norm_num [F4Part15,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part15,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 16 of equation 4. -/
def F4Part16 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (-768)) (.mul (.var 7) (.const (-416)))) (.mul (.var 6) (.const (768)))) (.mul (.var 3) (.add (.add (.add (.const (-448)) (.mul (.var 7) (.const (448)))) (.mul (.var 6) (.const (448)))) (.mul (.var 3) (.add (.add (.const (-128)) (.mul (.var 7) (.const (128)))) (.mul (.var 6) (.const (128))))))))))) (.mul (.var 1) (.add (.add (.const (1256)) (.mul (.var 6) (.const (248)))) (.mul (.var 3) (.const (404)))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part16 (z : Fin 8 → ℝ) :
    evalFin F4Part16 z = Boundary.P5.sourceEval z Certificates.P5.F4Part16 := by
  norm_num [F4Part16,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part16,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 17 of equation 4. -/
def F4Part17 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 3) (.add (.add (.mul (.var 7) (.const (272))) (.mul (.var 6) (.const (188)))) (.mul (.var 3) (.add (.add (.add (.const (352)) (.mul (.var 7) (.const (144)))) (.mul (.var 6) (.const (-352)))) (.mul (.var 3) (.add (.add (.add (.const (368)) (.mul (.var 7) (.const (-368)))) (.mul (.var 6) (.const (-368)))) (.mul (.var 3) (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192))))))))))))) (.mul (.var 0) (.const (-1512))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part17 (z : Fin 8 → ℝ) :
    evalFin F4Part17 z = Boundary.P5.sourceEval z Certificates.P5.F4Part17 := by
  norm_num [F4Part17,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part17,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 18 of equation 4. -/
def F4Part18 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.add (.mul (.var 6) (.const (-24))) (.mul (.var 3) (.add (.add (.const (-224)) (.mul (.var 6) (.const (-64)))) (.mul (.var 3) (.add (.add (.const (2096)) (.mul (.var 6) (.const (80)))) (.mul (.var 3) (.add (.add (.const (320)) (.mul (.var 6) (.const (64)))) (.mul (.var 3) (.add (.const (64)) (.mul (.var 6) (.const (-64)))))))))))) (.mul (.var 1) (.add (.add (.const (5472)) (.mul (.var 7) (.const (32)))) (.mul (.var 6) (.const (160)))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part18 (z : Fin 8 → ℝ) :
    evalFin F4Part18 z = Boundary.P5.sourceEval z Certificates.P5.F4Part18 := by
  norm_num [F4Part18,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part18,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 19 of equation 4. -/
def F4Part19 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.add (.add (.add (.const (1504)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (-608)))) (.mul (.var 3) (.add (.add (.add (.const (-1344)) (.mul (.var 7) (.const (-160)))) (.mul (.var 6) (.const (-448)))) (.mul (.var 3) (.add (.add (.add (.const (-576)) (.mul (.var 7) (.const (-64)))) (.mul (.var 6) (.const (576)))) (.mul (.var 3) (.add (.add (.const (-128)) (.mul (.var 7) (.const (128)))) (.mul (.var 6) (.const (128)))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part19 (z : Fin 8 → ℝ) :
    evalFin F4Part19 z = Boundary.P5.sourceEval z Certificates.P5.F4Part19 := by
  norm_num [F4Part19,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part19,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 20 of equation 4. -/
def F4Part20 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.add (.add (.const (2936)) (.mul (.var 6) (.const (296)))) (.mul (.var 3) (.add (.add (.add (.const (896)) (.mul (.var 7) (.const (192)))) (.mul (.var 6) (.const (128)))) (.mul (.var 3) (.add (.add (.add (.const (544)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (-544)))) (.mul (.var 3) (.add (.add (.add (.const (256)) (.mul (.var 7) (.const (-256)))) (.mul (.var 6) (.const (-256)))) (.mul (.var 3) (.const (64)))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part20 (z : Fin 8 → ℝ) :
    evalFin F4Part20 z = Boundary.P5.sourceEval z Certificates.P5.F4Part20 := by
  norm_num [F4Part20,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part20,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 21 of equation 4. -/
def F4Part21 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.mul (.var 7) (.const (-64))) (.mul (.var 6) (.const (-64)))))))))) (.mul (.var 0) (.add (.add (.const (-608)) (.mul (.var 3) (.add (.const (-48)) (.mul (.var 3) (.add (.const (832)) (.mul (.var 3) (.const (64)))))))) (.mul (.var 1) (.add (.add (.const (3296)) (.mul (.var 6) (.const (32)))) (.mul (.var 3) (.add (.add (.const (512)) (.mul (.var 6) (.const (-128)))) (.mul (.var 3) (.add (.const (-704)) (.mul (.var 6) (.const (-64)))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part21 (z : Fin 8 → ℝ) :
    evalFin F4Part21 z = Boundary.P5.sourceEval z Certificates.P5.F4Part21 := by
  norm_num [F4Part21,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part21,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 22 of equation 4. -/
def F4Part22 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.const (-128)) (.mul (.var 6) (.const (128))))))) (.mul (.var 1) (.add (.add (.const (3680)) (.mul (.var 6) (.const (160)))) (.mul (.var 3) (.add (.add (.add (.const (864)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (32)))) (.mul (.var 3) (.add (.add (.const (320)) (.mul (.var 6) (.const (-320)))) (.mul (.var 3) (.add (.add (.const (64)) (.mul (.var 7) (.const (-64)))) (.mul (.var 6) (.const (-64)))))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part22 (z : Fin 8 → ℝ) :
    evalFin F4Part22 z = Boundary.P5.sourceEval z Certificates.P5.F4Part22 := by
  norm_num [F4Part22,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part22,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 23 of equation 4. -/
def F4Part23 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.add (.add (.const (-96)) (.mul (.var 3) (.mul (.var 3) (.const (128))))) (.mul (.var 1) (.add (.add (.const (1024)) (.mul (.var 3) (.add (.const (64)) (.mul (.var 3) (.const (-128)))))) (.mul (.var 1) (.add (.add (.const (2528)) (.mul (.var 6) (.const (32)))) (.mul (.var 3) (.add (.const (384)) (.mul (.var 3) (.add (.const (64)) (.mul (.var 6) (.const (-64)))))))))))) (.mul (.var 0) (.mul (.var 1) (.add (.const (128)) (.mul (.var 1) (.const (896))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part23 (z : Fin 8 → ℝ) :
    evalFin F4Part23 z = Boundary.P5.sourceEval z Certificates.P5.F4Part23 := by
  norm_num [F4Part23,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part23,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 24 of equation 4. -/
def F4Part24 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 3) (.const (64))))) (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.const (128))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F4Part24 (z : Fin 8 → ℝ) :
    evalFin F4Part24 z = Boundary.P5.sourceEval z Certificates.P5.F4Part24 := by
  norm_num [F4Part24,evalFin,finEnv,Expr.eval,Certificates.P5.F4Part24,
    Boundary.P5.sourceEval]
  ring

/-- Executable regularized central equation 4. -/
def F4 : Expr := (.add (.add (.add (.add F4Part0 (.add F4Part1 F4Part2)) (.add F4Part3 (.add F4Part4 F4Part5))) (.add (.add F4Part6 (.add F4Part7 F4Part8)) (.add F4Part9 (.add F4Part10 F4Part11)))) (.add (.add (.add F4Part12 (.add F4Part13 F4Part14)) (.add F4Part15 (.add F4Part16 F4Part17))) (.add (.add F4Part18 (.add F4Part19 F4Part20)) (.add (.add F4Part21 F4Part22) (.add F4Part23 F4Part24)))))

/-- Exact source bridge for equation 4, including h=0. -/
theorem eval_F4 (z : Fin 8 → ℝ) :
    evalFin F4 z = Boundary.P5.sourceEval z Certificates.P5.F4 := by
  change ((((evalFin F4Part0 z + (evalFin F4Part1 z + evalFin F4Part2 z)) + (evalFin F4Part3 z + (evalFin F4Part4 z + evalFin F4Part5 z))) + ((evalFin F4Part6 z + (evalFin F4Part7 z + evalFin F4Part8 z)) + (evalFin F4Part9 z + (evalFin F4Part10 z + evalFin F4Part11 z)))) + (((evalFin F4Part12 z + (evalFin F4Part13 z + evalFin F4Part14 z)) + (evalFin F4Part15 z + (evalFin F4Part16 z + evalFin F4Part17 z))) + ((evalFin F4Part18 z + (evalFin F4Part19 z + evalFin F4Part20 z)) + ((evalFin F4Part21 z + evalFin F4Part22 z) + (evalFin F4Part23 z + evalFin F4Part24 z))))) = _
  rw [eval_F4Part0, eval_F4Part1, eval_F4Part2, eval_F4Part3, eval_F4Part4, eval_F4Part5, eval_F4Part6, eval_F4Part7, eval_F4Part8, eval_F4Part9, eval_F4Part10, eval_F4Part11, eval_F4Part12, eval_F4Part13, eval_F4Part14, eval_F4Part15, eval_F4Part16, eval_F4Part17, eval_F4Part18, eval_F4Part19, eval_F4Part20, eval_F4Part21, eval_F4Part22, eval_F4Part23, eval_F4Part24]
  simp only [Certificates.P5.F4,map_add]
  ring

/-- Compact exact Horner form of equation 4. -/
def F4Horner : Expr := (.add (.add (.add (.add (.const ((-3/2))) (.mul (.var 7) (.const ((13/2))))) (.mul (.var 6) (.const (-6)))) (.mul (.var 3) (.add (.add (.add (.const (21)) (.mul (.var 7) (.const (-16)))) (.mul (.var 6) (.const ((-129/4))))) (.mul (.var 3) (.add (.add (.add (.const (63)) (.mul (.var 7) (.const (-78)))) (.mul (.var 6) (.const (-48)))) (.mul (.var 3) (.add (.add (.add (.const (-12)) (.mul (.var 7) (.const (12)))) (.mul (.var 6) (.const (27)))) (.mul (.var 3) (.add (.add (.add (.const (-96)) (.mul (.var 7) (.const (116)))) (.mul (.var 6) (.const (96)))) (.mul (.var 3) (.mul (.var 3) (.add (.add (.const (48)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (-48))))))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const ((-83/2))) (.mul (.var 7) (.const ((93/2))))) (.mul (.var 6) (.const (-61)))) (.mul (.var 3) (.add (.add (.add (.const (110)) (.mul (.var 7) (.const (-80)))) (.mul (.var 6) (.const (-230)))) (.mul (.var 3) (.add (.add (.add (.const (291)) (.mul (.var 7) (.const (-366)))) (.mul (.var 6) (.const (-101)))) (.mul (.var 3) (.add (.add (.add (.const (-92)) (.mul (.var 7) (.const (112)))) (.mul (.var 6) (.const (252)))) (.mul (.var 3) (.add (.add (.add (.const (-304)) (.mul (.var 7) (.const (484)))) (.mul (.var 6) (.const (304)))) (.mul (.var 3) (.add (.add (.add (.const (48)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (-48)))) (.mul (.var 3) (.add (.add (.const (176)) (.mul (.var 7) (.const (-176)))) (.mul (.var 6) (.const (-176)))))))))))))))) (.mul (.var 1) (.add (.add (.add (.const (42)) (.mul (.var 7) (.const (18)))) (.mul (.var 6) (.const (18)))) (.mul (.var 3) (.add (.add (.add (.const (12)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (3)))) (.mul (.var 3) (.add (.add (.add (.const (60)) (.mul (.var 7) (.const (-80)))) (.mul (.var 6) (.const (-90)))) (.mul (.var 3) (.add (.add (.add (.const (120)) (.mul (.var 7) (.const (-160)))) (.mul (.var 6) (.const (-120)))) (.mul (.var 3) (.add (.add (.add (.const (-48)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (48)))) (.mul (.var 3) (.add (.add (.const (-96)) (.mul (.var 7) (.const (96)))) (.mul (.var 6) (.const (96)))))))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (-354)) (.mul (.var 7) (.const (88)))) (.mul (.var 6) (.const (-182)))) (.mul (.var 3) (.add (.add (.add (.const (145)) (.mul (.var 7) (.const (-156)))) (.mul (.var 6) (.const (-589)))) (.mul (.var 3) (.add (.add (.add (.const (772)) (.mul (.var 7) (.const (-564)))) (.mul (.var 6) (.const (140)))) (.mul (.var 3) (.add (.add (.add (.const (-128)) (.mul (.var 7) (.const (308)))) (.mul (.var 6) (.const (720)))) (.mul (.var 3) (.add (.add (.add (.const (-160)) (.mul (.var 7) (.const (656)))) (.mul (.var 6) (.const (160)))) (.mul (.var 3) (.add (.add (.add (.const (176)) (.mul (.var 7) (.const (-176)))) (.mul (.var 6) (.const (-176)))) (.mul (.var 3) (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192)))))))))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (562)) (.mul (.var 7) (.const (98)))) (.mul (.var 6) (.const (108)))) (.mul (.var 3) (.add (.add (.add (.const (320)) (.mul (.var 7) (.const (240)))) (.mul (.var 6) (.const (-160)))) (.mul (.var 3) (.add (.add (.add (.const (196)) (.mul (.var 7) (.const (-416)))) (.mul (.var 6) (.const (-516)))) (.mul (.var 3) (.add (.add (.add (.const (296)) (.mul (.var 7) (.const (-656)))) (.mul (.var 6) (.const (-296)))) (.mul (.var 3) (.add (.add (.add (.const (-272)) (.mul (.var 7) (.const (272)))) (.mul (.var 6) (.const (272)))) (.mul (.var 3) (.add (.add (.const (-352)) (.mul (.var 7) (.const (352)))) (.mul (.var 6) (.const (352)))))))))))))) (.mul (.var 1) (.add (.add (.add (.const (18)) (.mul (.var 7) (.const (2)))) (.mul (.var 6) (.const (12)))) (.mul (.var 3) (.add (.add (.add (.const (-12)) (.mul (.var 7) (.const (32)))) (.mul (.var 6) (.const (27)))) (.mul (.var 3) (.add (.add (.add (.const (-12)) (.mul (.var 7) (.const (32)))) (.mul (.var 6) (.const (12)))) (.mul (.var 3) (.add (.add (.add (.const (48)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (-48)))) (.mul (.var 3) (.add (.add (.const (48)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (-48)))))))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (-1178)) (.mul (.var 7) (.const (64)))) (.mul (.var 6) (.const (-222)))) (.mul (.var 3) (.add (.add (.add (.const (-96)) (.mul (.var 7) (.const (-128)))) (.mul (.var 6) (.const (-672)))) (.mul (.var 3) (.add (.add (.add (.const (1760)) (.mul (.var 7) (.const (-356)))) (.mul (.var 6) (.const (448)))) (.mul (.var 3) (.add (.add (.add (.const (192)) (.mul (.var 7) (.const (304)))) (.mul (.var 6) (.const (832)))) (.mul (.var 3) (.add (.add (.add (.const (240)) (.mul (.var 7) (.const (352)))) (.mul (.var 6) (.const (-240)))) (.mul (.var 3) (.add (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192)))) (.mul (.var 3) (.add (.add (.const (64)) (.mul (.var 7) (.const (-64)))) (.mul (.var 6) (.const (-64)))))))))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (2432)) (.mul (.var 7) (.const (176)))) (.mul (.var 6) (.const (256)))) (.mul (.var 3) (.add (.add (.add (.const (1300)) (.mul (.var 7) (.const (368)))) (.mul (.var 6) (.const (-708)))) (.mul (.var 3) (.add (.add (.add (.const (-88)) (.mul (.var 7) (.const (-768)))) (.mul (.var 6) (.const (-1096)))) (.mul (.var 3) (.add (.add (.add (.const (-144)) (.mul (.var 7) (.const (-848)))) (.mul (.var 6) (.const (144)))) (.mul (.var 3) (.add (.add (.add (.const (-544)) (.mul (.var 7) (.const (544)))) (.mul (.var 6) (.const (544)))) (.mul (.var 3) (.add (.add (.const (-384)) (.mul (.var 7) (.const (384)))) (.mul (.var 6) (.const (384)))))))))))))) (.mul (.var 1) (.add (.add (.add (.const (258)) (.mul (.var 7) (.const (2)))) (.mul (.var 6) (.const (92)))) (.mul (.var 3) (.add (.add (.add (.const (40)) (.mul (.var 7) (.const (160)))) (.mul (.var 6) (.const (120)))) (.mul (.var 3) (.add (.add (.add (.const (52)) (.mul (.var 7) (.const (128)))) (.mul (.var 6) (.const (-52)))) (.mul (.var 3) (.add (.add (.add (.const (224)) (.mul (.var 7) (.const (-224)))) (.mul (.var 6) (.const (-224)))) (.mul (.var 3) (.add (.add (.const (176)) (.mul (.var 7) (.const (-176)))) (.mul (.var 6) (.const (-176)))))))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (-1864)) (.mul (.var 7) (.const (16)))) (.mul (.var 6) (.const (-120)))) (.mul (.var 3) (.add (.add (.add (.const (-328)) (.mul (.var 7) (.const (-36)))) (.mul (.var 6) (.const (-344)))) (.mul (.var 3) (.add (.add (.add (.const (2608)) (.mul (.var 7) (.const (-80)))) (.mul (.var 6) (.const (336)))) (.mul (.var 3) (.add (.add (.add (.const (496)) (.mul (.var 7) (.const (96)))) (.mul (.var 6) (.const (400)))) (.mul (.var 3) (.add (.add (.add (.const (256)) (.mul (.var 7) (.const (64)))) (.mul (.var 6) (.const (-256)))) (.mul (.var 3) (.add (.add (.const (64)) (.mul (.var 7) (.const (-64)))) (.mul (.var 6) (.const (-64)))))))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (4984)) (.mul (.var 7) (.const (128)))) (.mul (.var 6) (.const (296)))) (.mul (.var 3) (.add (.add (.add (.const (2048)) (.mul (.var 7) (.const (224)))) (.mul (.var 6) (.const (-1024)))) (.mul (.var 3) (.add (.add (.add (.const (-992)) (.mul (.var 7) (.const (-592)))) (.mul (.var 6) (.const (-1056)))) (.mul (.var 3) (.add (.add (.add (.const (-768)) (.mul (.var 7) (.const (-416)))) (.mul (.var 6) (.const (768)))) (.mul (.var 3) (.add (.add (.add (.const (-448)) (.mul (.var 7) (.const (448)))) (.mul (.var 6) (.const (448)))) (.mul (.var 3) (.add (.add (.const (-128)) (.mul (.var 7) (.const (128)))) (.mul (.var 6) (.const (128)))))))))))))) (.mul (.var 1) (.add (.add (.const (1256)) (.mul (.var 6) (.const (248)))) (.mul (.var 3) (.add (.add (.add (.const (404)) (.mul (.var 7) (.const (272)))) (.mul (.var 6) (.const (188)))) (.mul (.var 3) (.add (.add (.add (.const (352)) (.mul (.var 7) (.const (144)))) (.mul (.var 6) (.const (-352)))) (.mul (.var 3) (.add (.add (.add (.const (368)) (.mul (.var 7) (.const (-368)))) (.mul (.var 6) (.const (-368)))) (.mul (.var 3) (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192)))))))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.const (-1512)) (.mul (.var 6) (.const (-24)))) (.mul (.var 3) (.add (.add (.const (-224)) (.mul (.var 6) (.const (-64)))) (.mul (.var 3) (.add (.add (.const (2096)) (.mul (.var 6) (.const (80)))) (.mul (.var 3) (.add (.add (.const (320)) (.mul (.var 6) (.const (64)))) (.mul (.var 3) (.add (.const (64)) (.mul (.var 6) (.const (-64)))))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (5472)) (.mul (.var 7) (.const (32)))) (.mul (.var 6) (.const (160)))) (.mul (.var 3) (.add (.add (.add (.const (1504)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (-608)))) (.mul (.var 3) (.add (.add (.add (.const (-1344)) (.mul (.var 7) (.const (-160)))) (.mul (.var 6) (.const (-448)))) (.mul (.var 3) (.add (.add (.add (.const (-576)) (.mul (.var 7) (.const (-64)))) (.mul (.var 6) (.const (576)))) (.mul (.var 3) (.add (.add (.const (-128)) (.mul (.var 7) (.const (128)))) (.mul (.var 6) (.const (128)))))))))))) (.mul (.var 1) (.add (.add (.const (2936)) (.mul (.var 6) (.const (296)))) (.mul (.var 3) (.add (.add (.add (.const (896)) (.mul (.var 7) (.const (192)))) (.mul (.var 6) (.const (128)))) (.mul (.var 3) (.add (.add (.add (.const (544)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (-544)))) (.mul (.var 3) (.add (.add (.add (.const (256)) (.mul (.var 7) (.const (-256)))) (.mul (.var 6) (.const (-256)))) (.mul (.var 3) (.add (.add (.const (64)) (.mul (.var 7) (.const (-64)))) (.mul (.var 6) (.const (-64)))))))))))))))) (.mul (.var 0) (.add (.add (.add (.const (-608)) (.mul (.var 3) (.add (.const (-48)) (.mul (.var 3) (.add (.const (832)) (.mul (.var 3) (.const (64)))))))) (.mul (.var 1) (.add (.add (.add (.const (3296)) (.mul (.var 6) (.const (32)))) (.mul (.var 3) (.add (.add (.const (512)) (.mul (.var 6) (.const (-128)))) (.mul (.var 3) (.add (.add (.const (-704)) (.mul (.var 6) (.const (-64)))) (.mul (.var 3) (.add (.const (-128)) (.mul (.var 6) (.const (128)))))))))) (.mul (.var 1) (.add (.add (.const (3680)) (.mul (.var 6) (.const (160)))) (.mul (.var 3) (.add (.add (.add (.const (864)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (32)))) (.mul (.var 3) (.add (.add (.const (320)) (.mul (.var 6) (.const (-320)))) (.mul (.var 3) (.add (.add (.const (64)) (.mul (.var 7) (.const (-64)))) (.mul (.var 6) (.const (-64)))))))))))))) (.mul (.var 0) (.add (.add (.add (.const (-96)) (.mul (.var 3) (.mul (.var 3) (.const (128))))) (.mul (.var 1) (.add (.add (.const (1024)) (.mul (.var 3) (.add (.const (64)) (.mul (.var 3) (.const (-128)))))) (.mul (.var 1) (.add (.add (.const (2528)) (.mul (.var 6) (.const (32)))) (.mul (.var 3) (.add (.const (384)) (.mul (.var 3) (.add (.const (64)) (.mul (.var 6) (.const (-64)))))))))))) (.mul (.var 0) (.add (.mul (.var 1) (.add (.const (128)) (.mul (.var 1) (.add (.const (896)) (.mul (.var 3) (.const (64))))))) (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.const (128))))))))))))))))))))))

theorem eval_F4Horner (z : Fin 8 → ℝ) : evalFin F4Horner z=evalFin F4 z := by
  norm_num [F4Horner,F4,F4Part0,F4Part1,F4Part2,F4Part3,F4Part4,F4Part5,F4Part6,F4Part7,F4Part8,F4Part9,F4Part10,F4Part11,F4Part12,F4Part13,F4Part14,F4Part15,F4Part16,F4Part17,F4Part18,F4Part19,F4Part20,F4Part21,F4Part22,F4Part23,F4Part24,evalFin,finEnv,Expr.eval]
  ring

/-- Exact executable coefficient chunk 0 of equation 5. -/
def F5Part0 : Expr := (.add (.add (.add (.const (-12)) (.mul (.var 7) (.const (22)))) (.mul (.var 6) (.const (-3)))) (.mul (.var 0) (.add (.add (.add (.add (.const (-116)) (.mul (.var 7) (.const (146)))) (.mul (.var 6) (.const (-74)))) (.mul (.var 2) (.add (.add (.const (-36)) (.mul (.var 7) (.const (66)))) (.mul (.var 6) (.const (21)))))) (.mul (.var 1) (.add (.add (.const (36)) (.mul (.var 7) (.const (14)))) (.mul (.var 6) (.const (9))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part0 (z : Fin 8 → ℝ) :
    evalFin F5Part0 z = Boundary.P5.sourceEval z Certificates.P5.F5Part0 := by
  norm_num [F5Part0,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part0,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 1 of equation 5. -/
def F5Part1 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.add (.add (.add (.const (-624)) (.mul (.var 7) (.const (292)))) (.mul (.var 6) (.const (-288)))) (.mul (.var 2) (.add (.add (.add (.const (156)) (.mul (.var 7) (.const (174)))) (.mul (.var 6) (.const (-256)))) (.mul (.var 2) (.add (.add (.const (180)) (.mul (.var 7) (.const (-300)))) (.mul (.var 6) (.const (-135)))))))) (.mul (.var 1) (.add (.add (.const (372)) (.mul (.var 7) (.const (138)))) (.mul (.var 6) (.const (108))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part1 (z : Fin 8 → ℝ) :
    evalFin F5Part1 z = Boundary.P5.sourceEval z Certificates.P5.F5Part1 := by
  norm_num [F5Part1,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part1,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 2 of equation 5. -/
def F5Part2 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.add (.mul (.var 2) (.add (.add (.const (-144)) (.mul (.var 7) (.const (224)))) (.mul (.var 6) (.const (84))))) (.mul (.var 1) (.add (.add (.const (12)) (.mul (.var 7) (.const (-12)))) (.mul (.var 6) (.const (3))))))) (.mul (.var 0) (.add (.add (.add (.const (-1784)) (.mul (.var 7) (.const (232)))) (.mul (.var 6) (.const (-424)))) (.mul (.var 2) (.add (.add (.const (1368)) (.mul (.var 7) (.const (-4)))) (.mul (.var 6) (.const (-1320))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part2 (z : Fin 8 → ℝ) :
    evalFin F5Part2 z = Boundary.P5.sourceEval z Certificates.P5.F5Part2 := by
  norm_num [F5Part2,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part2,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 3 of equation 5. -/
def F5Part3 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.add (.add (.add (.const (588)) (.mul (.var 7) (.const (-1608)))) (.mul (.var 6) (.const (-108)))) (.mul (.var 2) (.add (.add (.const (336)) (.mul (.var 7) (.const (-256)))) (.mul (.var 6) (.const (-336)))))))) (.mul (.var 1) (.add (.add (.add (.const (1432)) (.mul (.var 7) (.const (348)))) (.mul (.var 6) (.const (344)))) (.mul (.var 2) (.add (.add (.const (-432)) (.mul (.var 7) (.const (1072)))) (.mul (.var 6) (.const (-208)))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part3 (z : Fin 8 → ℝ) :
    evalFin F5Part3 z = Boundary.P5.sourceEval z Certificates.P5.F5Part3 := by
  norm_num [F5Part3,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part3,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 4 of equation 5. -/
def F5Part4 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.add (.add (.const (-72)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (72)))))) (.mul (.var 1) (.add (.add (.add (.const (68)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (92)))) (.mul (.var 2) (.add (.add (.const (-24)) (.mul (.var 7) (.const (64)))) (.mul (.var 6) (.const (24))))))))) (.mul (.var 0) (.add (.add (.const (-2672)) (.mul (.var 7) (.const (64)))) (.mul (.var 6) (.const (-272)))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part4 (z : Fin 8 → ℝ) :
    evalFin F5Part4 z = Boundary.P5.sourceEval z Certificates.P5.F5Part4 := by
  norm_num [F5Part4,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part4,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 5 of equation 5. -/
def F5Part5 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 2) (.add (.add (.add (.const (3304)) (.mul (.var 7) (.const (-208)))) (.mul (.var 6) (.const (-1960)))) (.mul (.var 2) (.add (.add (.add (.const (456)) (.mul (.var 7) (.const (-2892)))) (.mul (.var 6) (.const (1320)))) (.mul (.var 2) (.add (.add (.add (.const (944)) (.mul (.var 7) (.const (-224)))) (.mul (.var 6) (.const (-944)))) (.mul (.var 2) (.add (.add (.const (-720)) (.mul (.var 7) (.const (720)))) (.mul (.var 6) (.const (720)))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part5 (z : Fin 8 → ℝ) :
    evalFin F5Part5 z = Boundary.P5.sourceEval z Certificates.P5.F5Part5 := by
  norm_num [F5Part5,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part5,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 6 of equation 5. -/
def F5Part6 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.add (.add (.const (2648)) (.mul (.var 7) (.const (320)))) (.mul (.var 6) (.const (424)))) (.mul (.var 2) (.add (.add (.add (.const (-416)) (.mul (.var 7) (.const (1680)))) (.mul (.var 6) (.const (-1952)))) (.mul (.var 2) (.add (.add (.add (.const (-120)) (.mul (.var 7) (.const (-960)))) (.mul (.var 6) (.const (120)))) (.mul (.var 2) (.add (.add (.const (768)) (.mul (.var 7) (.const (-768)))) (.mul (.var 6) (.const (-768)))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part6 (z : Fin 8 → ℝ) :
    evalFin F5Part6 z = Boundary.P5.sourceEval z Certificates.P5.F5Part6 := by
  norm_num [F5Part6,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part6,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 7 of equation 5. -/
def F5Part7 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.add (.add (.add (.const (232)) (.mul (.var 7) (.const (-52)))) (.mul (.var 6) (.const (360)))) (.mul (.var 2) (.add (.add (.add (.const (-40)) (.mul (.var 7) (.const (400)))) (.mul (.var 6) (.const (40)))) (.mul (.var 2) (.add (.add (.const (-144)) (.mul (.var 7) (.const (144)))) (.mul (.var 6) (.const (144)))))))))) (.mul (.var 0) (.add (.add (.const (-2112)) (.mul (.var 6) (.const (-64)))) (.mul (.var 2) (.const (4336))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part7 (z : Fin 8 → ℝ) :
    evalFin F5Part7 z = Boundary.P5.sourceEval z Certificates.P5.F5Part7 := by
  norm_num [F5Part7,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part7,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 8 of equation 5. -/
def F5Part8 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 2) (.add (.add (.mul (.var 7) (.const (-96))) (.mul (.var 6) (.const (-1136)))) (.mul (.var 2) (.add (.add (.add (.const (96)) (.mul (.var 7) (.const (-2160)))) (.mul (.var 6) (.const (2976)))) (.mul (.var 2) (.add (.add (.add (.const (480)) (.mul (.var 7) (.const (1504)))) (.mul (.var 6) (.const (-480)))) (.mul (.var 2) (.add (.add (.add (.const (-2400)) (.mul (.var 7) (.const (2400)))) (.mul (.var 6) (.const (2400)))) (.mul (.var 2) (.const (288))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part8 (z : Fin 8 → ℝ) :
    evalFin F5Part8 z = Boundary.P5.sourceEval z Certificates.P5.F5Part8 := by
  norm_num [F5Part8,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part8,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 9 of equation 5. -/
def F5Part9 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 7) (.const (-288))) (.mul (.var 6) (.const (-288))))))))) (.mul (.var 1) (.add (.add (.add (.const (2480)) (.mul (.var 7) (.const (96)))) (.mul (.var 6) (.const (208)))) (.mul (.var 2) (.add (.add (.add (.const (-704)) (.mul (.var 7) (.const (1088)))) (.mul (.var 6) (.const (-3392)))) (.mul (.var 2) (.add (.add (.add (.const (-48)) (.mul (.var 7) (.const (-2928)))) (.mul (.var 6) (.const (48)))) (.mul (.var 2) (.const (2432)))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part9 (z : Fin 8 → ℝ) :
    evalFin F5Part9 z = Boundary.P5.sourceEval z Certificates.P5.F5Part9 := by
  norm_num [F5Part9,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part9,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 10 of equation 5. -/
def F5Part10 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.add (.mul (.var 7) (.const (-2432))) (.mul (.var 6) (.const (-2432)))) (.mul (.var 2) (.add (.add (.const (-480)) (.mul (.var 7) (.const (480)))) (.mul (.var 6) (.const (480))))))))) (.mul (.var 1) (.add (.add (.add (.const (512)) (.mul (.var 7) (.const (-16)))) (.mul (.var 6) (.const (512)))) (.mul (.var 2) (.add (.add (.add (.const (176)) (.mul (.var 7) (.const (816)))) (.mul (.var 6) (.const (-176)))) (.mul (.var 2) (.const (-384))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part10 (z : Fin 8 → ℝ) :
    evalFin F5Part10 z = Boundary.P5.sourceEval z Certificates.P5.F5Part10 := by
  norm_num [F5Part10,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part10,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 11 of equation 5. -/
def F5Part11 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 2) (.mul (.var 2) (.add (.add (.mul (.var 7) (.const (384))) (.mul (.var 6) (.const (384)))) (.mul (.var 2) (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192)))))))))) (.mul (.var 0) (.add (.const (-832)) (.mul (.var 2) (.add (.add (.const (3424)) (.mul (.var 6) (.const (-224)))) (.mul (.var 2) (.add (.add (.add (.const (432)) (.mul (.var 7) (.const (-576)))) (.mul (.var 6) (.const (2256)))) (.mul (.var 2) (.mul (.var 7) (.const (2368))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part11 (z : Fin 8 → ℝ) :
    evalFin F5Part11 z = Boundary.P5.sourceEval z Certificates.P5.F5Part11 := by
  norm_num [F5Part11,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part11,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 12 of equation 5. -/
def F5Part12 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.add (.add (.const (-2000)) (.mul (.var 7) (.const (2000)))) (.mul (.var 6) (.const (2000)))) (.mul (.var 2) (.add (.add (.const (1056)) (.mul (.var 7) (.const (-1056)))) (.mul (.var 6) (.const (-1056)))))))))) (.mul (.var 1) (.add (.add (.const (1120)) (.mul (.var 6) (.const (32)))) (.mul (.var 2) (.add (.add (.add (.const (-1344)) (.mul (.var 7) (.const (256)))) (.mul (.var 6) (.const (-2240)))) (.mul (.var 2) (.const (-576))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part12 (z : Fin 8 → ℝ) :
    evalFin F5Part12 z = Boundary.P5.sourceEval z Certificates.P5.F5Part12 := by
  norm_num [F5Part12,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part12,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 13 of equation 5. -/
def F5Part13 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.add (.add (.mul (.var 7) (.const (-2976))) (.mul (.var 6) (.const (576)))) (.mul (.var 2) (.add (.add (.add (.const (1664)) (.mul (.var 7) (.const (-1664)))) (.mul (.var 6) (.const (-1664)))) (.mul (.var 2) (.add (.add (.const (-1760)) (.mul (.var 7) (.const (1760)))) (.mul (.var 6) (.const (1760)))))))))) (.mul (.var 1) (.add (.add (.const (592)) (.mul (.var 6) (.const (304)))) (.mul (.var 2) (.add (.const (512)) (.mul (.var 7) (.const (672)))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part13 (z : Fin 8 → ℝ) :
    evalFin F5Part13 z = Boundary.P5.sourceEval z Certificates.P5.F5Part13 := by
  norm_num [F5Part13,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part13,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 14 of equation 5. -/
def F5Part14 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 2) (.add (.mul (.var 6) (.const (-512))) (.mul (.var 2) (.add (.add (.add (.const (-48)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (48)))) (.mul (.var 2) (.add (.add (.const (704)) (.mul (.var 7) (.const (-704)))) (.mul (.var 6) (.const (-704))))))))))) (.mul (.var 0) (.add (.const (-128)) (.mul (.var 2) (.add (.const (1472)) (.mul (.var 2) (.add (.add (.const (576)) (.mul (.var 6) (.const (576)))) (.mul (.var 2) (.const (384))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part14 (z : Fin 8 → ℝ) :
    evalFin F5Part14 z = Boundary.P5.sourceEval z Certificates.P5.F5Part14 := by
  norm_num [F5Part14,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part14,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 15 of equation 5. -/
def F5Part15 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.add (.mul (.var 7) (.const (896))) (.mul (.var 6) (.const (-384)))) (.mul (.var 2) (.mul (.var 2) (.add (.add (.const (1152)) (.mul (.var 7) (.const (-1152)))) (.mul (.var 6) (.const (-1152)))))))))) (.mul (.var 1) (.add (.const (192)) (.mul (.var 2) (.add (.add (.const (-1024)) (.mul (.var 6) (.const (-512)))) (.mul (.var 2) (.add (.add (.add (.const (-960)) (.mul (.var 7) (.const (-960)))) (.mul (.var 6) (.const (960)))) (.mul (.var 2) (.const (-512)))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part15 (z : Fin 8 → ℝ) :
    evalFin F5Part15 z = Boundary.P5.sourceEval z Certificates.P5.F5Part15 := by
  norm_num [F5Part15,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part15,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 16 of equation 5. -/
def F5Part16 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.add (.mul (.var 7) (.const (512))) (.mul (.var 6) (.const (512)))) (.mul (.var 2) (.add (.add (.const (-1920)) (.mul (.var 7) (.const (1920)))) (.mul (.var 6) (.const (1920))))))))) (.mul (.var 1) (.add (.add (.const (320)) (.mul (.var 6) (.const (64)))) (.mul (.var 2) (.add (.add (.add (.const (448)) (.mul (.var 7) (.const (192)))) (.mul (.var 6) (.const (-448)))) (.mul (.var 2) (.add (.const (384)) (.mul (.var 7) (.const (-384))))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part16 (z : Fin 8 → ℝ) :
    evalFin F5Part16 z = Boundary.P5.sourceEval z Certificates.P5.F5Part16 := by
  norm_num [F5Part16,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part16,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 17 of equation 5. -/
def F5Part17 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 6) (.const (-384))) (.mul (.var 2) (.add (.add (.const (768)) (.mul (.var 7) (.const (-768)))) (.mul (.var 6) (.const (-768)))))))))) (.mul (.var 0) (.mul (.var 2) (.add (.const (256)) (.mul (.var 2) (.add (.const (192)) (.mul (.var 2) (.add (.add (.const (256)) (.mul (.var 6) (.const (-256)))) (.mul (.var 2) (.add (.add (.add (.const (320)) (.mul (.var 7) (.const (-320)))) (.mul (.var 6) (.const (-320)))) (.mul (.var 2) (.const (384))))))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part17 (z : Fin 8 → ℝ) :
    evalFin F5Part17 z = Boundary.P5.sourceEval z Certificates.P5.F5Part17 := by
  norm_num [F5Part17,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part17,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 18 of equation 5. -/
def F5Part18 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.mul (.var 2) (.add (.mul (.var 7) (.const (-384))) (.mul (.var 6) (.const (-384))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.add (.const (-256)) (.mul (.var 2) (.add (.add (.const (-384)) (.mul (.var 6) (.const (384)))) (.mul (.var 2) (.add (.add (.add (.const (-512)) (.mul (.var 7) (.const (512)))) (.mul (.var 6) (.const (512)))) (.mul (.var 2) (.add (.add (.const (-640)) (.mul (.var 7) (.const (640)))) (.mul (.var 6) (.const (640))))))))))) (.mul (.var 1) (.const (64))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part18 (z : Fin 8 → ℝ) :
    evalFin F5Part18 z = Boundary.P5.sourceEval z Certificates.P5.F5Part18 := by
  norm_num [F5Part18,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part18,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 19 of equation 5. -/
def F5Part19 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.mul (.var 2) (.add (.add (.const (128)) (.mul (.var 6) (.const (-128)))) (.mul (.var 2) (.add (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192)))) (.mul (.var 2) (.add (.add (.const (256)) (.mul (.var 7) (.const (-256)))) (.mul (.var 6) (.const (-256)))))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F5Part19 (z : Fin 8 → ℝ) :
    evalFin F5Part19 z = Boundary.P5.sourceEval z Certificates.P5.F5Part19 := by
  norm_num [F5Part19,evalFin,finEnv,Expr.eval,Certificates.P5.F5Part19,
    Boundary.P5.sourceEval]
  ring

/-- Executable regularized central equation 5. -/
def F5 : Expr := (.add (.add (.add (.add F5Part0 F5Part1) (.add F5Part2 (.add F5Part3 F5Part4))) (.add (.add F5Part5 F5Part6) (.add F5Part7 (.add F5Part8 F5Part9)))) (.add (.add (.add F5Part10 F5Part11) (.add F5Part12 (.add F5Part13 F5Part14))) (.add (.add F5Part15 F5Part16) (.add F5Part17 (.add F5Part18 F5Part19)))))

/-- Exact source bridge for equation 5, including h=0. -/
theorem eval_F5 (z : Fin 8 → ℝ) :
    evalFin F5 z = Boundary.P5.sourceEval z Certificates.P5.F5 := by
  change ((((evalFin F5Part0 z + evalFin F5Part1 z) + (evalFin F5Part2 z + (evalFin F5Part3 z + evalFin F5Part4 z))) + ((evalFin F5Part5 z + evalFin F5Part6 z) + (evalFin F5Part7 z + (evalFin F5Part8 z + evalFin F5Part9 z)))) + (((evalFin F5Part10 z + evalFin F5Part11 z) + (evalFin F5Part12 z + (evalFin F5Part13 z + evalFin F5Part14 z))) + ((evalFin F5Part15 z + evalFin F5Part16 z) + (evalFin F5Part17 z + (evalFin F5Part18 z + evalFin F5Part19 z))))) = _
  rw [eval_F5Part0, eval_F5Part1, eval_F5Part2, eval_F5Part3, eval_F5Part4, eval_F5Part5, eval_F5Part6, eval_F5Part7, eval_F5Part8, eval_F5Part9, eval_F5Part10, eval_F5Part11, eval_F5Part12, eval_F5Part13, eval_F5Part14, eval_F5Part15, eval_F5Part16, eval_F5Part17, eval_F5Part18, eval_F5Part19]
  simp only [Certificates.P5.F5,map_add]
  ring

/-- Compact exact Horner form of equation 5. -/
def F5Horner : Expr := (.add (.add (.add (.const (-12)) (.mul (.var 7) (.const (22)))) (.mul (.var 6) (.const (-3)))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (-116)) (.mul (.var 7) (.const (146)))) (.mul (.var 6) (.const (-74)))) (.mul (.var 2) (.add (.add (.const (-36)) (.mul (.var 7) (.const (66)))) (.mul (.var 6) (.const (21)))))) (.mul (.var 1) (.add (.add (.const (36)) (.mul (.var 7) (.const (14)))) (.mul (.var 6) (.const (9)))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (-624)) (.mul (.var 7) (.const (292)))) (.mul (.var 6) (.const (-288)))) (.mul (.var 2) (.add (.add (.add (.const (156)) (.mul (.var 7) (.const (174)))) (.mul (.var 6) (.const (-256)))) (.mul (.var 2) (.add (.add (.const (180)) (.mul (.var 7) (.const (-300)))) (.mul (.var 6) (.const (-135)))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (372)) (.mul (.var 7) (.const (138)))) (.mul (.var 6) (.const (108)))) (.mul (.var 2) (.add (.add (.const (-144)) (.mul (.var 7) (.const (224)))) (.mul (.var 6) (.const (84)))))) (.mul (.var 1) (.add (.add (.const (12)) (.mul (.var 7) (.const (-12)))) (.mul (.var 6) (.const (3)))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (-1784)) (.mul (.var 7) (.const (232)))) (.mul (.var 6) (.const (-424)))) (.mul (.var 2) (.add (.add (.add (.const (1368)) (.mul (.var 7) (.const (-4)))) (.mul (.var 6) (.const (-1320)))) (.mul (.var 2) (.add (.add (.add (.const (588)) (.mul (.var 7) (.const (-1608)))) (.mul (.var 6) (.const (-108)))) (.mul (.var 2) (.add (.add (.const (336)) (.mul (.var 7) (.const (-256)))) (.mul (.var 6) (.const (-336)))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (1432)) (.mul (.var 7) (.const (348)))) (.mul (.var 6) (.const (344)))) (.mul (.var 2) (.add (.add (.add (.const (-432)) (.mul (.var 7) (.const (1072)))) (.mul (.var 6) (.const (-208)))) (.mul (.var 2) (.add (.add (.const (-72)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (72)))))))) (.mul (.var 1) (.add (.add (.add (.const (68)) (.mul (.var 7) (.const (-48)))) (.mul (.var 6) (.const (92)))) (.mul (.var 2) (.add (.add (.const (-24)) (.mul (.var 7) (.const (64)))) (.mul (.var 6) (.const (24)))))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (-2672)) (.mul (.var 7) (.const (64)))) (.mul (.var 6) (.const (-272)))) (.mul (.var 2) (.add (.add (.add (.const (3304)) (.mul (.var 7) (.const (-208)))) (.mul (.var 6) (.const (-1960)))) (.mul (.var 2) (.add (.add (.add (.const (456)) (.mul (.var 7) (.const (-2892)))) (.mul (.var 6) (.const (1320)))) (.mul (.var 2) (.add (.add (.add (.const (944)) (.mul (.var 7) (.const (-224)))) (.mul (.var 6) (.const (-944)))) (.mul (.var 2) (.add (.add (.const (-720)) (.mul (.var 7) (.const (720)))) (.mul (.var 6) (.const (720)))))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (2648)) (.mul (.var 7) (.const (320)))) (.mul (.var 6) (.const (424)))) (.mul (.var 2) (.add (.add (.add (.const (-416)) (.mul (.var 7) (.const (1680)))) (.mul (.var 6) (.const (-1952)))) (.mul (.var 2) (.add (.add (.add (.const (-120)) (.mul (.var 7) (.const (-960)))) (.mul (.var 6) (.const (120)))) (.mul (.var 2) (.add (.add (.const (768)) (.mul (.var 7) (.const (-768)))) (.mul (.var 6) (.const (-768)))))))))) (.mul (.var 1) (.add (.add (.add (.const (232)) (.mul (.var 7) (.const (-52)))) (.mul (.var 6) (.const (360)))) (.mul (.var 2) (.add (.add (.add (.const (-40)) (.mul (.var 7) (.const (400)))) (.mul (.var 6) (.const (40)))) (.mul (.var 2) (.add (.add (.const (-144)) (.mul (.var 7) (.const (144)))) (.mul (.var 6) (.const (144)))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.const (-2112)) (.mul (.var 6) (.const (-64)))) (.mul (.var 2) (.add (.add (.add (.const (4336)) (.mul (.var 7) (.const (-96)))) (.mul (.var 6) (.const (-1136)))) (.mul (.var 2) (.add (.add (.add (.const (96)) (.mul (.var 7) (.const (-2160)))) (.mul (.var 6) (.const (2976)))) (.mul (.var 2) (.add (.add (.add (.const (480)) (.mul (.var 7) (.const (1504)))) (.mul (.var 6) (.const (-480)))) (.mul (.var 2) (.add (.add (.add (.const (-2400)) (.mul (.var 7) (.const (2400)))) (.mul (.var 6) (.const (2400)))) (.mul (.var 2) (.add (.add (.const (288)) (.mul (.var 7) (.const (-288)))) (.mul (.var 6) (.const (-288)))))))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (2480)) (.mul (.var 7) (.const (96)))) (.mul (.var 6) (.const (208)))) (.mul (.var 2) (.add (.add (.add (.const (-704)) (.mul (.var 7) (.const (1088)))) (.mul (.var 6) (.const (-3392)))) (.mul (.var 2) (.add (.add (.add (.const (-48)) (.mul (.var 7) (.const (-2928)))) (.mul (.var 6) (.const (48)))) (.mul (.var 2) (.add (.add (.add (.const (2432)) (.mul (.var 7) (.const (-2432)))) (.mul (.var 6) (.const (-2432)))) (.mul (.var 2) (.add (.add (.const (-480)) (.mul (.var 7) (.const (480)))) (.mul (.var 6) (.const (480)))))))))))) (.mul (.var 1) (.add (.add (.add (.const (512)) (.mul (.var 7) (.const (-16)))) (.mul (.var 6) (.const (512)))) (.mul (.var 2) (.add (.add (.add (.const (176)) (.mul (.var 7) (.const (816)))) (.mul (.var 6) (.const (-176)))) (.mul (.var 2) (.add (.add (.add (.const (-384)) (.mul (.var 7) (.const (384)))) (.mul (.var 6) (.const (384)))) (.mul (.var 2) (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192)))))))))))))) (.mul (.var 0) (.add (.add (.add (.const (-832)) (.mul (.var 2) (.add (.add (.const (3424)) (.mul (.var 6) (.const (-224)))) (.mul (.var 2) (.add (.add (.add (.const (432)) (.mul (.var 7) (.const (-576)))) (.mul (.var 6) (.const (2256)))) (.mul (.var 2) (.add (.mul (.var 7) (.const (2368))) (.mul (.var 2) (.add (.add (.add (.const (-2000)) (.mul (.var 7) (.const (2000)))) (.mul (.var 6) (.const (2000)))) (.mul (.var 2) (.add (.add (.const (1056)) (.mul (.var 7) (.const (-1056)))) (.mul (.var 6) (.const (-1056)))))))))))))) (.mul (.var 1) (.add (.add (.add (.const (1120)) (.mul (.var 6) (.const (32)))) (.mul (.var 2) (.add (.add (.add (.const (-1344)) (.mul (.var 7) (.const (256)))) (.mul (.var 6) (.const (-2240)))) (.mul (.var 2) (.add (.add (.add (.const (-576)) (.mul (.var 7) (.const (-2976)))) (.mul (.var 6) (.const (576)))) (.mul (.var 2) (.add (.add (.add (.const (1664)) (.mul (.var 7) (.const (-1664)))) (.mul (.var 6) (.const (-1664)))) (.mul (.var 2) (.add (.add (.const (-1760)) (.mul (.var 7) (.const (1760)))) (.mul (.var 6) (.const (1760)))))))))))) (.mul (.var 1) (.add (.add (.const (592)) (.mul (.var 6) (.const (304)))) (.mul (.var 2) (.add (.add (.add (.const (512)) (.mul (.var 7) (.const (672)))) (.mul (.var 6) (.const (-512)))) (.mul (.var 2) (.add (.add (.add (.const (-48)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (48)))) (.mul (.var 2) (.add (.add (.const (704)) (.mul (.var 7) (.const (-704)))) (.mul (.var 6) (.const (-704)))))))))))))) (.mul (.var 0) (.add (.add (.add (.const (-128)) (.mul (.var 2) (.add (.const (1472)) (.mul (.var 2) (.add (.add (.const (576)) (.mul (.var 6) (.const (576)))) (.mul (.var 2) (.add (.add (.add (.const (384)) (.mul (.var 7) (.const (896)))) (.mul (.var 6) (.const (-384)))) (.mul (.var 2) (.mul (.var 2) (.add (.add (.const (1152)) (.mul (.var 7) (.const (-1152)))) (.mul (.var 6) (.const (-1152))))))))))))) (.mul (.var 1) (.add (.add (.const (192)) (.mul (.var 2) (.add (.add (.const (-1024)) (.mul (.var 6) (.const (-512)))) (.mul (.var 2) (.add (.add (.add (.const (-960)) (.mul (.var 7) (.const (-960)))) (.mul (.var 6) (.const (960)))) (.mul (.var 2) (.add (.add (.add (.const (-512)) (.mul (.var 7) (.const (512)))) (.mul (.var 6) (.const (512)))) (.mul (.var 2) (.add (.add (.const (-1920)) (.mul (.var 7) (.const (1920)))) (.mul (.var 6) (.const (1920)))))))))))) (.mul (.var 1) (.add (.add (.const (320)) (.mul (.var 6) (.const (64)))) (.mul (.var 2) (.add (.add (.add (.const (448)) (.mul (.var 7) (.const (192)))) (.mul (.var 6) (.const (-448)))) (.mul (.var 2) (.add (.add (.add (.const (384)) (.mul (.var 7) (.const (-384)))) (.mul (.var 6) (.const (-384)))) (.mul (.var 2) (.add (.add (.const (768)) (.mul (.var 7) (.const (-768)))) (.mul (.var 6) (.const (-768)))))))))))))) (.mul (.var 0) (.add (.mul (.var 2) (.add (.const (256)) (.mul (.var 2) (.add (.const (192)) (.mul (.var 2) (.add (.add (.const (256)) (.mul (.var 6) (.const (-256)))) (.mul (.var 2) (.add (.add (.add (.const (320)) (.mul (.var 7) (.const (-320)))) (.mul (.var 6) (.const (-320)))) (.mul (.var 2) (.add (.add (.const (384)) (.mul (.var 7) (.const (-384)))) (.mul (.var 6) (.const (-384))))))))))))) (.mul (.var 1) (.add (.mul (.var 2) (.add (.const (-256)) (.mul (.var 2) (.add (.add (.const (-384)) (.mul (.var 6) (.const (384)))) (.mul (.var 2) (.add (.add (.add (.const (-512)) (.mul (.var 7) (.const (512)))) (.mul (.var 6) (.const (512)))) (.mul (.var 2) (.add (.add (.const (-640)) (.mul (.var 7) (.const (640)))) (.mul (.var 6) (.const (640))))))))))) (.mul (.var 1) (.add (.const (64)) (.mul (.var 2) (.add (.add (.const (128)) (.mul (.var 6) (.const (-128)))) (.mul (.var 2) (.add (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192)))) (.mul (.var 2) (.add (.add (.const (256)) (.mul (.var 7) (.const (-256)))) (.mul (.var 6) (.const (-256))))))))))))))))))))))))))))))

theorem eval_F5Horner (z : Fin 8 → ℝ) : evalFin F5Horner z=evalFin F5 z := by
  norm_num [F5Horner,F5,F5Part0,F5Part1,F5Part2,F5Part3,F5Part4,F5Part5,F5Part6,F5Part7,F5Part8,F5Part9,F5Part10,F5Part11,F5Part12,F5Part13,F5Part14,F5Part15,F5Part16,F5Part17,F5Part18,F5Part19,evalFin,finEnv,Expr.eval]
  ring

/-- Exact executable coefficient chunk 0 of equation 6. -/
def F6Part0 : Expr := (.add (.add (.add (.const (21)) (.mul (.var 7) (.const (-16)))) (.mul (.var 6) (.const ((-129/4))))) (.mul (.var 3) (.add (.add (.add (.const (126)) (.mul (.var 7) (.const (-156)))) (.mul (.var 6) (.const (-96)))) (.mul (.var 3) (.add (.add (.add (.const (-36)) (.mul (.var 7) (.const (36)))) (.mul (.var 6) (.const (81)))) (.mul (.var 3) (.add (.add (.const (-384)) (.mul (.var 7) (.const (464)))) (.mul (.var 6) (.const (384))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part0 (z : Fin 8 → ℝ) :
    evalFin F6Part0 z = Boundary.P5.sourceEval z Certificates.P5.F6Part0 := by
  norm_num [F6Part0,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part0,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 1 of equation 6. -/
def F6Part1 : Expr := (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.const (288)) (.mul (.var 7) (.const (-288)))) (.mul (.var 6) (.const (-288))))))))) (.mul (.var 0) (.add (.add (.add (.const (110)) (.mul (.var 7) (.const (-80)))) (.mul (.var 6) (.const (-230)))) (.mul (.var 3) (.add (.add (.add (.const (582)) (.mul (.var 7) (.const (-732)))) (.mul (.var 6) (.const (-202)))) (.mul (.var 3) (.add (.add (.const (-276)) (.mul (.var 7) (.const (336)))) (.mul (.var 6) (.const (756))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part1 (z : Fin 8 → ℝ) :
    evalFin F6Part1 z = Boundary.P5.sourceEval z Certificates.P5.F6Part1 := by
  norm_num [F6Part1,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part1,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 2 of equation 6. -/
def F6Part2 : Expr := (.mul (.var 0) (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (-1216)) (.mul (.var 7) (.const (1936)))) (.mul (.var 6) (.const (1216)))) (.mul (.var 3) (.add (.add (.add (.const (240)) (.mul (.var 7) (.const (-240)))) (.mul (.var 6) (.const (-240)))) (.mul (.var 3) (.add (.add (.const (1056)) (.mul (.var 7) (.const (-1056)))) (.mul (.var 6) (.const (-1056))))))))))) (.mul (.var 1) (.add (.add (.const (12)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (3)))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part2 (z : Fin 8 → ℝ) :
    evalFin F6Part2 z = Boundary.P5.sourceEval z Certificates.P5.F6Part2 := by
  norm_num [F6Part2,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part2,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 3 of equation 6. -/
def F6Part3 : Expr := (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.add (.add (.add (.const (120)) (.mul (.var 7) (.const (-160)))) (.mul (.var 6) (.const (-180)))) (.mul (.var 3) (.add (.add (.add (.const (360)) (.mul (.var 7) (.const (-480)))) (.mul (.var 6) (.const (-360)))) (.mul (.var 3) (.add (.add (.add (.const (-192)) (.mul (.var 7) (.const (192)))) (.mul (.var 6) (.const (192)))) (.mul (.var 3) (.add (.add (.const (-480)) (.mul (.var 7) (.const (480)))) (.mul (.var 6) (.const (480)))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part3 (z : Fin 8 → ℝ) :
    evalFin F6Part3 z = Boundary.P5.sourceEval z Certificates.P5.F6Part3 := by
  norm_num [F6Part3,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part3,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 4 of equation 6. -/
def F6Part4 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.add (.add (.const (145)) (.mul (.var 7) (.const (-156)))) (.mul (.var 6) (.const (-589)))) (.mul (.var 3) (.add (.add (.add (.const (1544)) (.mul (.var 7) (.const (-1128)))) (.mul (.var 6) (.const (280)))) (.mul (.var 3) (.add (.add (.add (.const (-384)) (.mul (.var 7) (.const (924)))) (.mul (.var 6) (.const (2160)))) (.mul (.var 3) (.add (.add (.const (-640)) (.mul (.var 7) (.const (2624)))) (.mul (.var 6) (.const (640))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part4 (z : Fin 8 → ℝ) :
    evalFin F6Part4 z = Boundary.P5.sourceEval z Certificates.P5.F6Part4 := by
  norm_num [F6Part4,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part4,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 5 of equation 6. -/
def F6Part5 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (880)) (.mul (.var 7) (.const (-880)))) (.mul (.var 6) (.const (-880)))) (.mul (.var 3) (.add (.add (.const (1152)) (.mul (.var 7) (.const (-1152)))) (.mul (.var 6) (.const (-1152)))))))))) (.mul (.var 1) (.add (.add (.add (.const (320)) (.mul (.var 7) (.const (240)))) (.mul (.var 6) (.const (-160)))) (.mul (.var 3) (.add (.add (.const (392)) (.mul (.var 7) (.const (-832)))) (.mul (.var 6) (.const (-1032))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part5 (z : Fin 8 → ℝ) :
    evalFin F6Part5 z = Boundary.P5.sourceEval z Certificates.P5.F6Part5 := by
  norm_num [F6Part5,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part5,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 6 of equation 6. -/
def F6Part6 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (888)) (.mul (.var 7) (.const (-1968)))) (.mul (.var 6) (.const (-888)))) (.mul (.var 3) (.add (.add (.add (.const (-1088)) (.mul (.var 7) (.const (1088)))) (.mul (.var 6) (.const (1088)))) (.mul (.var 3) (.add (.add (.const (-1760)) (.mul (.var 7) (.const (1760)))) (.mul (.var 6) (.const (1760)))))))))) (.mul (.var 1) (.add (.add (.const (-12)) (.mul (.var 7) (.const (32)))) (.mul (.var 6) (.const (27)))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part6 (z : Fin 8 → ℝ) :
    evalFin F6Part6 z = Boundary.P5.sourceEval z Certificates.P5.F6Part6 := by
  norm_num [F6Part6,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part6,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 7 of equation 6. -/
def F6Part7 : Expr := (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 3) (.add (.add (.add (.const (-24)) (.mul (.var 7) (.const (64)))) (.mul (.var 6) (.const (24)))) (.mul (.var 3) (.add (.add (.add (.const (144)) (.mul (.var 7) (.const (-144)))) (.mul (.var 6) (.const (-144)))) (.mul (.var 3) (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192))))))))))) (.mul (.var 0) (.add (.add (.const (-96)) (.mul (.var 7) (.const (-128)))) (.mul (.var 6) (.const (-672))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part7 (z : Fin 8 → ℝ) :
    evalFin F6Part7 z = Boundary.P5.sourceEval z Certificates.P5.F6Part7 := by
  norm_num [F6Part7,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part7,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 8 of equation 6. -/
def F6Part8 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 3) (.add (.add (.add (.const (3520)) (.mul (.var 7) (.const (-712)))) (.mul (.var 6) (.const (896)))) (.mul (.var 3) (.add (.add (.add (.const (576)) (.mul (.var 7) (.const (912)))) (.mul (.var 6) (.const (2496)))) (.mul (.var 3) (.add (.add (.add (.const (960)) (.mul (.var 7) (.const (1408)))) (.mul (.var 6) (.const (-960)))) (.mul (.var 3) (.add (.add (.const (960)) (.mul (.var 7) (.const (-960)))) (.mul (.var 6) (.const (-960))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part8 (z : Fin 8 → ℝ) :
    evalFin F6Part8 z = Boundary.P5.sourceEval z Certificates.P5.F6Part8 := by
  norm_num [F6Part8,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part8,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 9 of equation 6. -/
def F6Part9 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.const (384)) (.mul (.var 7) (.const (-384)))) (.mul (.var 6) (.const (-384))))))))) (.mul (.var 1) (.add (.add (.add (.const (1300)) (.mul (.var 7) (.const (368)))) (.mul (.var 6) (.const (-708)))) (.mul (.var 3) (.add (.add (.add (.const (-176)) (.mul (.var 7) (.const (-1536)))) (.mul (.var 6) (.const (-2192)))) (.mul (.var 3) (.add (.add (.const (-432)) (.mul (.var 7) (.const (-2544)))) (.mul (.var 6) (.const (432)))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part9 (z : Fin 8 → ℝ) :
    evalFin F6Part9 z = Boundary.P5.sourceEval z Certificates.P5.F6Part9 := by
  norm_num [F6Part9,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part9,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 10 of equation 6. -/
def F6Part10 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 3) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (-2176)) (.mul (.var 7) (.const (2176)))) (.mul (.var 6) (.const (2176)))) (.mul (.var 3) (.add (.add (.const (-1920)) (.mul (.var 7) (.const (1920)))) (.mul (.var 6) (.const (1920))))))))) (.mul (.var 1) (.add (.add (.add (.const (40)) (.mul (.var 7) (.const (160)))) (.mul (.var 6) (.const (120)))) (.mul (.var 3) (.add (.add (.const (104)) (.mul (.var 7) (.const (256)))) (.mul (.var 6) (.const (-104))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part10 (z : Fin 8 → ℝ) :
    evalFin F6Part10 z = Boundary.P5.sourceEval z Certificates.P5.F6Part10 := by
  norm_num [F6Part10,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part10,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 11 of equation 6. -/
def F6Part11 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (672)) (.mul (.var 7) (.const (-672)))) (.mul (.var 6) (.const (-672)))) (.mul (.var 3) (.add (.add (.const (704)) (.mul (.var 7) (.const (-704)))) (.mul (.var 6) (.const (-704)))))))))) (.mul (.var 0) (.add (.add (.add (.const (-328)) (.mul (.var 7) (.const (-36)))) (.mul (.var 6) (.const (-344)))) (.mul (.var 3) (.add (.add (.const (5216)) (.mul (.var 7) (.const (-160)))) (.mul (.var 6) (.const (672)))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part11 (z : Fin 8 → ℝ) :
    evalFin F6Part11 z = Boundary.P5.sourceEval z Certificates.P5.F6Part11 := by
  norm_num [F6Part11,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part11,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 12 of equation 6. -/
def F6Part12 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 3) (.mul (.var 3) (.add (.add (.add (.const (1488)) (.mul (.var 7) (.const (288)))) (.mul (.var 6) (.const (1200)))) (.mul (.var 3) (.add (.add (.add (.const (1024)) (.mul (.var 7) (.const (256)))) (.mul (.var 6) (.const (-1024)))) (.mul (.var 3) (.add (.add (.const (320)) (.mul (.var 7) (.const (-320)))) (.mul (.var 6) (.const (-320)))))))))) (.mul (.var 1) (.add (.add (.const (2048)) (.mul (.var 7) (.const (224)))) (.mul (.var 6) (.const (-1024))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part12 (z : Fin 8 → ℝ) :
    evalFin F6Part12 z = Boundary.P5.sourceEval z Certificates.P5.F6Part12 := by
  norm_num [F6Part12,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part12,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 13 of equation 6. -/
def F6Part13 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.add (.add (.add (.const (-1984)) (.mul (.var 7) (.const (-1184)))) (.mul (.var 6) (.const (-2112)))) (.mul (.var 3) (.add (.add (.add (.const (-2304)) (.mul (.var 7) (.const (-1248)))) (.mul (.var 6) (.const (2304)))) (.mul (.var 3) (.add (.add (.add (.const (-1792)) (.mul (.var 7) (.const (1792)))) (.mul (.var 6) (.const (1792)))) (.mul (.var 3) (.add (.add (.const (-640)) (.mul (.var 7) (.const (640)))) (.mul (.var 6) (.const (640))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part13 (z : Fin 8 → ℝ) :
    evalFin F6Part13 z = Boundary.P5.sourceEval z Certificates.P5.F6Part13 := by
  norm_num [F6Part13,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part13,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 14 of equation 6. -/
def F6Part14 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.add (.add (.add (.const (404)) (.mul (.var 7) (.const (272)))) (.mul (.var 6) (.const (188)))) (.mul (.var 3) (.add (.add (.add (.const (704)) (.mul (.var 7) (.const (288)))) (.mul (.var 6) (.const (-704)))) (.mul (.var 3) (.add (.add (.add (.const (1104)) (.mul (.var 7) (.const (-1104)))) (.mul (.var 6) (.const (-1104)))) (.mul (.var 3) (.add (.add (.const (768)) (.mul (.var 7) (.const (-768)))) (.mul (.var 6) (.const (-768))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part14 (z : Fin 8 → ℝ) :
    evalFin F6Part14 z = Boundary.P5.sourceEval z Certificates.P5.F6Part14 := by
  norm_num [F6Part14,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part14,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 15 of equation 6. -/
def F6Part15 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.add (.add (.const (-224)) (.mul (.var 6) (.const (-64)))) (.mul (.var 3) (.add (.add (.const (4192)) (.mul (.var 6) (.const (160)))) (.mul (.var 3) (.add (.add (.const (960)) (.mul (.var 6) (.const (192)))) (.mul (.var 3) (.add (.const (256)) (.mul (.var 6) (.const (-256)))))))))) (.mul (.var 1) (.add (.add (.add (.const (1504)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (-608)))) (.mul (.var 3) (.const (-2688)))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part15 (z : Fin 8 → ℝ) :
    evalFin F6Part15 z = Boundary.P5.sourceEval z Certificates.P5.F6Part15 := by
  norm_num [F6Part15,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part15,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 16 of equation 6. -/
def F6Part16 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 3) (.add (.add (.mul (.var 7) (.const (-320))) (.mul (.var 6) (.const (-896)))) (.mul (.var 3) (.add (.add (.add (.const (-1728)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (1728)))) (.mul (.var 3) (.add (.add (.const (-512)) (.mul (.var 7) (.const (512)))) (.mul (.var 6) (.const (512))))))))) (.mul (.var 1) (.add (.add (.add (.const (896)) (.mul (.var 7) (.const (192)))) (.mul (.var 6) (.const (128)))) (.mul (.var 3) (.const (1088))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part16 (z : Fin 8 → ℝ) :
    evalFin F6Part16 z = Boundary.P5.sourceEval z Certificates.P5.F6Part16 := by
  norm_num [F6Part16,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part16,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 17 of equation 6. -/
def F6Part17 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 3) (.add (.add (.mul (.var 7) (.const (96))) (.mul (.var 6) (.const (-1088)))) (.mul (.var 3) (.add (.add (.add (.const (768)) (.mul (.var 7) (.const (-768)))) (.mul (.var 6) (.const (-768)))) (.mul (.var 3) (.add (.add (.const (256)) (.mul (.var 7) (.const (-256)))) (.mul (.var 6) (.const (-256))))))))))) (.mul (.var 0) (.add (.add (.const (-48)) (.mul (.var 3) (.add (.const (1664)) (.mul (.var 3) (.const (192)))))) (.mul (.var 1) (.const (512)))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part17 (z : Fin 8 → ℝ) :
    evalFin F6Part17 z = Boundary.P5.sourceEval z Certificates.P5.F6Part17 := by
  norm_num [F6Part17,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part17,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 18 of equation 6. -/
def F6Part18 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.add (.add (.mul (.var 6) (.const (-128))) (.mul (.var 3) (.add (.add (.const (-1408)) (.mul (.var 6) (.const (-128)))) (.mul (.var 3) (.add (.const (-384)) (.mul (.var 6) (.const (384)))))))) (.mul (.var 1) (.add (.add (.add (.const (864)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (32)))) (.mul (.var 3) (.add (.add (.const (640)) (.mul (.var 6) (.const (-640)))) (.mul (.var 3) (.add (.const (192)) (.mul (.var 7) (.const (-192)))))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part18 (z : Fin 8 → ℝ) :
    evalFin F6Part18 z = Boundary.P5.sourceEval z Certificates.P5.F6Part18 := by
  norm_num [F6Part18,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part18,
    Boundary.P5.sourceEval]
  ring

/-- Exact executable coefficient chunk 19 of equation 6. -/
def F6Part19 : Expr := (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 1) (.mul (.var 3) (.mul (.var 3) (.mul (.var 6) (.const (-192))))))) (.mul (.var 0) (.add (.add (.mul (.var 3) (.const (256))) (.mul (.var 1) (.add (.add (.const (64)) (.mul (.var 3) (.const (-256)))) (.mul (.var 1) (.add (.const (384)) (.mul (.var 3) (.add (.const (128)) (.mul (.var 6) (.const (-128)))))))))) (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.const (64))))))))))))))

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F6Part19 (z : Fin 8 → ℝ) :
    evalFin F6Part19 z = Boundary.P5.sourceEval z Certificates.P5.F6Part19 := by
  norm_num [F6Part19,evalFin,finEnv,Expr.eval,Certificates.P5.F6Part19,
    Boundary.P5.sourceEval]
  ring

/-- Executable regularized central equation 6. -/
def F6 : Expr := (.add (.add (.add (.add F6Part0 F6Part1) (.add F6Part2 (.add F6Part3 F6Part4))) (.add (.add F6Part5 F6Part6) (.add F6Part7 (.add F6Part8 F6Part9)))) (.add (.add (.add F6Part10 F6Part11) (.add F6Part12 (.add F6Part13 F6Part14))) (.add (.add F6Part15 F6Part16) (.add F6Part17 (.add F6Part18 F6Part19)))))

/-- Exact source bridge for equation 6, including h=0. -/
theorem eval_F6 (z : Fin 8 → ℝ) :
    evalFin F6 z = Boundary.P5.sourceEval z Certificates.P5.F6 := by
  change ((((evalFin F6Part0 z + evalFin F6Part1 z) + (evalFin F6Part2 z + (evalFin F6Part3 z + evalFin F6Part4 z))) + ((evalFin F6Part5 z + evalFin F6Part6 z) + (evalFin F6Part7 z + (evalFin F6Part8 z + evalFin F6Part9 z)))) + (((evalFin F6Part10 z + evalFin F6Part11 z) + (evalFin F6Part12 z + (evalFin F6Part13 z + evalFin F6Part14 z))) + ((evalFin F6Part15 z + evalFin F6Part16 z) + (evalFin F6Part17 z + (evalFin F6Part18 z + evalFin F6Part19 z))))) = _
  rw [eval_F6Part0, eval_F6Part1, eval_F6Part2, eval_F6Part3, eval_F6Part4, eval_F6Part5, eval_F6Part6, eval_F6Part7, eval_F6Part8, eval_F6Part9, eval_F6Part10, eval_F6Part11, eval_F6Part12, eval_F6Part13, eval_F6Part14, eval_F6Part15, eval_F6Part16, eval_F6Part17, eval_F6Part18, eval_F6Part19]
  simp only [Certificates.P5.F6,map_add]
  ring

/-- Compact exact Horner form of equation 6. -/
def F6Horner : Expr := (.add (.add (.add (.add (.const (21)) (.mul (.var 7) (.const (-16)))) (.mul (.var 6) (.const ((-129/4))))) (.mul (.var 3) (.add (.add (.add (.const (126)) (.mul (.var 7) (.const (-156)))) (.mul (.var 6) (.const (-96)))) (.mul (.var 3) (.add (.add (.add (.const (-36)) (.mul (.var 7) (.const (36)))) (.mul (.var 6) (.const (81)))) (.mul (.var 3) (.add (.add (.add (.const (-384)) (.mul (.var 7) (.const (464)))) (.mul (.var 6) (.const (384)))) (.mul (.var 3) (.mul (.var 3) (.add (.add (.const (288)) (.mul (.var 7) (.const (-288)))) (.mul (.var 6) (.const (-288))))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (110)) (.mul (.var 7) (.const (-80)))) (.mul (.var 6) (.const (-230)))) (.mul (.var 3) (.add (.add (.add (.const (582)) (.mul (.var 7) (.const (-732)))) (.mul (.var 6) (.const (-202)))) (.mul (.var 3) (.add (.add (.add (.const (-276)) (.mul (.var 7) (.const (336)))) (.mul (.var 6) (.const (756)))) (.mul (.var 3) (.add (.add (.add (.const (-1216)) (.mul (.var 7) (.const (1936)))) (.mul (.var 6) (.const (1216)))) (.mul (.var 3) (.add (.add (.add (.const (240)) (.mul (.var 7) (.const (-240)))) (.mul (.var 6) (.const (-240)))) (.mul (.var 3) (.add (.add (.const (1056)) (.mul (.var 7) (.const (-1056)))) (.mul (.var 6) (.const (-1056)))))))))))))) (.mul (.var 1) (.add (.add (.add (.const (12)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (3)))) (.mul (.var 3) (.add (.add (.add (.const (120)) (.mul (.var 7) (.const (-160)))) (.mul (.var 6) (.const (-180)))) (.mul (.var 3) (.add (.add (.add (.const (360)) (.mul (.var 7) (.const (-480)))) (.mul (.var 6) (.const (-360)))) (.mul (.var 3) (.add (.add (.add (.const (-192)) (.mul (.var 7) (.const (192)))) (.mul (.var 6) (.const (192)))) (.mul (.var 3) (.add (.add (.const (-480)) (.mul (.var 7) (.const (480)))) (.mul (.var 6) (.const (480)))))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (145)) (.mul (.var 7) (.const (-156)))) (.mul (.var 6) (.const (-589)))) (.mul (.var 3) (.add (.add (.add (.const (1544)) (.mul (.var 7) (.const (-1128)))) (.mul (.var 6) (.const (280)))) (.mul (.var 3) (.add (.add (.add (.const (-384)) (.mul (.var 7) (.const (924)))) (.mul (.var 6) (.const (2160)))) (.mul (.var 3) (.add (.add (.add (.const (-640)) (.mul (.var 7) (.const (2624)))) (.mul (.var 6) (.const (640)))) (.mul (.var 3) (.add (.add (.add (.const (880)) (.mul (.var 7) (.const (-880)))) (.mul (.var 6) (.const (-880)))) (.mul (.var 3) (.add (.add (.const (1152)) (.mul (.var 7) (.const (-1152)))) (.mul (.var 6) (.const (-1152)))))))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (320)) (.mul (.var 7) (.const (240)))) (.mul (.var 6) (.const (-160)))) (.mul (.var 3) (.add (.add (.add (.const (392)) (.mul (.var 7) (.const (-832)))) (.mul (.var 6) (.const (-1032)))) (.mul (.var 3) (.add (.add (.add (.const (888)) (.mul (.var 7) (.const (-1968)))) (.mul (.var 6) (.const (-888)))) (.mul (.var 3) (.add (.add (.add (.const (-1088)) (.mul (.var 7) (.const (1088)))) (.mul (.var 6) (.const (1088)))) (.mul (.var 3) (.add (.add (.const (-1760)) (.mul (.var 7) (.const (1760)))) (.mul (.var 6) (.const (1760)))))))))))) (.mul (.var 1) (.add (.add (.add (.const (-12)) (.mul (.var 7) (.const (32)))) (.mul (.var 6) (.const (27)))) (.mul (.var 3) (.add (.add (.add (.const (-24)) (.mul (.var 7) (.const (64)))) (.mul (.var 6) (.const (24)))) (.mul (.var 3) (.add (.add (.add (.const (144)) (.mul (.var 7) (.const (-144)))) (.mul (.var 6) (.const (-144)))) (.mul (.var 3) (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192)))))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (-96)) (.mul (.var 7) (.const (-128)))) (.mul (.var 6) (.const (-672)))) (.mul (.var 3) (.add (.add (.add (.const (3520)) (.mul (.var 7) (.const (-712)))) (.mul (.var 6) (.const (896)))) (.mul (.var 3) (.add (.add (.add (.const (576)) (.mul (.var 7) (.const (912)))) (.mul (.var 6) (.const (2496)))) (.mul (.var 3) (.add (.add (.add (.const (960)) (.mul (.var 7) (.const (1408)))) (.mul (.var 6) (.const (-960)))) (.mul (.var 3) (.add (.add (.add (.const (960)) (.mul (.var 7) (.const (-960)))) (.mul (.var 6) (.const (-960)))) (.mul (.var 3) (.add (.add (.const (384)) (.mul (.var 7) (.const (-384)))) (.mul (.var 6) (.const (-384)))))))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (1300)) (.mul (.var 7) (.const (368)))) (.mul (.var 6) (.const (-708)))) (.mul (.var 3) (.add (.add (.add (.const (-176)) (.mul (.var 7) (.const (-1536)))) (.mul (.var 6) (.const (-2192)))) (.mul (.var 3) (.add (.add (.add (.const (-432)) (.mul (.var 7) (.const (-2544)))) (.mul (.var 6) (.const (432)))) (.mul (.var 3) (.add (.add (.add (.const (-2176)) (.mul (.var 7) (.const (2176)))) (.mul (.var 6) (.const (2176)))) (.mul (.var 3) (.add (.add (.const (-1920)) (.mul (.var 7) (.const (1920)))) (.mul (.var 6) (.const (1920)))))))))))) (.mul (.var 1) (.add (.add (.add (.const (40)) (.mul (.var 7) (.const (160)))) (.mul (.var 6) (.const (120)))) (.mul (.var 3) (.add (.add (.add (.const (104)) (.mul (.var 7) (.const (256)))) (.mul (.var 6) (.const (-104)))) (.mul (.var 3) (.add (.add (.add (.const (672)) (.mul (.var 7) (.const (-672)))) (.mul (.var 6) (.const (-672)))) (.mul (.var 3) (.add (.add (.const (704)) (.mul (.var 7) (.const (-704)))) (.mul (.var 6) (.const (-704)))))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.add (.const (-328)) (.mul (.var 7) (.const (-36)))) (.mul (.var 6) (.const (-344)))) (.mul (.var 3) (.add (.add (.add (.const (5216)) (.mul (.var 7) (.const (-160)))) (.mul (.var 6) (.const (672)))) (.mul (.var 3) (.add (.add (.add (.const (1488)) (.mul (.var 7) (.const (288)))) (.mul (.var 6) (.const (1200)))) (.mul (.var 3) (.add (.add (.add (.const (1024)) (.mul (.var 7) (.const (256)))) (.mul (.var 6) (.const (-1024)))) (.mul (.var 3) (.add (.add (.const (320)) (.mul (.var 7) (.const (-320)))) (.mul (.var 6) (.const (-320)))))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (2048)) (.mul (.var 7) (.const (224)))) (.mul (.var 6) (.const (-1024)))) (.mul (.var 3) (.add (.add (.add (.const (-1984)) (.mul (.var 7) (.const (-1184)))) (.mul (.var 6) (.const (-2112)))) (.mul (.var 3) (.add (.add (.add (.const (-2304)) (.mul (.var 7) (.const (-1248)))) (.mul (.var 6) (.const (2304)))) (.mul (.var 3) (.add (.add (.add (.const (-1792)) (.mul (.var 7) (.const (1792)))) (.mul (.var 6) (.const (1792)))) (.mul (.var 3) (.add (.add (.const (-640)) (.mul (.var 7) (.const (640)))) (.mul (.var 6) (.const (640)))))))))))) (.mul (.var 1) (.add (.add (.add (.const (404)) (.mul (.var 7) (.const (272)))) (.mul (.var 6) (.const (188)))) (.mul (.var 3) (.add (.add (.add (.const (704)) (.mul (.var 7) (.const (288)))) (.mul (.var 6) (.const (-704)))) (.mul (.var 3) (.add (.add (.add (.const (1104)) (.mul (.var 7) (.const (-1104)))) (.mul (.var 6) (.const (-1104)))) (.mul (.var 3) (.add (.add (.const (768)) (.mul (.var 7) (.const (-768)))) (.mul (.var 6) (.const (-768)))))))))))))) (.mul (.var 0) (.add (.add (.add (.add (.const (-224)) (.mul (.var 6) (.const (-64)))) (.mul (.var 3) (.add (.add (.const (4192)) (.mul (.var 6) (.const (160)))) (.mul (.var 3) (.add (.add (.const (960)) (.mul (.var 6) (.const (192)))) (.mul (.var 3) (.add (.const (256)) (.mul (.var 6) (.const (-256)))))))))) (.mul (.var 1) (.add (.add (.add (.add (.const (1504)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (-608)))) (.mul (.var 3) (.add (.add (.add (.const (-2688)) (.mul (.var 7) (.const (-320)))) (.mul (.var 6) (.const (-896)))) (.mul (.var 3) (.add (.add (.add (.const (-1728)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (1728)))) (.mul (.var 3) (.add (.add (.const (-512)) (.mul (.var 7) (.const (512)))) (.mul (.var 6) (.const (512)))))))))) (.mul (.var 1) (.add (.add (.add (.const (896)) (.mul (.var 7) (.const (192)))) (.mul (.var 6) (.const (128)))) (.mul (.var 3) (.add (.add (.add (.const (1088)) (.mul (.var 7) (.const (96)))) (.mul (.var 6) (.const (-1088)))) (.mul (.var 3) (.add (.add (.add (.const (768)) (.mul (.var 7) (.const (-768)))) (.mul (.var 6) (.const (-768)))) (.mul (.var 3) (.add (.add (.const (256)) (.mul (.var 7) (.const (-256)))) (.mul (.var 6) (.const (-256)))))))))))))) (.mul (.var 0) (.add (.add (.add (.const (-48)) (.mul (.var 3) (.add (.const (1664)) (.mul (.var 3) (.const (192)))))) (.mul (.var 1) (.add (.add (.add (.const (512)) (.mul (.var 6) (.const (-128)))) (.mul (.var 3) (.add (.add (.const (-1408)) (.mul (.var 6) (.const (-128)))) (.mul (.var 3) (.add (.const (-384)) (.mul (.var 6) (.const (384)))))))) (.mul (.var 1) (.add (.add (.add (.const (864)) (.mul (.var 7) (.const (48)))) (.mul (.var 6) (.const (32)))) (.mul (.var 3) (.add (.add (.const (640)) (.mul (.var 6) (.const (-640)))) (.mul (.var 3) (.add (.add (.const (192)) (.mul (.var 7) (.const (-192)))) (.mul (.var 6) (.const (-192)))))))))))) (.mul (.var 0) (.add (.add (.mul (.var 3) (.const (256))) (.mul (.var 1) (.add (.add (.const (64)) (.mul (.var 3) (.const (-256)))) (.mul (.var 1) (.add (.const (384)) (.mul (.var 3) (.add (.const (128)) (.mul (.var 6) (.const (-128)))))))))) (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.const (64))))))))))))))))))))

theorem eval_F6Horner (z : Fin 8 → ℝ) : evalFin F6Horner z=evalFin F6 z := by
  norm_num [F6Horner,F6,F6Part0,F6Part1,F6Part2,F6Part3,F6Part4,F6Part5,F6Part6,F6Part7,F6Part8,F6Part9,F6Part10,F6Part11,F6Part12,F6Part13,F6Part14,F6Part15,F6Part16,F6Part17,F6Part18,F6Part19,evalFin,finEnv,Expr.eval]
  ring

/-- The seven original divided equations, with parameter first. -/
def system : Fin 7 → Expr := ![F0Horner,F1Horner,F2Horner,F3Horner,F4Horner,F5Horner,F6Horner]

/-- All expression operations admit verified automatic differentiation. -/
theorem check_supported : ∀ i, (system i).checkADSupported = true := by kernel_decide

/-- Source system equality, preserving the parameter/unknown ordering. -/
theorem source_system (h : ℝ) (x : Boundary.P5.Coordinates) :
    Numerics.Parametric.system system h x = Boundary.P5.regularSystem (h,x) := by
  have he : Fin.cons h x = Boundary.P5.arguments h x := by
    ext j
    fin_cases j <;> rfl
  ext i
  fin_cases i
  · change evalFin F0Horner (Fin.cons h x) = _
    rw [eval_F0Horner,eval_F0,he]
    rfl
  · change evalFin F1Horner (Fin.cons h x) = _
    rw [eval_F1Horner,eval_F1,he]
    rfl
  · change evalFin F2Horner (Fin.cons h x) = _
    rw [eval_F2Horner,eval_F2,he]
    rfl
  · change evalFin F3Horner (Fin.cons h x) = _
    rw [eval_F3Horner,eval_F3,he]
    rfl
  · change evalFin F4Horner (Fin.cons h x) = _
    rw [eval_F4Horner,eval_F4,he]
    rfl
  · change evalFin F5Horner (Fin.cons h x) = _
    rw [eval_F5Horner,eval_F5,he]
    rfl
  · change evalFin F6Horner (Fin.cons h x) = _
    rw [eval_F6Horner,eval_F6,he]
    rfl

end polyak.Certificates.Continuation.P5
