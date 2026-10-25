import polyak.CertifiedExamples.Plateaus.KernelExpressions
import polyak.CertifiedExamples.Plateaus.Enclosure

namespace polyak.CertifiedExamples.Plateaus
open LeanCert.Core chebyshev2.Numerics

def blockFirst {a b : ℕ} (i : Fin a) : E (a+b) := .variable (i.castAdd b)
def blockSecond {a b : ℕ} (i : Fin b) : E (a+b) := .variable (i.natAdd a)

theorem blockFirst_value {a b : ℕ} (v : Fin a → ℝ) (w : Fin b → ℝ) (i : Fin a) :
    (blockFirst (b:=b) i).value (Fin.append v w)=v i := by
  simp only [blockFirst,IntervalExpr.value,Fin.append_left]

theorem blockSecond_value {a b : ℕ} (v : Fin a → ℝ) (w : Fin b → ℝ) (i : Fin b) :
    (blockSecond (a:=a) i).value (Fin.append v w)=w i := by
  simp only [blockSecond,IntervalExpr.value,Fin.append_right]

theorem append_mem {a b : ℕ} (v : Fin a → ℝ) (w : Fin b → ℝ)
    (A : Fin a → IntervalRat) (B : Fin b → IntervalRat)
    (hv : ∀i,v i∈A i) (hw : ∀i,w i∈B i) :
    ∀i,Fin.append v w i∈Fin.append A B i := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [Fin.append_left] using hv i
  | right i => simpa only [Fin.append_right] using hw i

def matrixBlock {d a : ℕ} (i j : Fin d) : E (d*d+a) :=
  blockFirst (finProdFinEquiv (i,j))

theorem matrixBlock_value {d a : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin a → ℝ) (i j : Fin d) :
    (matrixBlock (a:=a) i j).value (Fin.append (matrixPoint M) v)=M i j := by
  rw [matrixBlock,blockFirst_value]
  simp only [matrixPoint,Equiv.symm_apply_apply]

theorem matrixBlock_values {d a : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin a → ℝ) :
    Matrix.of (fun i j=>(matrixBlock (a:=a) i j).value (Fin.append (matrixPoint M) v))=M := by
  ext i j
  exact matrixBlock_value M v i j

theorem moments2_block_value (M : Matrix (Fin 2) (Fin 2) ℝ) (t : Fin 2 → ℝ) (i : Fin 2) :
    (moments2Expr (matrixBlock (a:=2)) (blockSecond (a:=4)) i).value
      (Fin.append (matrixPoint M) t)=slopeMoments M t i := by
  rw [moments2Expr_value,matrixBlock_values]
  simp only [blockSecond_value]

theorem moments3_block_value (M : Matrix (Fin 3) (Fin 3) ℝ) (t : Fin 3 → ℝ) (i : Fin 3) :
    (moments3Expr (matrixBlock (a:=3)) (blockSecond (a:=9)) i).value
      (Fin.append (matrixPoint M) t)=slopeMoments M t i := by
  rw [moments3Expr_value,matrixBlock_values]
  simp only [blockSecond_value]

end polyak.CertifiedExamples.Plateaus
