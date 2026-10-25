import polyak.CertifiedExamples.Exact313.Code
import polyak.Numerics.Parametric.Contract

/-! The genuine three-dimensional contact system in the actual Xi coefficients.
The multiplier ratio is eliminated by its first exact contact equation.
Clearing its denominator leaves three polynomial equations, with their actual
Frechet derivative checked by the existing AD semantics. -/
namespace polyak.CertifiedExamples.Exact313.SystemCode
open LeanCert.Core LeanCert.Engine Numerics.Parametric

def xi (c : Expr) : Expr := .add (.add (.var 1) (.mul (.var 2) c))
  (.mul (.var 3) (.pow c 2))
def xiD (c : Expr) : Expr := .add (.var 2) (.mul (.const 2) (.mul (.var 3) c))
def w (c : Expr) : Expr := .mul (.const 8) (.mul (.pow c 2) (.add (.const 1) c))
def wD (c : Expr) : Expr := .mul (.const 8) (.mul c (.add (.const 2) (.mul (.const 3) c)))
def z (c : Expr) : Expr := .sub (.mul (.const 8) (.pow c 3)) (.mul (.const 4) c)
def zD (c : Expr) : Expr := .sub (.mul (.const 24) (.pow c 2)) (.const 4)
def ratioNumerator : Expr := .sub (.add (.const 1) (Code.cosine 6)) (xi (Code.cosine 6))
def ratioDenominator : Expr := .add (.mul (xi (Code.cosine 6)) (w (Code.cosine 6)))
  (.mul (.add (.const 1) (Code.cosine 6)) (z (Code.cosine 6)))
def contact (c : Expr) : Expr :=
  .add (.mul ratioDenominator (.sub (xi c) (.add (.const 1) c)))
    (.mul ratioNumerator (.add (.mul (xi c) (w c)) (.mul (.add (.const 1) c) (z c))))
def slope (c : Expr) : Expr :=
  .add (.mul ratioDenominator (.sub (xiD c) (.const 1)))
    (.mul ratioNumerator (.add (.add (.mul (xiD c) (w c)) (.mul (xi c) (wD c)))
      (.add (z c) (.mul (.add (.const 1) c) (zD c)))))
def equations : Fin 3 → Expr :=
  ![contact (Code.cosine 4),slope (Code.cosine 6),slope (Code.cosine 4)]

theorem supported : ∀i,ADSupported (equations i) := by
  intro i
  apply (Expr.checkADSupported_eq_true_iff _).mp
  fin_cases i <;> rfl

def nonsingularCheck (I : IntervalRat) (X : Fin 3 → IntervalRat)
    (Y : Matrix (Fin 3) (Fin 3) ℚ) (cfg : DyadicConfig) : Bool :=
  dyadicJacobianSucceeded equations I X cfg &&
    decide (intervalMatrixBound (preconditionedJacobian Y (dyadicJacobian equations I X cfg))<1)

noncomputable section

theorem nonsingularCheck_sound (I : IntervalRat) (X : Fin 3 → IntervalRat)
    (Y : Matrix (Fin 3) (Fin 3) ℚ) (cfg : DyadicConfig)
    (h : nonsingularCheck I X Y cfg=true) {s : ℝ} {x : Fin 3 → ℝ}
    (hs : s∈I) (hx : FinBoxMem x X) :
    (fderiv ℝ (system equations s) x).IsInvertible := by
  simp only [nonsingularCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  have hJ := dyadicJacobian_mem equations supported I X cfg h.1 hs hx
  apply isInvertible_of_defect (matrixCLM (Y.map fun q => (q : ℝ)))
  rw [←newton_fderiv _ equations supported]
  exact (fderiv_norm_le_of_enclosure equations supported Y _ s x hJ).trans_lt
    (by exact_mod_cast h.2)

end
end polyak.CertifiedExamples.Exact313.SystemCode
