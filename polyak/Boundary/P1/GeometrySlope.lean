import polyak.Numerics.Parametric.DerivativeTwo

/-!
Article: (p1physical), strict decrease of 1/2+zB at the spiral junction.
Use: checked AD enclosures bound the actual Cramer numerator, not an unrelated matrix.
-/
namespace polyak.Boundary.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric

private def determinantInterval (J : Matrix (Fin 2) (Fin 2) IntervalRat) : IntervalRat :=
  (J 0 0 |>.mul (J 1 1)).sub (J 0 1 |>.mul (J 1 0))
private def numeratorInterval (J : Matrix (Fin 2) (Fin 2) IntervalRat)
    (p : Fin 2 → IntervalRat) : IntervalRat :=
  (J 1 0 |>.mul (p 0)).sub (J 0 0 |>.mul (p 1))

def geometrySlopeCheck (F : Fin 2 → Expr) (I : IntervalRat) (X : Fin 2 → IntervalRat)
    (cfg : DyadicConfig) : Bool :=
  let J := dyadicJacobian F I X cfg
  let p := fun i => outcome (dyadicDerivative (F i) (finBoxEnv (box I X)) 0 cfg)
  let D := determinantInterval J
  let N := ((X 1).mul D).add (I.mul (numeratorInterval J p))
  dyadicJacobianSucceeded F I X cfg &&
    decide (∀ i, succeeded (dyadicDerivative (F i) (finBoxEnv (box I X)) 0 cfg)=true) &&
    decide (0<D.lo) && decide (N.hi<0)

noncomputable section

theorem geometrySlopeCheck_sound (F : Fin 2 → Expr) (hF : ∀ i, ADSupported (F i))
    (I : IntervalRat) (X : Fin 2 → IntervalRat) (cfg : DyadicConfig)
    (hc : geometrySlopeCheck F I X cfg=true)
    {s : ℝ} {x v : Fin 2 → ℝ} (hs : s∈I) (hx : FinBoxMem x X)
    (he : (jacobian F s x).mulVec v= -parameterDerivative F s x) :
    x 1+s*v 1<0 := by
  simp only [geometrySlopeCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hj := dyadicJacobian_mem F hF I X cfg hc.1.1.1 hs hx
  have hp := parameterDerivative_mem F I X cfg hc.1.1.2 hs hx
  have hd : determinantTwo (jacobian F s x)∈determinantInterval (dyadicJacobian F I X cfg) :=
    IntervalRat.mem_sub (IntervalRat.mem_mul (hj 0 0) (hj 1 1))
      (IntervalRat.mem_mul (hj 0 1) (hj 1 0))
  have hn : cramerNumeratorB (jacobian F s x) (parameterDerivative F s x)∈
      numeratorInterval (dyadicJacobian F I X cfg)
        (fun i => outcome (dyadicDerivative (F i) (finBoxEnv (box I X)) 0 cfg)) :=
    IntervalRat.mem_sub (IntervalRat.mem_mul (hj 1 0) (hp 0))
      (IntervalRat.mem_mul (hj 0 0) (hp 1))
  have hN := IntervalRat.mem_add (IntervalRat.mem_mul (hx 1) hd) (IntervalRat.mem_mul hs hn)
  have hDpos : 0<determinantTwo (jacobian F s x) :=
    lt_of_lt_of_le (by exact_mod_cast hc.1.2) hd.1
  have hNneg : x 1*determinantTwo (jacobian F s x)+
      s*cramerNumeratorB (jacobian F s x) (parameterDerivative F s x)<0 :=
    lt_of_le_of_lt hN.2 (by exact_mod_cast hc.2)
  have hcB := cramer_B (jacobian F s x) (parameterDerivative F s x) v he
  rw [← hcB] at hNneg
  have hid : x 1*determinantTwo (jacobian F s x)+s*(determinantTwo (jacobian F s x)*v 1)=
      determinantTwo (jacobian F s x)*(x 1+s*v 1) := by ring
  rw [hid] at hNneg
  by_contra hh
  have hn0 : 0≤x 1+s*v 1 := le_of_not_gt hh
  exact (not_lt_of_ge (mul_nonneg hDpos.le hn0)) hNneg

end
end polyak.Boundary.P1
