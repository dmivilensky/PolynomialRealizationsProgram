import polyak.CertifiedExamples.Plateaus.Enclosure
import polyak.CertifiedExamples.Plateaus.SymbolSemantics
import polyak.Farey.Examples.ThirteenContracts

/-! Independent coefficient formulas and elementary sufficient gap tests. -/
namespace polyak.CertifiedExamples.Plateaus
open LeanCert.Core chebyshev2.Numerics

def coefficientExpr (y b:ℚ) : Fin 3→E 1 :=
  let x:=divideE (cst y) (.variable 0)
  let A:=minus (cst (1+b)) (divideE (plus x (cst y)) (cst 2))
  let B:=divideE (minus (cst y) x) (cst 2)
  let den:=times (times (cst 2) B) (cst (1-b))
  ![divideE (minus (minus (square B) (square (cst (1-b)))) (square A)) den,
    divideE (times (times (cst 2) A) (cst (1+b))) den,
    divideE (cst (-4*b)) den]

def coefficientBox (I:IntervalRat) : Fin 1→IntervalRat:=fun _=>I

def gapTestExpr (i:Fin 5) : E 3 :=
  let C0:E 3:=.variable 0
  let C1:E 3:=.variable 1
  let C2:E 3:=.variable 2
  let D:=plus (square (minus (cst 1) C1)) (times (times (cst 4) C2) (minus (cst 1) C0))
  ![.neg C2,D,minus (cst ((41/50)^2)) D,
    minus (minus C1 (cst 1)) (cst (41/50)),
    minus (times (cst (307/1000)) (times (cst (-2)) C2))
      (plus (minus C1 (cst 1)) (cst (41/50)))] i

noncomputable section
open General Levels Farey.Examples

theorem coefficientExpr_actual (q:Tuning) (y b:ℚ) (hy:q.y=(y:ℝ)) (hb:q.beta=(b:ℝ))
    (i:Fin 3) : (coefficientExpr y b i).value (fun _=>q.kappa)=coefficientVector q i := by
  fin_cases i <;>
    simp [coefficientExpr,coefficientVector,plus,minus,times,divideE,cst,square,IntervalExpr.value,
      Chart.coefficients,Tuning.A,Tuning.B,Tuning.x,hy,hb,div_eq_mul_inv,sub_eq_add_neg]

theorem Xi_mem_of_checks (q:Tuning) (y b:ℚ) (I:IntervalRat) (X:Fin 3→IntervalRat)
    (hy:q.y=(y:ℝ)) (hb:q.beta=(b:ℝ)) (hk:q.kappa∈I)
    (hc:∀i,enclosed (coefficientExpr y b i) (coefficientBox I) (X i)=true) :
    ∀i,coefficientVector q i∈X i := by
  intro i
  have h:=enclosed_sound (coefficientExpr y b i) (coefficientBox I) (X i) (hc i)
    (fun _=>q.kappa) (fun _=>hk)
  rwa [coefficientExpr_actual q y b hy hb i] at h

private theorem cos_fifth_lower : (307:ℝ)/1000<Chart.boundaryCosine 5 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  have hn:=Real.sqrt_nonneg (5:ℝ)
  unfold Chart.boundaryCosine Chart.boundaryAngle
  norm_num only [Nat.cast_ofNat]
  rw [show 2*Real.pi/(5:ℝ)=2*(Real.pi/5) by ring,Real.cos_two_mul,Real.cos_pi_div_five]
  nlinarith

private theorem gapTest_values (q:Tuning)
    (h:∀i:Fin 5,0<(gapTestExpr i).value (coefficientVector q)) :
    (Chart.coefficients q).c2<0 ∧ 0<Chart.gapDiscriminant (Chart.coefficients q) ∧
      Chart.gapDiscriminant (Chart.coefficients q)<(41/50)^2 ∧
      41/50<(Chart.coefficients q).c1-1 ∧
      (Chart.coefficients q).c1-1+41/50<(307/1000)*(-2*(Chart.coefficients q).c2) := by
  have h0:=h 0;have h1:=h 1;have h2:=h 2;have h3:=h 3;have h4:=h 4
  norm_num [gapTestExpr,coefficientVector,plus,minus,times,cst,square,IntervalExpr.value] at h0 h1 h2 h3 h4
  unfold Chart.gapDiscriminant
  constructor
  · linarith
  constructor
  · exact h1
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem gap_four_of_polynomial_tests (q:Tuning)
    (h:∀i:Fin 5,0<(gapTestExpr i).value (coefficientVector q)) : Geometry.Gap 4 q := by
  obtain ⟨hc,hD,hupper,hl,hr⟩:=gapTest_values q h
  have hs:=Real.sq_sqrt hD.le
  have hn:=Real.sqrt_nonneg (Chart.gapDiscriminant (Chart.coefficients q))
  have hroot : Real.sqrt (Chart.gapDiscriminant (Chart.coefficients q))<41/50 := by nlinarith
  apply gap_four_of_checks
  refine ⟨hc,hD,?_,?_⟩
  · have hz : Chart.boundaryCosine 4=0 := by
      unfold Chart.boundaryCosine Chart.boundaryAngle
      norm_num [show 2*Real.pi/(4:ℝ)=Real.pi/2 by ring,Real.cos_pi_div_two]
    rw [hz]
    unfold Chart.leftRoot
    rw [lt_div_iff₀ (by linarith)]
    linarith
  · apply lt_trans (b:=(307:ℝ)/1000) _ cos_fifth_lower
    unfold Chart.rightRoot
    rw [div_lt_iff₀ (by linarith)]
    linarith

theorem gap_four_of_checked_boxes (q:Tuning) (X:Fin 3→IntervalRat)
    (hX:∀i,coefficientVector q i∈X i)
    (hc:∀i:Fin 5,(IntervalExpr.neg (gapTestExpr i)).strictNegative X=true) : Geometry.Gap 4 q := by
  apply gap_four_of_polynomial_tests
  intro i
  have h:=(IntervalExpr.neg (gapTestExpr i)).strictNegative_sound X (hc i) hX
  change -(gapTestExpr i).value (coefficientVector q)<0 at h
  linarith

end
end polyak.CertifiedExamples.Plateaus
