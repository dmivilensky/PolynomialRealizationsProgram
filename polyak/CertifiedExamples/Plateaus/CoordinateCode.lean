import polyak.CertifiedExamples.Plateaus.Coordinates
import polyak.CertifiedExamples.Plateaus.SymbolComponents

/-! Source-derived polynomial derivatives and their executable expressions.
The first jets used in the slope system are genuine derivatives. -/
namespace polyak.CertifiedExamples.Plateaus
open LeanCert.Core LeanCert.Engine chebyshev2.Numerics
open scoped BigOperators

def hornerExpr {d : ℕ} (c : E d) : List ℚ → E d
  | [] => cst 0
  | q::qs => plus (cst q) (times c (hornerExpr c qs))

def qpolyExpr {d : ℕ} (p : QPoly) (c : E d) : E d := hornerExpr c p.coeffs.toList

def lagComponentCode (n : ℤ) (i : Fin 4) : QPoly :=
  ((QPoly.constant 1).add (qneg QPoly.X)).mul (componentCode n i)

def coordinateWeightExpr {d : ℕ} (X : Fin 3 → E d) (i : Fin 4) : E d :=
  if h : i.val<3 then X ⟨i.val,h⟩ else cst 1

def coordinateCodeExpr {d : ℕ} (X : Fin 3 → E d) (n : ℤ) (order : ℕ) (c : E d) : E d :=
  let e := fun i : Fin 4 => times (coordinateWeightExpr X i)
    (qpolyExpr ((QPoly.derivative^[order]) (lagComponentCode n i)) c)
  plus (plus (plus (e 0) (e 1)) (e 2)) (e 3)

noncomputable section
open Polynomial General Levels

def coordinateWeight (X : Fin 3 → ℝ) (i : Fin 4) : ℝ :=
  if h : i.val<3 then X ⟨i.val,h⟩ else 1

def coordinateCodeValue (X : Fin 3 → ℝ) (n : ℤ) (order : ℕ) (c : ℝ) : ℝ :=
  ∑ i, coordinateWeight X i *
    Polynomial.aeval c ((QPoly.derivative^[order]) (lagComponentCode n i)).toPoly

theorem hornerExpr_value {d : ℕ} (c : E d) (qs : List ℚ) (v : Fin d → ℝ) :
    (hornerExpr c qs).value v =
      ∑ j ∈ Finset.range qs.length,(qs.getD j 0 : ℝ)*(c.value v)^j := by
  induction qs with
  | nil => simp [hornerExpr,cst,IntervalExpr.value]
  | cons q qs ih =>
    simp only [hornerExpr,cst,plus,times,IntervalExpr.value,ih,List.length_cons]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_zero,List.getD_cons_succ,pow_zero,mul_one]
    rw [Finset.mul_sum,add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem qpolyExpr_value {d : ℕ} (p : QPoly) (c : E d) (v : Fin d → ℝ) :
    (qpolyExpr p c).value v=Polynomial.aeval (c.value v) p.toPoly := by
  rw [qpolyExpr,hornerExpr_value,QPoly.aeval_toPoly_eq_sum]

theorem coordinateCodeExpr_value {d : ℕ} (X : Fin 3 → E d) (n : ℤ) (order : ℕ)
    (c : E d) (v : Fin d → ℝ) :
    (coordinateCodeExpr X n order c).value v =
      coordinateCodeValue (fun i=>(X i).value v) n order (c.value v) := by
  norm_num [coordinateCodeExpr,coordinateCodeValue,coordinateWeightExpr,coordinateWeight,
    plus,times,cst,IntervalExpr.value,qpolyExpr_value,Fin.sum_univ_succ]
  ring

theorem coordinateCodeValue_zero (X : Fin 3 → ℝ) (n : ℤ) (c : ℝ) :
    coordinateCodeValue X n 0 c=coordinateLag X n c := by
  unfold coordinateCodeValue
  simp only [Function.iterate_zero,id_eq,lagComponentCode,QPoly.toPoly_mul,
    QPoly.toPoly_add,QPoly.toPoly_constant,qneg,QPoly.toPoly_mul,QPoly.toPoly_constant,
    QPoly.toPoly_X,map_mul,map_add,aeval_C,aeval_X,componentCode_value]
  norm_num [Fin.sum_univ_succ,coordinateWeight,componentValue]
  have h := ModeLocking.TwoLag.W_identity n.natAbs c
  unfold coordinateLag coefficientValue
  linear_combination (X 0+X 1*c+X 2*c^2)*h

theorem coordinateCodeValue_deriv (X : Fin 3 → ℝ) (n : ℤ) (order : ℕ) :
    deriv (coordinateCodeValue X n order)=coordinateCodeValue X n (order+1) := by
  funext c
  unfold coordinateCodeValue
  rw [deriv_fun_sum (fun i _ =>
    (((QPoly.derivative^[order]) (lagComponentCode n i)).toPoly.hasDerivAt_aeval c).differentiableAt.const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [deriv_const_mul_field,Polynomial.deriv_aeval,←QPoly.toPoly_derivative]
  simp only [Function.iterate_succ_apply']

theorem coordinateCodeValue_one (X : Fin 3 → ℝ) (n : ℤ) :
    coordinateCodeValue X n 1=deriv (coordinateLag X n) := by
  have he : coordinateCodeValue X n 0=coordinateLag X n := funext (coordinateCodeValue_zero X n)
  rw [←he,coordinateCodeValue_deriv]

end
end polyak.CertifiedExamples.Plateaus
