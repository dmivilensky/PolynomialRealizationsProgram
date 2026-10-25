import polyak.CertifiedExamples.Plateaus.SymbolComponents
import polyak.CertifiedExamples.Plateaus.Bernstein

/-! Independent semantic identity for aligned Bernstein component tables. -/
namespace polyak.CertifiedExamples.Plateaus
open LeanCert.Core LeanCert.Engine

abbrev componentIndex {r:ℕ} (i:Fin (r*4)) : Fin r×Fin 4 := finProdFinEquiv.symm i

def sourceFamily {r:ℕ} (n:Fin r→ℤ) (order:ℕ) (i:Fin (r*4)) : QPoly :=
  (QPoly.derivative^[order]) (componentCode (n (componentIndex i).1) (componentIndex i).2)

def familyIdentityCheck {r:ℕ} (n:Fin r→ℤ) (order:ℕ) (P:Fin (r*4)→QPoly) : Bool :=
  decide (∀i,(P i).trim=(sourceFamily n order i).trim)

def weightBoxes {r:ℕ} (X:Fin 3→IntervalRat) (lam:Fin r→IntervalRat) (i:Fin (r*4)) : IntervalRat :=
  IntervalRat.mul (lam (componentIndex i).1)
    (if h:(componentIndex i).2.val<3 then X ⟨(componentIndex i).2.val,h⟩ else IntervalRat.singleton 1)

noncomputable section
open General Levels Polynomial
open scoped BigOperators

def coefficientVector (q:Tuning) : Fin 3→ℝ :=
  ![(Chart.coefficients q).c0,(Chart.coefficients q).c1,(Chart.coefficients q).c2]

def weightValues {r:ℕ} (X:Fin 3→ℝ) (lam:Fin r→ℝ) (i:Fin (r*4)) : ℝ :=
  lam (componentIndex i).1*
    (if h:(componentIndex i).2.val<3 then X ⟨(componentIndex i).2.val,h⟩ else 1)

def weightedFunction {m:ℕ} (w:Fin m→ℝ) (P:Fin m→QPoly) (c:ℝ) : ℝ :=
  ∑i,w i*Polynomial.aeval c (P i).toPoly

def indexedSymbol {r:ℕ} (q:Tuning) (n:Fin r→ℤ) (lam:Fin r→ℝ) (c:ℝ) : ℝ :=
  ∑j,lam j*dividedLag q (n j) c

theorem weightValues_mem {r:ℕ} (X:Fin 3→ℝ) (lam:Fin r→ℝ)
    (XB:Fin 3→IntervalRat) (lamB:Fin r→IntervalRat)
    (hX:∀i,X i∈XB i) (hlam:∀j,lam j∈lamB j) :
    ∀i,weightValues X lam i∈weightBoxes XB lamB i := by
  intro i
  unfold weightValues weightBoxes
  apply IntervalRat.mem_mul (hlam _)
  split
  · exact hX _
  · simpa using IntervalRat.mem_singleton (1:ℚ)

theorem familyIdentity_sound {r:ℕ} (n:Fin r→ℤ) (order:ℕ) (P:Fin (r*4)→QPoly)
    (hc:familyIdentityCheck n order P=true) : ∀i,(P i).toPoly=(sourceFamily n order i).toPoly := by
  have h:∀i,(P i).trim=(sourceFamily n order i).trim:=of_decide_eq_true hc
  intro i
  rw [←QPoly.toPoly_trim (P i),h i,QPoly.toPoly_trim]

theorem component_sum (q:Tuning) (n:ℤ) (c:ℝ) :
    (∑i:Fin 4,(if h:i.val<3 then coefficientVector q ⟨i.val,h⟩ else 1)*
      componentValue n i c)=dividedLag q n c := by
  norm_num [Fin.sum_univ_succ,componentValue,coefficientVector]
  unfold dividedLag
  rw [←Chart.eval_coefficients]
  unfold Chart.Coefficients.eval
  ring

theorem sourceFamily_zero (r:ℕ) (q:Tuning) (n:Fin r→ℤ) (lam:Fin r→ℝ) :
    weightedFunction (weightValues (coefficientVector q) lam) (sourceFamily n 0)=indexedSymbol q n lam := by
  funext c
  unfold weightedFunction
  rw [←finProdFinEquiv.sum_comp]
  simp only [sourceFamily,componentIndex,Equiv.symm_apply_apply,Function.iterate_zero, id_eq,
    weightValues,componentCode_value,Fintype.sum_prod_type]
  unfold indexedSymbol
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum,component_sum]

theorem weightedFunction_deriv {m:ℕ} (w:Fin m→ℝ) (P:Fin m→QPoly) :
    deriv (weightedFunction w P)=weightedFunction w (fun i=>(P i).derivative) := by
  funext c
  unfold weightedFunction
  rw [deriv_fun_sum (fun i _=>((P i).toPoly.hasDerivAt_aeval c).differentiableAt.const_mul (w i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [deriv_const_mul_field,Polynomial.deriv_aeval,QPoly.toPoly_derivative]

theorem sourceFamily_deriv {r:ℕ} (w:Fin (r*4)→ℝ) (n:Fin r→ℤ) (order:ℕ) :
    deriv (weightedFunction w (sourceFamily n order))=weightedFunction w (sourceFamily n (order+1)) := by
  rw [weightedFunction_deriv]
  congr 1
  funext i
  simp only [sourceFamily,Function.iterate_succ_apply']

theorem sourceFamily_second (r:ℕ) (q:Tuning) (n:Fin r→ℤ) (lam:Fin r→ℝ) :
    deriv^[2] (indexedSymbol q n lam)=
      weightedFunction (weightValues (coefficientVector q) lam) (sourceFamily n 2) := by
  rw [←sourceFamily_zero r q n lam]
  change deriv (deriv (weightedFunction _ (sourceFamily n 0)))=_
  rw [sourceFamily_deriv,sourceFamily_deriv]

theorem indexedSymbol_analytic {r:ℕ} (q:Tuning) (n:Fin r→ℤ) (lam:Fin r→ℝ) (c:ℝ) :
    AnalyticAt ℝ (indexedSymbol q n lam) c := by
  rw [←sourceFamily_zero r q n lam]
  unfold weightedFunction
  have he : (fun x=>∑i,weightValues (coefficientVector q) lam i*
      Polynomial.aeval x (sourceFamily n 0 i).toPoly)=
      ∑i,fun x=>weightValues (coefficientVector q) lam i*
        Polynomial.aeval x (sourceFamily n 0 i).toPoly := by funext x;simp
  rw [he]
  apply Finset.analyticAt_sum
  intro i _
  exact analyticAt_const.mul (analyticAt_id.aeval_polynomial (sourceFamily n 0 i).toPoly)

end
end polyak.CertifiedExamples.Plateaus
