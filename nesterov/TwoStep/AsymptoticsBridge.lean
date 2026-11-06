import nesterov.TwoStep.AsymptoticsModel
import nesterov.Slow.Model
import nesterov.Momentum.Stationary
import Mathlib.Topology.Order.LeftRight

/-! A literal accelerated parameter family is a second-order family of actual methods.
Only its value at the limiting endpoint is filled in; no regularity beyond the
article's parameter limits is imposed. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set Polynomial
open scoped Topology

def endpointPatch (f : ℝ→ℝ) (v ε : ℝ) : ℝ := if ε=0 then v else f ε

theorem endpointPatch_tendsto {f : ℝ→ℝ} {v : ℝ}
    (hf : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 v)) :
    Tendsto (endpointPatch f v) (𝓝[>] (0:ℝ)) (𝓝 v) := by
  apply hf.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  simp only [endpointPatch,ite_eq_right (ne_of_gt hε)]

theorem endpointPatch_continuousWithinAt {f : ℝ→ℝ} {v : ℝ}
    (hf : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 v)) :
    ContinuousWithinAt (endpointPatch f v) (Ici 0) 0 := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  simpa only [ContinuousWithinAt,endpointPatch,ite_true] using endpointPatch_tendsto hf

theorem method_queryPolynomial (β τ h : ℝ) (hh : h≠0) :
    (Momentum.method β τ h hh).queryPolynomial=C (-τ)*1+C (1+τ)*X := by
  change (∑ j : Fin 2,monomial j.val (![-τ,1+τ] j))=_
  simp only [Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Fin.val_zero,Fin.val_one,
    ←C_mul_X_pow_eq_monomial,pow_zero,pow_one]

theorem method_recurrencePolynomial (β τ h : ℝ) (hh : h≠0) :
    (Momentum.method β τ h hh).recurrencePolynomial=
      C (-β/h)*1+C ((1+β)/h)*X+C (-1/h)*X^2 := by
  change (∑ j : Fin 3,monomial j.val (![-β/h,(1+β)/h,-1/h] j))=_
  simp only [Fin.sum_univ_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Fin.val_zero,Fin.val_one,Fin.val_two,←C_mul_X_pow_eq_monomial,pow_zero,pow_one]
  rfl

namespace Scaling
variable {θ y τ : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ)

def endpointBeta : ℝ→ℝ := endpointPatch (fun ε=>(F.tuning ε).beta) 1
def endpointTau : ℝ→ℝ := endpointPatch (fun ε=>(F.tuning ε).tau) τ
def endpointStep : ℝ→ℝ := endpointPatch (fun ε=>(F.tuning ε).stepSize) y

theorem endpointStep_pos (ε : ℝ) : 0<F.endpointStep ε := by
  unfold endpointStep endpointPatch
  split_ifs
  · exact F.step_pos
  · exact (F.tuning ε).step_pos

def endpointMethod (ε : ℝ) : StationaryMethod := Momentum.method
  (F.endpointBeta ε) (F.endpointTau ε) (F.endpointStep ε) (F.endpointStep_pos ε).ne'

theorem endpointMethod_eq {ε : ℝ} (hε : ε≠0) :
    F.endpointMethod ε=Momentum.method (F.tuning ε).beta (F.tuning ε).tau
      (F.tuning ε).stepSize (F.tuning ε).step_pos.ne' := by
  unfold endpointMethod endpointBeta endpointTau endpointStep endpointPatch
  simp only [ite_eq_right hε]

private theorem endpoint_query_cont (n : ℕ) :
    ContinuousWithinAt (fun ε=>(F.endpointMethod ε).queryPolynomial.coeff n) (Ici 0) 0 := by
  have ht := endpointPatch_continuousWithinAt F.tau_tendsto
  have h₀ := ht.neg.mul_const ((1 : Polynomial ℝ).coeff n)
  have h₁ := ((continuousWithinAt_const (b:=(1:ℝ))).add ht).mul_const ((X : Polynomial ℝ).coeff n)
  convert h₀.add h₁ using 1
  funext ε
  simp only [endpointMethod,method_queryPolynomial,coeff_add,coeff_C_mul,endpointTau]
  rfl

private theorem endpoint_recurrence_cont (n : ℕ) :
    ContinuousWithinAt (fun ε=>(F.endpointMethod ε).recurrencePolynomial.coeff n) (Ici 0) 0 := by
  have hb := endpointPatch_continuousWithinAt F.beta_tendsto
  have hh := endpointPatch_continuousWithinAt F.step_tendsto
  have hne : F.endpointStep 0≠0 := (F.endpointStep_pos 0).ne'
  have h₀ := (hb.neg.div hh hne).mul_const ((1 : Polynomial ℝ).coeff n)
  have h₁ := (((continuousWithinAt_const (b:=(1:ℝ))).add hb).div hh hne).mul_const ((X : Polynomial ℝ).coeff n)
  have h₂ := ((continuousWithinAt_const (b:=(-1:ℝ))).div hh hne).mul_const ((X^2 : Polynomial ℝ).coeff n)
  convert (h₀.add h₁).add h₂ using 1
  funext ε
  simp only [endpointMethod,method_recurrencePolynomial,coeff_add,coeff_C_mul,endpointBeta,endpointStep]
  rfl

/-- The endpoint extension implements Definition second using the actual source executor. -/
def toSecondOrderFamily (he : F.epsilon=id) : Slow.SecondOrderFamily θ y where
  method := F.endpointMethod
  memory := 2
  memory_two := le_rfl
  fixed_memory := fun _=>rfl
  query_cont := F.endpoint_query_cont
  recurrence_cont := F.endpoint_recurrence_cont
  theta_pos := F.theta_pos
  step_pos := F.step_pos
  q0 := C (-1/y)
  initial_factor := by
    unfold endpointMethod
    rw [method_recurrencePolynomial]
    simp only [endpointBeta,endpointStep,endpointPatch,ite_true,neg_div,mul_one]
    have hc : (1+1)/y=(-1/y)*(-2) := by ring
    rw [hc,map_mul]
    simp only [map_neg,map_ofNat,map_one]
    simp only [neg_div,one_div,C_neg]
    ring
  q0_one := by simp
  beta := F.endpointBeta
  beta_zero := by simp [endpointBeta,endpointPatch]
  beta_root := by
    filter_upwards [self_mem_nhdsWithin] with ε _hε
    unfold endpointMethod
    rw [method_recurrencePolynomial]
    simp only [eval_add,eval_mul,eval_C,eval_X,eval_pow,mul_one]
    ring
  beta_slow := by
    have ht := F.theta_tendsto
    rw [he] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0<ε at hε
    simp only [endpointBeta,endpointPatch,ite_eq_right (ne_of_gt hε),id_eq]

theorem toSecondOrderFamily_method_eq (he : F.epsilon=id) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.toSecondOrderFamily he).method ε=
      Momentum.method (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize
        (F.tuning ε).step_pos.ne' := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact F.endpointMethod_eq (ne_of_gt hε)

end Scaling
end
end nesterov.TwoStep
