import nesterov.Slow.ScaledLimit
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! Uniform evaluation control for bounded-degree coefficient-continuous families. -/
namespace nesterov.Slow
noncomputable section
open Polynomial Filter Set Asymptotics
open scoped Topology

lemma eval_sub_eval_one (p : Polynomial ℝ) (z : ℂ) :
    p.eval₂ Complex.ofRealHom z-((p.eval (1:ℝ):ℝ):ℂ)=
      (z-1)*(p /ₘ (X-C 1)).eval₂ Complex.ofRealHom z := by
  have hh := congrArg (fun q : Polynomial ℝ=>q.eval₂ Complex.ofRealHom z)
    (modByMonic_add_div p (X-C 1))
  simp only [modByMonic_X_sub_C_eq_C_eval,eval₂_add,eval₂_mul,eval₂_sub,eval₂_X,eval₂_C] at hh
  have hc (r : ℝ) : Complex.ofRealHom r=(r:ℂ) := rfl
  simp only [hc,Complex.ofReal_one] at hh
  linear_combination -hh

lemma eval_sub_eval_one_isBigO {A : Type*} {l : Filter A} {p : A→Polynomial ℝ}
    {p₀ : Polynomial ℝ} {z : A→ℂ} {N : ℕ}
    (hp : ∀ j,Tendsto (fun a=>(p a).coeff j) l (𝓝 (p₀.coeff j)))
    (hdeg : ∀ a,(p a).natDegree≤N) (hdeg₀ : p₀.natDegree≤N)
    (hz : Tendsto z l (𝓝 1)) :
    (fun a=>(p a).eval₂ Complex.ofRealHom (z a)-(((p a).eval (1:ℝ):ℝ):ℂ)) =O[l] (fun a=>z a-1) := by
  have hq := tendsto_divByMonic_coeff hp hdeg hdeg₀
    (tendsto_const_nhds : Tendsto (fun _ : A=>(1:ℝ)) l (𝓝 1))
  have hd (q : Polynomial ℝ) (h : q.natDegree≤N) : (q /ₘ (X-C 1)).natDegree<N+1 := by
    rw [natDegree_divByMonic _ (monic_X_sub_C _),natDegree_X_sub_C]
    omega
  have ht := tendsto_eval₂_of_coeff (N:=N+1) hq (fun a=>hd (p a) (hdeg a)) (hd p₀ hdeg₀) hz
  have hh := (isBigO_refl (fun a=>z a-1) l).mul (ht.isBigO_one ℂ)
  simpa only [mul_one] using hh.congr_left (fun a=>(eval_sub_eval_one (p a) (z a)).symm)

lemma exp_linear_remainder_isBigO {A : Type*} {l : Filter A} {e w : A→ℂ}
    (he : Tendsto e l (𝓝 0)) (hw : w =O[l] (fun _=> (1:ℂ))) :
    (fun a=>Complex.exp (-e a*w a)-1+e a*w a) =O[l] (fun a=>(e a)^2) := by
  have ha : (fun a=> -e a*w a) =O[l] e := by
    simpa only [mul_one] using ((isBigO_refl e l).neg_left.mul hw)
  have hz : Tendsto (fun a=> -e a*w a) l (𝓝 0) := ha.trans_tendsto he
  have hr := ((Complex.exp_sub_sum_range_isBigO_pow 2).comp_tendsto hz).trans (ha.pow 2)
  apply hr.congr_left
  intro a
  simp only [Function.comp_def,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    pow_zero,pow_one,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one]
  ring

end
end nesterov.Slow
