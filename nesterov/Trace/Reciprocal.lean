import nesterov.Trace.Model
import nesterov.Trace.Disk
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Polynomial

/-! Reciprocal polynomial quotients are analytic on the closed unit disk when
the original denominator is strictly Schur stable. -/
namespace nesterov.Trace
noncomputable section
open Polynomial Complex Metric Set
open scoped Topology

theorem eval_reverse_mul_inv_pow (p : Polynomial ℝ) {z : ℂ} (hz : z≠0) :
    eval p.reverse z*(z⁻¹)^p.natDegree=eval p z⁻¹ := by
  let _ : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz)
  have hh := Polynomial.eval₂_reverse_mul_pow Complex.ofRealHom z⁻¹ p
  simpa only [invOf_eq_inv,inv_inv,eval,Polynomial.eval_map] using hh

theorem reverse_ne_zero_closedBall (p : Polynomial ℝ) (hp : p≠0)
    (hs : ∀ z : ℂ,eval p z=0 → ‖z‖<1) {z : ℂ} (hz : z∈closedBall (0:ℂ) 1) :
    eval p.reverse z≠0 := by
  by_cases hz0 : z=0
  · subst z
    rw [eval_zero,Polynomial.coeff_zero_reverse]
    exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hp
  · intro hh
    have he : eval p z⁻¹=0 := by rw [←eval_reverse_mul_inv_pow p hz0,hh,zero_mul]
    have hn := hs z⁻¹ he
    rw [norm_inv,←one_div] at hn
    have hpz : 0<‖z‖ := norm_pos_iff.mpr hz0
    have hgt : 1<‖z‖ := (div_lt_one hpz).mp hn
    have hle : ‖z‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using hz
    exact not_lt_of_ge hle hgt

structure StableQuotient where
  numerator : Polynomial ℝ
  denominator : Polynomial ℝ
  denominator_ne : denominator≠0
  degree_eq : numerator.natDegree=denominator.natDegree
  leading_eq : numerator.leadingCoeff=denominator.leadingCoeff
  roots_inside : ∀ z : ℂ,eval denominator z=0 → ‖z‖<1

namespace StableQuotient
variable (A : StableQuotient)

def diskFunction (z : ℂ) : ℂ := eval A.numerator.reverse z/eval A.denominator.reverse z-1

theorem denominator_reverse_ne {z : ℂ} (hz : z∈closedBall (0:ℂ) 1) :
    eval A.denominator.reverse z≠0 :=
  reverse_ne_zero_closedBall A.denominator A.denominator_ne A.roots_inside hz

theorem diskFunction_analytic {z : ℂ} (hz : z∈closedBall (0:ℂ) 1) :
    AnalyticAt ℂ A.diskFunction z := by
  have hN : AnalyticAt ℂ (eval A.numerator.reverse) z := by
    exact AnalyticOnNhd.eval_polynomial _ z (Set.mem_univ z)
  have hD : AnalyticAt ℂ (eval A.denominator.reverse) z := by
    exact AnalyticOnNhd.eval_polynomial _ z (Set.mem_univ z)
  exact (hN.div hD (A.denominator_reverse_ne hz)).sub analyticAt_const

theorem diskFunction_zero : A.diskFunction 0=0 := by
  unfold diskFunction
  rw [eval_zero,eval_zero,Polynomial.coeff_zero_reverse,Polynomial.coeff_zero_reverse,A.leading_eq]
  rw [div_self (by exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr A.denominator_ne),sub_self]

theorem diskFunction_reciprocal {z : ℂ} (hz : z≠0)
    (hd : eval A.denominator z⁻¹≠0) :
    A.diskFunction z=eval A.numerator z⁻¹/eval A.denominator z⁻¹-1 := by
  have hN := eval_reverse_mul_inv_pow A.numerator hz
  have hD := eval_reverse_mul_inv_pow A.denominator hz
  rw [A.degree_eq] at hN
  have hpow : (z⁻¹)^A.denominator.natDegree≠0 := pow_ne_zero _ (inv_ne_zero hz)
  unfold diskFunction
  congr 1
  apply (div_eq_div_iff (by
    intro hh
    rw [hh,zero_mul] at hD
    exact hd hD.symm) hd).mpr
  rw [←hN,←hD]
  ring

theorem diskFunction_diffCont : DiffContOnCl ℂ A.diskFunction (ball 0 1) := by
  refine ⟨fun z hz=>(A.diskFunction_analytic (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt,?_⟩
  rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)]
  exact fun z hz=>(A.diskFunction_analytic hz).continuousAt.continuousWithinAt

theorem diskFunction_dslope_diffCont : DiffContOnCl ℂ (dslope A.diskFunction 1) (ball 0 1) := by
  have ha : AnalyticAt ℂ A.diskFunction 1 := A.diskFunction_analytic (by norm_num [mem_closedBall])
  have hd1 : DifferentiableAt ℂ (dslope A.diskFunction 1) 1 := by
    obtain ⟨p,hp⟩ := ha
    exact hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt
  have hd (z : ℂ) (hz : z∈closedBall (0:ℂ) 1) : DifferentiableAt ℂ (dslope A.diskFunction 1) z := by
    by_cases h : z=1
    · simpa only [h] using hd1
    · exact (differentiableAt_dslope_of_ne h).mpr (A.diskFunction_analytic hz).differentiableAt
  refine ⟨fun z hz=>(hd z (ball_subset_closedBall hz)).differentiableWithinAt,?_⟩
  rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)]
  exact fun z hz=>(hd z hz).continuousAt.continuousWithinAt

end StableQuotient
end
end nesterov.Trace
