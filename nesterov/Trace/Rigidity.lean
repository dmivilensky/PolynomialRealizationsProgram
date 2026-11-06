import nesterov.Trace.Formula
import nesterov.Trace.Comparison
import nesterov.Trace.Circle
import nesterov.Trace.TMM
import Mathlib.Order.Interval.Set.Infinite

/-! The exact rigidity direction in the trace formula, proved on real radial
values of the analytic quotient and then as a polynomial identity. -/
namespace nesterov.Trace
noncomputable section
open Complex Metric Set Real Polynomial
open scoped Topology
namespace StableQuotient
variable (Q : StableQuotient)

theorem diskFunction_real (x : ℝ) : (Q.diskFunction (x:ℂ)).im=0 := by
  unfold diskFunction
  rw [eval_ofReal,eval_ofReal]
  simp only [Complex.div_im,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_mul,sub_self,
    zero_div,Complex.sub_im,Complex.one_im]
end StableQuotient

namespace DoubleRootData
variable (A : DoubleRootData)

private theorem boundary_cont (R : QuotientRepresentation A.numerator (A.phi 1)) :
    ContinuousOn (boundaryValue R.quotient.diskFunction) (sphere (0:ℂ) 1) := by
  have hF := R.quotient.diskFunction_diffCont
  have hG := R.quotient.diskFunction_dslope_diffCont
  apply (boundaryValue_continuousOn ?_ ?_).mono sphere_subset_closedBall
  · simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hF.2
  · simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hG.2

private theorem boundary_conj (R : QuotientRepresentation A.numerator (A.phi 1)) :
    ∀ z∈sphere (0:ℂ) 1,boundaryValue R.quotient.diskFunction (star z)=boundaryValue R.quotient.diskFunction z := by
  have hreal : (R.quotient.diskFunction 1).im=0 := by rw [A.representation_one R];rfl
  intro z hz
  have hn : ‖z‖=1 := by simpa [mem_sphere,dist_zero_right] using hz
  apply R.quotient.boundaryValue_conj _ hreal
  rw [Complex.normSq_eq_norm_sq,hn,one_pow]

theorem boundary_nonneg_of_symbol (hs : A.SchurExceptMinusOne)
    (R : QuotientRepresentation A.numerator (A.phi 1))
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) :
    ∀ z : ℂ,Complex.normSq z=1 → 0≤boundaryValue R.quotient.diskFunction z := by
  apply nonneg_unit_of_upper (A.boundary_cont R) (A.boundary_conj R)
  intro ω hω
  have ht : 0≤A.traceIntegrand ω := by
    unfold traceIntegrand
    apply div_nonneg
    · exact mul_nonneg (by linarith [Real.neg_one_le_cos ω]) (hS ω hω)
    · exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  rw [A.traceIntegrand_representation hs R hω] at ht
  linarith

theorem tmmTransfer_of_zero_symbol (hs : A.SchurExceptMinusOne)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,A.symbol ω=0) : A.tmmTransfer := by
  obtain ⟨R⟩ := A.exists_quotientRepresentation hs
  have hF := R.quotient.diskFunction_diffCont
  have hG := R.quotient.diskFunction_dslope_diffCont
  have hzero := R.quotient.diskFunction_zero
  have hreal : (R.quotient.diskFunction 1).im=0 := by rw [A.representation_one R];rfl
  have hB := A.boundary_nonneg_of_symbol hs R (fun ω hω=>(hS ω hω).ge)
  have hUpper : ∀ ω∈Ioo (0:ℝ) Real.pi,
      boundaryValue R.quotient.diskFunction (Complex.exp ((ω:ℂ)*Complex.I))=0 := by
    intro ω hω
    have hh := A.traceIntegrand_representation hs R hω
    have ht : A.traceIntegrand ω=0 := by simp only [traceIntegrand,hS ω hω,mul_zero,zero_div]
    rw [ht] at hh
    linarith
  have hBneg : ∀ z : ℂ,Complex.normSq z=1 → 0≤ -boundaryValue R.quotient.diskFunction z := by
    apply nonneg_unit_of_upper (A.boundary_cont R).neg _ _
    · intro z hz
      exact congrArg Neg.neg (A.boundary_conj R z hz)
    · intro ω hω
      change 0≤ -boundaryValue R.quotient.diskFunction (Complex.exp ((ω:ℂ)*Complex.I))
      rw [hUpper ω hω,neg_zero]
  have hBez (z : ℂ) (hz : Complex.normSq z=1) : boundaryValue R.quotient.diskFunction z=0 :=
    le_antisymm (by linarith [hBneg z hz]) (hB z hz)
  have hF1re : (R.quotient.diskFunction 1).re=0 := by
    have hh := boundaryValue_circleAverage hF hG
    have havg : circleAverage (boundaryValue R.quotient.diskFunction) 0 1=0 := by
      apply circleAverage_const_on_circle
      intro z hz
      have hn : ‖z‖=1 := by simpa [mem_sphere,dist_zero_right] using hz
      apply hBez
      rw [Complex.normSq_eq_norm_sq,hn,one_pow]
    rw [havg,hzero,Complex.zero_re,sub_zero] at hh
    exact hh.symm
  have hradial (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) : R.quotient.diskFunction (x:ℂ)=0 := by
    have hh := radial_comparison hF hG hzero hreal (fun z hz=>by
      have hn : ‖z‖=1 := by simpa [mem_sphere,dist_zero_right] using hz
      exact hB z (by rw [Complex.normSq_eq_norm_sq,hn,one_pow])) hx.1 hx.2
    rw [hF1re] at hh
    exact Complex.ext (by simpa only [Complex.zero_re] using le_antisymm hh.2 hh.1)
      (by simpa only [Complex.zero_im] using R.quotient.diskFunction_real x)
  have heval (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) :
      Polynomial.eval x R.quotient.numerator.reverse=Polynomial.eval x R.quotient.denominator.reverse := by
    have hh := hradial x hx
    unfold StableQuotient.diskFunction at hh
    have hd : eval R.quotient.denominator.reverse (x:ℂ)≠0 :=
      R.quotient.denominator_reverse_ne (by simp [mem_closedBall,abs_of_pos hx.1,hx.2.le])
    have he := (div_eq_one_iff_eq hd).mp (sub_eq_zero.mp hh)
    exact_mod_cast (by simpa only [eval_ofReal] using he :
      ((Polynomial.eval x R.quotient.numerator.reverse:ℝ):ℂ)=((Polynomial.eval x R.quotient.denominator.reverse:ℝ):ℂ))
  have hrev : R.quotient.numerator.reverse=R.quotient.denominator.reverse :=
    Polynomial.eq_of_infinite_eval_eq _ _ ((Set.Ioo_infinite (by norm_num : (0:ℝ)<1)).mono heval)
  have hnd : R.quotient.numerator=R.quotient.denominator := by
    unfold Polynomial.reverse at hrev
    rw [R.quotient.degree_eq] at hrev
    simpa only [Polynomial.reflect_reflect] using congrArg (Polynomial.reflect R.quotient.denominator.natDegree) hrev
  have hsource : A.numerator=A.phi 1 := by
    calc
      A.numerator = R.common*R.quotient.numerator := R.numerator_factor
      _ = R.common*R.quotient.denominator := by rw [hnd]
      _ = A.phi 1 := R.denominator_factor.symm
  have hv : A.v=(X-C 1)^2*A.q := A.factor
  unfold tmmTransfer
  unfold numerator phi at hsource
  rw [hv] at hsource
  norm_num only [C_1,C_ofNat] at hsource ⊢
  linear_combination -hsource

theorem zero_symbol_iff_tmmTransfer (hs : A.SchurExceptMinusOne) :
    (∀ ω : ℝ,A.symbol ω=0) ↔ A.tmmTransfer :=
  ⟨fun h=>A.tmmTransfer_of_zero_symbol hs (fun ω _=>h ω),A.tmmTransfer_zero_symbol⟩

end DoubleRootData
end
end nesterov.Trace
