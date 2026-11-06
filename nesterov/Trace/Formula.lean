import nesterov.Trace.Representation
import nesterov.Trace.EvenAverage

/-! The literal trace formula and bounded source integrand, with the optional
simple characteristic root at −1 canceled inside the analytic representation. -/
namespace nesterov.Trace
noncomputable section
open Complex Metric Set Real Filter MeasureTheory intervalIntegral
open scoped Topology
namespace DoubleRootData
variable (A : DoubleRootData)

private theorem circle_normSq (ω : ℝ) : Complex.normSq (Complex.exp ((ω:ℂ)*Complex.I))=1 := by
  simp [Complex.normSq_eq_norm_sq]

private theorem circle_im (ω : ℝ) : (Complex.exp ((ω:ℂ)*Complex.I)).im=Real.sin ω := by
  rw [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_one,zero_mul,add_zero,zero_add]

private theorem circle_re (ω : ℝ) : (Complex.exp ((ω:ℂ)*Complex.I)).re=Real.cos ω := by
  rw [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]

theorem traceIntegrand_representation (hs : A.SchurExceptMinusOne)
    (R : QuotientRepresentation A.numerator (A.phi 1)) {ω : ℝ} (hω : ω∈Ioo (0:ℝ) Real.pi) :
    A.traceIntegrand ω=2*boundaryValue R.quotient.diskFunction (Complex.exp ((ω:ℂ)*Complex.I)) := by
  let z := Complex.exp ((ω:ℂ)*Complex.I)
  have hz := circle_normSq ω
  have hi : 0<z.im := by rw [show z.im=Real.sin ω from circle_im ω];exact Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hz1 : z≠1 := fun hh=>by rw [hh,Complex.one_im] at hi;linarith
  have hd : eval (A.phi 1) z≠0 := by
    intro hh
    rcases hs z hh with hn|⟨he,_⟩
    · have hnorm : ‖z‖=1 := by simp [z]
      rw [hnorm] at hn
      exact lt_irrefl _ hn
    · rw [he,Complex.neg_im,Complex.one_im,neg_zero] at hi
      exact lt_irrefl _ hi
  have hb := A.representation_boundary R hz hz1 hd
  have hre : z.re=Real.cos ω := circle_re ω
  have hsdef : ((1-z)*eval (A.phi 0) z*star (eval (A.phi 1) z)).re=A.symbol ω := rfl
  rw [hre,hsdef] at hb
  change A.traceIntegrand ω=2*boundaryValue R.quotient.diskFunction z
  rw [hb]
  unfold traceIntegrand
  have hscale (a d : ℝ) : a/d=2*(a/(2*d)) := by
    by_cases hd : d=0
    · simp only [hd,mul_zero,div_zero]
    · field_simp
  simpa only [mul_assoc] using hscale ((1+Real.cos ω)*A.symbol ω)
    ((1-Real.cos ω)^2*Complex.normSq (eval (A.phi 1) (Complex.exp ((ω:ℂ)*Complex.I))))

@[simp] theorem traceIntegrand_zero : A.traceIntegrand 0=0 := by simp [traceIntegrand]
@[simp] theorem traceIntegrand_pi : A.traceIntegrand Real.pi=0 := by simp [traceIntegrand]

private theorem representation_boundary_continuous
    (R : QuotientRepresentation A.numerator (A.phi 1)) :
    Continuous (fun ω : ℝ=>boundaryValue R.quotient.diskFunction (Complex.exp ((ω:ℂ)*Complex.I))) := by
  have hF := R.quotient.diskFunction_diffCont
  have hG := R.quotient.diskFunction_dslope_diffCont
  have hc := boundaryValue_continuousOn
    (by simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hF.2)
    (by simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hG.2)
  exact hc.comp_continuous (by fun_prop) (fun ω=>by simp [mem_closedBall])

theorem traceIntegrand_integrable (hs : A.SchurExceptMinusOne) :
    IntervalIntegrable A.traceIntegrand volume 0 Real.pi := by
  obtain ⟨R⟩ := A.exists_quotientRepresentation hs
  have hc := (A.representation_boundary_continuous R).const_mul 2
  apply (hc.intervalIntegrable 0 Real.pi).congr_uIoo
  intro ω hω
  have hω' : ω∈Ioo (0:ℝ) Real.pi := by simpa only [uIoo_of_lt Real.pi_pos] using hω
  exact (A.traceIntegrand_representation hs R hω').symm

theorem traceIntegrand_bounded (hs : A.SchurExceptMinusOne) :
    ∃ K : ℝ,0≤K ∧ ∀ ω∈Icc (0:ℝ) Real.pi,|A.traceIntegrand ω|≤K := by
  obtain ⟨R⟩ := A.exists_quotientRepresentation hs
  let H : C(Icc (0:ℝ) Real.pi,ℝ) :=
    ⟨fun ω=>2*boundaryValue R.quotient.diskFunction (Complex.exp (((ω:ℝ):ℂ)*Complex.I)),by
      have hc := (A.representation_boundary_continuous R).const_mul 2
      exact hc.comp continuous_subtype_val⟩
  refine ⟨‖H‖,norm_nonneg _,fun ω hω=>?_⟩
  by_cases h0 : ω=0
  · rw [h0,A.traceIntegrand_zero,abs_zero]
    exact norm_nonneg _
  by_cases hp : ω=Real.pi
  · rw [hp,A.traceIntegrand_pi,abs_zero]
    exact norm_nonneg _
  rw [A.traceIntegrand_representation hs R ⟨lt_of_le_of_ne hω.1 (Ne.symm h0),lt_of_le_of_ne hω.2 hp⟩]
  simpa only [H,ContinuousMap.coe_mk,Real.norm_eq_abs] using H.norm_coe_le_norm ⟨ω,hω⟩

/-- Theorem trace(a), exact source integral and its boundedness. -/
theorem trace_formula (hs : A.SchurExceptMinusOne) :
    2/A.y-1=(1/(2*Real.pi))*∫ ω in (0:ℝ)..Real.pi,A.traceIntegrand ω := by
  obtain ⟨R⟩ := A.exists_quotientRepresentation hs
  let F := R.quotient.diskFunction
  have hF := R.quotient.diskFunction_diffCont
  have hG := R.quotient.diskFunction_dslope_diffCont
  have hc : ContinuousOn (boundaryValue F) (sphere (0:ℂ) 1) := by
    apply (boundaryValue_continuousOn ?_ ?_).mono sphere_subset_closedBall
    · simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hF.2
    · simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hG.2
  have hreal : (F 1).im=0 := by
    change (R.quotient.diskFunction 1).im=0
    rw [A.representation_one R]
    rfl
  have hconj : ∀ z∈sphere (0:ℂ) 1,boundaryValue F (star z)=boundaryValue F z := by
    intro z hz
    have hn : ‖z‖=1 := by simpa only [mem_sphere,dist_zero_right] using hz
    apply R.quotient.boundaryValue_conj _ hreal
    rw [Complex.normSq_eq_norm_sq,hn,one_pow]
  have hhalf := circleAverage_half_integral hc hconj
  have havg := boundaryValue_circleAverage hF hG
  rw [A.representation_one R,R.quotient.diskFunction_zero,Complex.ofReal_re,Complex.zero_re,sub_zero] at havg
  have heq : (∫ ω in (0:ℝ)..Real.pi,A.traceIntegrand ω)=
      2*(∫ ω in (0:ℝ)..Real.pi,boundaryValue F (Complex.exp ((ω:ℂ)*Complex.I))) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
    intro ω hω
    exact A.traceIntegrand_representation hs R hω
  rw [heq]
  rw [hhalf] at havg
  rw [←havg]
  ring

end DoubleRootData
end
end nesterov.Trace
