import nesterov.Trace.CurvatureBounds

/-! The literal curvature trace integral, Equation `tracelambda`, including its
nonnegativity under the source closed-root pencil assumptions. -/
namespace nesterov.Trace
noncomputable section
open Complex Metric Set Real Filter MeasureTheory intervalIntegral
open scoped Topology
namespace DoubleRootData
variable (A : DoubleRootData)

def curvatureTraceIntegrand (lam ω : ℝ) : ℝ :=
  let z := Complex.exp ((ω:ℂ)*Complex.I)
  (1+Real.cos ω)*(lam*A.symbol ω+(1-lam)*(1-Real.cos ω)*Complex.normSq (eval (A.phi 0) z))/
    ((1-Real.cos ω)^2*Complex.normSq (eval (A.phi lam) z))

private theorem curvature_circle_re (ω : ℝ) :
    (Complex.exp ((ω:ℂ)*Complex.I)).re=Real.cos ω := by
  rw [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]

private theorem curvature_circle_im (ω : ℝ) :
    (Complex.exp ((ω:ℂ)*Complex.I)).im=Real.sin ω := by
  rw [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_one,zero_mul,add_zero,zero_add]

theorem curvatureTraceIntegrand_representation {lam : ℝ} (hlam : 0<lam)
    (hs : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖<1)
    {ω : ℝ} (hω : ω∈Ioo (0:ℝ) Real.pi) :
    A.curvatureTraceIntegrand lam ω=
      2*boundaryValue (A.curvatureQuotient lam hs).diskFunction (Complex.exp ((ω:ℂ)*Complex.I)) := by
  let z := Complex.exp ((ω:ℂ)*Complex.I)
  have hz : Complex.normSq z=1 := by simp [z,Complex.normSq_eq_norm_sq]
  have hz1 : z≠1 := by
    intro hh
    have hi : z.im=Real.sin ω := curvature_circle_im ω
    rw [hh,Complex.one_im] at hi
    linarith [Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2]
  rw [A.curvature_boundary hlam hs hz hz1,A.curvature_symbol]
  have hU : A.unitSymbol z=A.symbol ω := rfl
  rw [hU,show z.re=Real.cos ω from curvature_circle_re ω]
  unfold curvatureTraceIntegrand
  dsimp [z]
  have hscale (a d : ℝ) : a/d=2*(a/(2*d)) := by
    by_cases hd : d=0
    · simp only [hd,mul_zero,div_zero]
    · field_simp
  simpa only [mul_assoc] using hscale
    ((1+Real.cos ω)*(lam*A.symbol ω+(1-lam)*(1-Real.cos ω)*
      Complex.normSq (eval (A.phi 0) (Complex.exp ((ω:ℂ)*Complex.I)))))
    ((1-Real.cos ω)^2*Complex.normSq (eval (A.phi lam) (Complex.exp ((ω:ℂ)*Complex.I))))

private theorem curvature_boundary_continuous {lam : ℝ}
    (hs : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖<1) :
    Continuous (fun ω : ℝ=>boundaryValue (A.curvatureQuotient lam hs).diskFunction
      (Complex.exp ((ω:ℂ)*Complex.I))) := by
  let Q := A.curvatureQuotient lam hs
  have hc := boundaryValue_continuousOn
    (by simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using Q.diskFunction_diffCont.2)
    (by simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using Q.diskFunction_dslope_diffCont.2)
  exact hc.comp_continuous (by fun_prop) (fun ω=>by simp [mem_closedBall])

theorem curvatureTraceIntegrand_integrable {lam : ℝ} (hlam : 0<lam)
    (hs : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖<1) :
    IntervalIntegrable (A.curvatureTraceIntegrand lam) volume 0 Real.pi := by
  have hc := (A.curvature_boundary_continuous hs).const_mul 2
  apply (hc.intervalIntegrable 0 Real.pi).congr_uIoo
  intro ω hω
  have hω' : ω∈Ioo (0:ℝ) Real.pi := by simpa only [uIoo_of_lt Real.pi_pos] using hω
  exact (A.curvatureTraceIntegrand_representation hlam hs hω').symm

/-- Equation tracelambda, under the strictly stable curvature pencil. -/
theorem curvature_trace_formula {lam : ℝ} (hlam : 0<lam)
    (hs : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖<1) :
    2/(lam*A.y)-1=(1/(2*Real.pi))*∫ ω in (0:ℝ)..Real.pi,A.curvatureTraceIntegrand lam ω := by
  let Q := A.curvatureQuotient lam hs
  have hF := Q.diskFunction_diffCont
  have hG := Q.diskFunction_dslope_diffCont
  have hc : ContinuousOn (boundaryValue Q.diskFunction) (sphere (0:ℂ) 1) := by
    apply (boundaryValue_continuousOn ?_ ?_).mono sphere_subset_closedBall
    · simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hF.2
    · simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hG.2
  have hreal : (Q.diskFunction 1).im=0 := by rw [A.curvatureQuotient_one hlam];rfl
  have hconj : ∀ z∈sphere (0:ℂ) 1,boundaryValue Q.diskFunction (star z)=boundaryValue Q.diskFunction z := by
    intro z hz
    have hn : ‖z‖=1 := by simpa only [mem_sphere,dist_zero_right] using hz
    apply Q.boundaryValue_conj _ hreal
    rw [Complex.normSq_eq_norm_sq,hn,one_pow]
  have hhalf := circleAverage_half_integral hc hconj
  have havg := boundaryValue_circleAverage hF hG
  rw [A.curvatureQuotient_one hlam,Q.diskFunction_zero,Complex.ofReal_re,Complex.zero_re,sub_zero] at havg
  have heq : (∫ ω in (0:ℝ)..Real.pi,A.curvatureTraceIntegrand lam ω)=
      2*(∫ ω in (0:ℝ)..Real.pi,boundaryValue Q.diskFunction (Complex.exp ((ω:ℂ)*Complex.I))) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
    intro ω hω
    exact A.curvatureTraceIntegrand_representation hlam hs hω
  rw [heq]
  rw [hhalf] at havg
  rw [←havg]
  ring

/-- The same literal integral and nonnegative value under the source's closed-root
hypotheses after the explicitly proved common-factor reduction. -/
theorem curvature_trace_formula_of_closed {lam : ℝ} (hlam0 : 0<lam) (hlam1 : lam<1)
    (hcop : IsCoprime A.u A.v) (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω)
    (hclosed : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖≤1) :
    2/(lam*A.y)-1=(1/(2*Real.pi))*∫ ω in (0:ℝ)..Real.pi,A.curvatureTraceIntegrand lam ω ∧
      0≤(1/(2*Real.pi))*∫ ω in (0:ℝ)..Real.pi,A.curvatureTraceIntegrand lam ω := by
  have hs := A.curvature_strict_of_closed hcop hS hlam0 hlam1 hclosed
  have heq := A.curvature_trace_formula hlam0 hs
  refine ⟨heq,?_⟩
  rw [←heq]
  have hb := A.curvature_radial_bounds hlam0 hlam1 hs hS (x:=1/2) (by norm_num) (by norm_num)
  exact hb.1.trans hb.2

end DoubleRootData
end
end nesterov.Trace
