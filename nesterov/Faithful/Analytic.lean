import nesterov.Faithful.Algebra
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Polynomial

/-! Analytic germs used in the exact limit-frequency expansion. -/
namespace nesterov.Faithful
noncomputable section
open Filter Asymptotics Polynomial
open scoped Topology

def circle (ω : ℝ) : ℂ := Complex.exp ((ω:ℂ)*Complex.I)
def evalComplex (p : Polynomial ℝ) (z : ℂ) : ℂ := (p.map Complex.ofRealHom).eval z

@[simp] theorem circle_zero : circle 0=1 := by simp [circle]

@[fun_prop] theorem analyticAt_circle (ω : ℝ) : AnalyticAt ℝ circle ω := by
  unfold circle
  have hexp : AnalyticAt ℝ Complex.exp ((ω:ℂ)*Complex.I) :=
    (Complex.differentiable_exp.analyticAt _).restrictScalars
  have hinner : AnalyticAt ℝ (fun x : ℝ=>(x:ℂ)*Complex.I) ω :=
    (Complex.ofRealCLM.analyticAt ω).fun_mul analyticAt_const
  exact AnalyticAt.fun_comp (f:=fun x : ℝ=>(x:ℂ)*Complex.I) hexp hinner

theorem hasDerivAt_circle (ω : ℝ) : HasDerivAt circle (Complex.I*circle ω) ω := by
  have hh := ((Complex.hasDerivAt_exp ((ω:ℂ)*Complex.I)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt ω
    ((Complex.ofRealCLM.hasDerivAt).mul_const Complex.I)
  change HasDerivAt (fun x : ℝ=>Complex.exp ((x:ℂ)*Complex.I))
    (Complex.I*Complex.exp ((ω:ℂ)*Complex.I)) ω
  simpa [Function.comp_def,mul_comm] using hh

@[fun_prop] theorem analyticAt_evalComplex (p : Polynomial ℝ) (z : ℂ) :
    AnalyticAt ℝ (evalComplex p) z := by
  exact (AnalyticOnNhd.eval_polynomial (𝕜:=ℝ) (p.map Complex.ofRealHom)) z (Set.mem_univ _)

theorem hasDerivAt_evalComplex_comp {f : ℝ→ℂ} {d : ℂ} {x : ℝ}
    (p : Polynomial ℝ) (hf : HasDerivAt f d x) :
    HasDerivAt (fun x=>evalComplex p (f x)) (evalComplex p.derivative (f x)*d) x := by
  have hh := (((p.map Complex.ofRealHom).hasDerivAt (f x)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x hf
  simpa [evalComplex,Polynomial.derivative_map,mul_comm,Function.comp_def] using hh

/-- The analytic circle increment has the exact divided germ and the first
jet required by the half-step calculation. -/
theorem exists_circle_increment : ∃ E : ℝ→ℂ,AnalyticAt ℝ E 0 ∧ E 0=Complex.I ∧
    HasDerivAt E (-1/2) 0 ∧ ∀ ω,circle ω-1=(ω:ℂ)*E ω := by
  let f : ℝ→ℂ := fun ω=>circle ω-1
  have hf : AnalyticAt ℝ f 0 := (analyticAt_circle 0).sub analyticAt_const
  have hd (ω : ℝ) : HasDerivAt f (Complex.I*circle ω) ω := (hasDerivAt_circle ω).sub_const 1
  have hder : deriv f=fun ω=>Complex.I*circle ω := funext (fun ω=>(hd ω).deriv)
  have hi2 : iteratedDeriv 2 f 0= -1 := by
    rw [iteratedDeriv_succ,iteratedDeriv_succ,iteratedDeriv_zero]
    rw [hder]
    have hh := (hasDerivAt_circle 0).const_mul Complex.I
    simpa using hh.deriv
  obtain ⟨R,hR,heq⟩ := hf.exists_eq_sum_add_pow_mul 3
  let E : ℝ→ℂ := fun ω=>Complex.I-(ω:ℂ)/2+(ω:ℂ)^2*R ω
  have hreal : AnalyticAt ℝ (fun ω : ℝ=>(ω:ℂ)) 0 := Complex.ofRealCLM.analyticAt 0
  have hE : AnalyticAt ℝ E 0 := (analyticAt_const.sub (hreal.div_const (c:=(2:ℂ)))).add ((hreal.pow 2).mul hR)
  refine ⟨E,hE,by simp [E],?_,fun ω=>?_⟩
  · have hh : HasDerivAt (fun ω : ℝ=>(ω:ℂ)/2) (1/2) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x:=(0:ℝ))).div_const (2:ℂ))
    have hpow := (((Complex.ofRealCLM.hasDerivAt (x:=(0:ℝ))).pow 2).mul hR.differentiableAt.hasDerivAt)
    have hr := (hasDerivAt_const (0:ℝ) Complex.I).sub hh |>.add hpow
    convert hr using 1
    · ext ω
      rfl
    · norm_num
  · have hh := heq ω
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,iteratedDeriv_zero,
      Nat.factorial_zero,Nat.factorial_succ,Nat.cast_one,Nat.cast_mul,
      pow_zero,pow_one,zero_add,div_one,one_smul] at hh
    rw [show f 0=0 by simp [f],show iteratedDeriv 1 f 0=Complex.I by simpa [iteratedDeriv_succ,iteratedDeriv_zero] using (hd 0).deriv,hi2] at hh
    simp only [f,E,zero_add,Complex.real_smul] at hh ⊢
    push_cast at hh
    convert hh using 1
    ring

end
end nesterov.Faithful
