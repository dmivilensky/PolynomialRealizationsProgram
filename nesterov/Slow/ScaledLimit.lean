import nesterov.Slow.Factorization
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Exp
import nesterov.Flow.Constants

/-! The continuous-family slow curvature limit, without a coefficient derivative. -/
namespace nesterov.Slow
noncomputable section
open Polynomial Filter Set Asymptotics
open scoped Topology

private theorem ofRealHom_apply (x : ℝ) : Complex.ofRealHom x=(x:ℂ) := rfl

def expIncrement (z : ℂ) : ℂ := dslope Complex.exp 0 z

@[simp] theorem expIncrement_zero : expIncrement 0=1 := by
  simpa only [expIncrement,dslope_same,Complex.exp_zero] using (Complex.hasDerivAt_exp 0).deriv

theorem expIncrement_continuousAt : ContinuousAt expIncrement 0 :=
  continuousAt_dslope_same.mpr (Complex.differentiable_exp.differentiableAt)

theorem expIncrement_mul (z : ℂ) : z*expIncrement z=Complex.exp z-1 := by
  simpa only [expIncrement,sub_zero,smul_eq_mul,Complex.exp_zero] using sub_smul_dslope Complex.exp 0 z

namespace SecondOrderFamily
variable {θ y : ℝ} (F : SecondOrderFamily θ y)

def wave (_F : SecondOrderFamily θ y) (ε : ℝ) (w : ℂ) : ℂ := Complex.exp (-(ε:ℂ)*w)
def curvature (ε : ℝ) (z : ℂ) : ℂ := (F.v ε).eval₂ Complex.ofRealHom z/(F.u ε).eval₂ Complex.ofRealHom z
def scaledCurvature (ε : ℝ) (w : ℂ) : ℂ := F.curvature ε (F.wave ε w)/(ε:ℂ)^2

theorem wave_tendsto {A : Type*} {l : Filter A} {e : A→ℝ} {w : A→ℂ} {w₀ : ℂ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a=>F.wave (e a) (w a)) l (𝓝 1) := by
  have hε : Tendsto (fun a=>(e a:ℂ)) l (𝓝 0) := by
    convert (Complex.continuous_ofReal.tendsto _).comp (he.mono_right nhdsWithin_le_nhds) using 1
    funext a
    rfl
  simpa only [wave,neg_zero,zero_mul,Complex.exp_zero] using (hε.neg.mul hw).cexp

theorem query_wave_tendsto {A : Type*} {l : Filter A} {e : A→ℝ} {w : A→ℂ} {w₀ : ℂ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a=>(F.u (e a)).eval₂ Complex.ofRealHom (F.wave (e a) (w a))) l (𝓝 1) := by
  have hh := tendsto_eval₂_of_coeff (fun j=>(F.u_coeff_tendsto j).comp he)
    (fun a=>F.u_natDegree_lt (e a)) (F.u_natDegree_lt 0) (F.wave_tendsto he hw)
  have hval : (F.u 0).eval₂ Complex.ofRealHom 1=1 := by
    simpa only [map_one,F.u_one,ofRealHom_apply,Complex.ofReal_one] using eval₂_at_apply (p:=F.u 0) Complex.ofRealHom (1:ℝ)
  rwa [hval] at hh

theorem quotient_wave_tendsto {A : Type*} {l : Filter A} {e : A→ℝ} {w : A→ℂ} {w₀ : ℂ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a=>(F.quotient (e a)).eval₂ Complex.ofRealHom (F.wave (e a) (w a))) l
      (𝓝 ((-1/y:ℝ):ℂ)) := by
  have hh := tendsto_eval₂_of_coeff (N:=F.memory+1)
    (fun j=>(F.quotient_coeff_tendsto j).comp he)
    (fun a=>lt_of_le_of_lt (F.quotient_natDegree_le (e a)) (Nat.lt_succ_self _))
    (by rw [←F.quotient_zero];exact lt_of_le_of_lt (F.quotient_natDegree_le 0) (Nat.lt_succ_self _))
    (F.wave_tendsto he hw)
  have hval : F.q0.eval₂ Complex.ofRealHom 1=((-1/y:ℝ):ℂ) := by
    simpa only [map_one,F.q0_one,ofRealHom_apply] using eval₂_at_apply (p:=F.q0) Complex.ofRealHom (1:ℝ)
  rwa [hval] at hh

/-- Exact factored identity before taking any slow limit. -/
theorem scaledCurvature_factored : ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ w : ℂ,
    F.scaledCurvature ε w=
      (-w*expIncrement (-(ε:ℂ)*w))*
        ((F.thetaAt ε:ℂ)-w*expIncrement (-(ε:ℂ)*w))*
        (F.quotient ε).eval₂ Complex.ofRealHom (F.wave ε w)/
          (F.u ε).eval₂ Complex.ofRealHom (F.wave ε w) := by
  filter_upwards [F.factorization,self_mem_nhdsWithin] with ε hfac hε w
  have he : (ε:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hε)
  have hθ : (ε:ℂ)*(F.thetaAt ε:ℂ)=1-(F.beta ε:ℂ) := by
    dsimp [thetaAt]
    push_cast
    field_simp
  have hz : F.wave ε w-1= -(ε:ℂ)*w*expIncrement (-(ε:ℂ)*w) :=
    (expIncrement_mul (-(ε:ℂ)*w)).symm
  unfold scaledCurvature curvature
  rw [hfac]
  simp only [eval₂_mul,eval₂_sub,eval₂_X,eval₂_C,ofRealHom_apply,Complex.ofReal_one]
  have hβ : F.wave ε w-(F.beta ε:ℂ)=(F.wave ε w-1)+(1-(F.beta ε:ℂ)) := by ring
  rw [hβ,←hθ,hz]
  field_simp [he]
  ring

/-- All moving slow modes have the exact flow curvature limit. -/
theorem scaledCurvature_tendsto {A : Type*} {l : Filter A} {e : A→ℝ} {w : A→ℂ} {w₀ : ℂ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a=>F.scaledCurvature (e a) (w a)) l (𝓝 (w₀*((θ:ℂ)-w₀)/(y:ℂ))) := by
  have hε : Tendsto (fun a=>(e a:ℂ)) l (𝓝 0) := by
    convert (Complex.continuous_ofReal.tendsto _).comp (he.mono_right nhdsWithin_le_nhds) using 1
    funext a
    rfl
  have hE : Tendsto (fun a=>expIncrement (-(e a:ℂ)*w a)) l (𝓝 1) := by
    have hz : Tendsto (fun a=> -(e a:ℂ)*w a) l (𝓝 0) := by simpa using hε.neg.mul hw
    simpa only [Function.comp_def,expIncrement_zero] using expIncrement_continuousAt.tendsto.comp hz
  have hθ := (Complex.continuous_ofReal.tendsto _).comp (F.thetaAt_tendsto.comp he)
  have hmain := ((hw.neg.mul hE).mul (hθ.sub (hw.mul hE))).mul (F.quotient_wave_tendsto he hw)
  have hh := hmain.div (F.query_wave_tendsto he hw) (by norm_num : (1:ℂ)≠0)
  have heq : (fun a=>F.scaledCurvature (e a) (w a))=ᶠ[l]
      (fun a=>(-w a*expIncrement (-(e a:ℂ)*w a))*
        ((F.thetaAt (e a):ℂ)-w a*expIncrement (-(e a:ℂ)*w a))*
        (F.quotient (e a)).eval₂ Complex.ofRealHom (F.wave (e a) (w a))/
          (F.u (e a)).eval₂ Complex.ofRealHom (F.wave (e a) (w a))) := by
    filter_upwards [he.eventually F.scaledCurvature_factored] with a ha
    exact ha (w a)
  convert hh.congr' heq.symm using 1
  push_cast
  ring_nf

end SecondOrderFamily
end
end nesterov.Slow
