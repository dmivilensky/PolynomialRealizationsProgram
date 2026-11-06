import nesterov.Slow.ScaledLimit

/-! Article: Lemma D.3, the exact scaled query coefficients and their limits. -/
namespace nesterov.Slow.SecondOrderFamily
noncomputable section
open Polynomial Filter Set
open scoped Topology
variable {θ y : ℝ} (F : nesterov.Slow.SecondOrderFamily θ y)

def correction (ε : ℝ) (w : ℂ) : ℂ := (F.scaledCurvature ε w-1)/(1-(ε:ℂ)^2)
def queryRatio (ε : ℝ) (w : ℂ) : ℂ :=
  (1+(ε:ℂ)^2-2*F.curvature ε (F.wave ε w))/(1-(ε:ℂ)^2)
def slowG (ε : ℝ) (w : ℂ) : ℝ :=
  F.stepAt ε*((F.correction ε w).re-ε^2*Complex.normSq (F.correction ε w))
def slowS (ε : ℝ) (w : ℂ) : ℝ := -F.stepAt ε*(F.correction ε w).im

theorem queryRatio_eq {ε : ℝ} (hε : ε≠0) (hε1 : ε^2≠1) (w : ℂ) :
    F.queryRatio ε w=1-2*(ε:ℂ)^2*F.correction ε w := by
  have he : (ε:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hε
  have hden : 1-(ε:ℂ)^2≠0 := by
    have hh : (ε^2:ℝ)≠1 := hε1
    exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hh)
  unfold queryRatio correction scaledCurvature
  field_simp [he,hden]
  ring

theorem query_coefficients_exact {ε : ℝ} (hε : ε≠0) (hε1 : ε^2≠1) (hy : F.stepAt ε≠0) (w : ℂ) :
    1-Complex.normSq (F.queryRatio ε w)=(4*ε^2/F.stepAt ε)*F.slowG ε w ∧
    2*(F.queryRatio ε w).im=(4*ε^2/F.stepAt ε)*F.slowS ε w := by
  rw [F.queryRatio_eq hε hε1]
  unfold slowG slowS
  have hr2 : (2:ℂ).re=(2:ℝ) := rfl
  have hi2 : (2:ℂ).im=0 := rfl
  constructor
  · simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im,←Complex.ofReal_pow,hr2,hi2]
    field_simp [hy]
    ring
  · simp only [Complex.sub_im,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.one_im,←Complex.ofReal_pow,hr2,hi2]
    field_simp [hy]
    ring

theorem correction_tendsto {A : Type*} {l : Filter A} {e : A→ℝ} {w : A→ℂ} {w₀ : ℂ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a=>F.correction (e a) (w a)) l (𝓝 (w₀*((θ:ℂ)-w₀)/(y:ℂ)-1)) := by
  have hε : Tendsto (fun a=>(e a:ℂ)) l (𝓝 0) := by
    convert (Complex.continuous_ofReal.tendsto _).comp (he.mono_right nhdsWithin_le_nhds) using 1
    funext a
    rfl
  have hh := ((F.scaledCurvature_tendsto he hw).sub_const 1).div
    (tendsto_const_nhds.sub (hε.pow 2)) (by norm_num : (1:ℂ)-0^2≠0)
  simp only [zero_pow (by decide : 2≠0),sub_zero,div_one] at hh
  convert hh using 1
  funext a
  rfl

theorem slowG_tendsto {A : Type*} {l : Filter A} {e : A→ℝ} {w : A→ℂ} {w₀ : ℂ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a=>F.slowG (e a) (w a)) l
      (𝓝 (y*(w₀*((θ:ℂ)-w₀)/(y:ℂ)-1).re)) := by
  have hε := he.mono_right nhdsWithin_le_nhds
  have hcor := F.correction_tendsto he hw
  have hn := (Complex.continuous_normSq.tendsto _).comp hcor
  have hr := Complex.continuous_re.tendsto _ |>.comp hcor
  simpa only [slowG,Function.comp_def,zero_pow (by decide : 2≠0),zero_mul,sub_zero] using
    (F.stepAt_tendsto.comp he).mul (hr.sub ((hε.pow 2).mul hn))

theorem slowS_tendsto {A : Type*} {l : Filter A} {e : A→ℝ} {w : A→ℂ} {w₀ : ℂ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a=>F.slowS (e a) (w a)) l
      (𝓝 (-y*(w₀*((θ:ℂ)-w₀)/(y:ℂ)-1).im)) :=
  (F.stepAt_tendsto.comp he).neg.mul (Complex.continuous_im.tendsto _ |>.comp (F.correction_tendsto he hw))


def slowPoint (c γ : ℝ) : ℂ := (c:ℂ)-(γ:ℂ)*Complex.I

theorem slow_limit_algebra (θ y c γ : ℝ) (hy : y≠0) :
    y*(slowPoint c γ*((θ:ℂ)-slowPoint c γ)/(y:ℂ)-1).re=γ^2-nesterov.Flow.delta θ y c ∧
    -y*(slowPoint c γ*((θ:ℂ)-slowPoint c γ)/(y:ℂ)-1).im=(θ-2*c)*γ := by
  unfold slowPoint nesterov.Flow.delta
  simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.one_re,Complex.one_im,
    Complex.normSq_apply]
  constructor <;> field_simp [hy] <;> ring

theorem slowG_physical_tendsto {A : Type*} {l : Filter A}
    {e c γ : A→ℝ} {c₀ γ₀ : ℝ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hc : Tendsto c l (𝓝 c₀)) (hγ : Tendsto γ l (𝓝 γ₀)) :
    Tendsto (fun a=>F.slowG (e a) (slowPoint (c a) (γ a))) l
      (𝓝 (γ₀^2-nesterov.Flow.delta θ y c₀)) := by
  have hw : Tendsto (fun a=>slowPoint (c a) (γ a)) l (𝓝 (slowPoint c₀ γ₀)) := by
    unfold slowPoint
    exact ((Complex.continuous_ofReal.tendsto _).comp hc).sub
      (((Complex.continuous_ofReal.tendsto _).comp hγ).mul_const Complex.I)
  have hh := F.slowG_tendsto he hw
  rwa [(slow_limit_algebra θ y c₀ γ₀ F.step_pos.ne').1] at hh

theorem slowS_physical_tendsto {A : Type*} {l : Filter A}
    {e c γ : A→ℝ} {c₀ γ₀ : ℝ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hc : Tendsto c l (𝓝 c₀)) (hγ : Tendsto γ l (𝓝 γ₀)) :
    Tendsto (fun a=>F.slowS (e a) (slowPoint (c a) (γ a))) l
      (𝓝 ((θ-2*c₀)*γ₀)) := by
  have hw : Tendsto (fun a=>slowPoint (c a) (γ a)) l (𝓝 (slowPoint c₀ γ₀)) := by
    unfold slowPoint
    exact ((Complex.continuous_ofReal.tendsto _).comp hc).sub
      (((Complex.continuous_ofReal.tendsto _).comp hγ).mul_const Complex.I)
  have hh := F.slowS_tendsto he hw
  rwa [(slow_limit_algebra θ y c₀ γ₀ F.step_pos.ne').2] at hh

end
end nesterov.Slow.SecondOrderFamily
