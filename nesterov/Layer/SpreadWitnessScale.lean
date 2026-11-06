import nesterov.Layer.SpreadWitnessGeometry
import nesterov.Spread.KernelData
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Quantitative scale comparisons behind the spread-witness hypotheses. -/
namespace nesterov.TwoStep.Spread
noncomputable section
open Set Filter
open scoped Topology

def cubicScale (x : ℝ) : ℝ := x*Real.sqrt x
def bandMargin (ck s ω₀ : ℝ) : ℝ := min (1/4) (min (ω₀^2/6) (ck*s^2))
def marginFactor (ck s : ℝ) : ℝ := min (1/8) (min (1/6) (ck*s^2/2))

theorem cubicScale_pos {x : ℝ} (hx : 0<x) : 0<cubicScale x :=
  mul_pos hx (Real.sqrt_pos.mpr hx)

theorem cubicScale_eq_rpow {x : ℝ} (hx : 0<x) : cubicScale x=x^(3/2:ℝ) := by
  calc
    _=x^(1:ℝ)*x^(1/2:ℝ) := by rw [Real.rpow_one,←Real.sqrt_eq_rpow];rfl
    _=x^((1:ℝ)+1/2) := (Real.rpow_add hx _ _).symm
    _=_ := by norm_num

theorem marginFactor_pos {ck s : ℝ} (hck : 0<ck) (hs : 0<s) : 0<marginFactor ck s := by
  unfold marginFactor
  exact lt_min (by norm_num) (lt_min (by norm_num) (by positivity))

theorem bandMargin_pos {ck s ω₀ : ℝ} (hck : 0<ck) (hs : 0<s) (hω₀ : 0<ω₀) :
    0<bandMargin ck s ω₀ := by
  unfold bandMargin
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem margin_lower {ck s ω₀ x : ℝ} (hck : 0≤ck) (hx : 0≤x) (hx2 : x≤2) (hxω : x≤ω₀^2) :
    marginFactor ck s*x≤bandMargin ck s ω₀ := by
  have h1 : marginFactor ck s≤1/8 := min_le_left _ _
  have h2 : marginFactor ck s≤1/6 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : marginFactor ck s≤ck*s^2/2 := (min_le_right _ _).trans (min_le_right _ _)
  unfold bandMargin
  refine le_min ?_ (le_min ?_ ?_)
  · nlinarith [mul_le_mul_of_nonneg_right h1 hx]
  · nlinarith [mul_le_mul_of_nonneg_right h2 hx]
  · nlinarith [mul_le_mul_of_nonneg_right h3 hx,
      mul_le_mul_of_nonneg_left hx2 (mul_nonneg hck (sq_nonneg s))]

theorem margin_frequency_lower {ck s ω₀ x : ℝ} (hck : 0<ck) (hs : 0<s)
    (hω₀ : 0<ω₀) (hx : 0≤x) (hx2 : x≤2) (hxω : x≤ω₀^2) :
    marginFactor ck s*cubicScale x≤bandMargin ck s ω₀*ω₀ := by
  have hm := margin_lower (ck:=ck) (s:=s) hck.le hx hx2 hxω
  have hroot : Real.sqrt x≤ω₀ := Real.sqrt_le_iff.mpr ⟨hω₀.le,hxω⟩
  unfold cubicScale
  calc
    _=(marginFactor ck s*x)*Real.sqrt x := by ring
    _≤bandMargin ck s ω₀*ω₀ := by
      gcongr
      exact (bandMargin_pos hck hs hω₀).le

theorem ratio_tendsto_of_denominator_lower {A : Type*} {l : Filter A}
    {f p q : A→ℝ} {D : ℝ} (hD : 0<D)
    (hf : ∀ᶠ a in l,0≤f a) (hp : ∀ᶠ a in l,0<p a)
    (hqp : ∀ᶠ a in l,D*p a≤q a)
    (hlim : Tendsto (fun a=>f a/p a) l (𝓝 0)) :
    Tendsto (fun a=>f a/q a) l (𝓝 0) := by
  have hupper : ∀ᶠ a in l, f a/q a≤(1/D)*(f a/p a) := by
    filter_upwards [hf,hp,hqp] with a hf hp hq
    calc
      _≤f a/(D*p a) := div_le_div_of_nonneg_left hf (mul_pos hD hp) hq
      _=_ := by field_simp
  have hlower : ∀ᶠ a in l,0≤f a/q a := by
    filter_upwards [hf,hp,hqp] with a hf hp hq
    exact div_nonneg hf ((mul_pos hD hp).trans_le hq).le
  exact squeeze_zero' hlower hupper (by simpa only [mul_zero] using hlim.const_mul (1/D))

theorem ratio_xi_of_cubic {A : Type*} {l : Filter A} {f x : A→ℝ}
    (hf : ∀ᶠ a in l,0≤f a) (hx : ∀ᶠ a in l,0<x a)
    (hx2 : ∀ᶠ a in l,x a≤2)
    (hlim : Tendsto (fun a=>f a/cubicScale (x a)) l (𝓝 0)) :
    Tendsto (fun a=>f a/x a) l (𝓝 0) := by
  have hupper : ∀ᶠ a in l,f a/x a≤Real.sqrt 2*(f a/cubicScale (x a)) := by
    filter_upwards [hf,hx,hx2] with a hf hx hx2
    have hs := Real.sqrt_le_sqrt hx2
    have heq : f a/x a=(f a/cubicScale (x a))*Real.sqrt (x a) := by
      unfold cubicScale
      field_simp [(Real.sqrt_pos.mpr hx).ne']
    rw [heq,mul_comm (Real.sqrt 2)]
    exact mul_le_mul_of_nonneg_left hs (div_nonneg hf (cubicScale_pos hx).le)
  have hlower : ∀ᶠ a in l,0≤f a/x a := by
    filter_upwards [hf,hx] with a hf hx
    exact div_nonneg hf hx.le
  exact squeeze_zero' hlower hupper (by simpa only [mul_zero] using hlim.const_mul (Real.sqrt 2))

theorem abs_log_radius_bound {c ε : ℝ} (hc : 0<c) (hε : 0<ε) (hsmall : c*ε≤1/2) :
    |Real.log (1-c*ε)|≤2*c*ε := by
  have hr : 0<1-c*ε := by linarith
  have hlog : Real.log (1-c*ε)≤0 := Real.log_nonpos hr.le (by nlinarith)
  have hl := Real.one_sub_inv_le_log_of_pos hr
  have hi : (1-c*ε)⁻¹≤1+2*c*ε := (inv_le_iff_one_le_mul₀ hr).mpr (by
    nlinarith [mul_nonneg (mul_pos hc hε).le (show 0≤1-2*(c*ε) by linarith)])
  rw [abs_of_nonpos hlog]
  linarith

end
end nesterov.TwoStep.Spread
