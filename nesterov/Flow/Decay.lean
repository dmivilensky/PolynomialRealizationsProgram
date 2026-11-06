import nesterov.Flow.Lyapunov
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Article: §3, the decay exponent in Theorem `flow`(d).
Use: the literal continuous-time logarithmic liminf, in extended reals so
that a zero observable has exponent +∞.  Nonzero exponential observables
have finite exact exponents, proved by squeezing their logarithmic slopes.
-/

noncomputable section

namespace nesterov.Flow

open Filter
open scoped Topology

/-- Extended logarithmic slope, with the usual log(0)=-∞ convention. -/
def logarithmicSlope (y t : ℝ) : EReal :=
  if y = 0 then ⊤ else ((-Real.log y / t : ℝ) : EReal)

def observableExponent (y : ℝ → ℝ) : EReal :=
  Filter.liminf (fun t : ℝ => logarithmicSlope (y t) t) Filter.atTop

variable {E : Type*} [NormedAddCommGroup E]

/-- The article's state exponent ℓ(x), using the actual velocity. -/
def decayExponent (x v : ℝ → E) : EReal :=
  observableExponent (fun t => ‖x t‖ + ‖v t‖)

theorem logarithmicSlope_lower {y t C c : ℝ} (ht : 0 < t) (hC : 0 < C)
    (hy : 0 ≤ y) (hupper : y ≤ C * Real.exp (-c * t)) :
    ((c - Real.log C / t : ℝ) : EReal) ≤ logarithmicSlope y t := by
  unfold logarithmicSlope
  split_ifs with hzero
  · exact le_top
  · have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hzero)
    have hlog := Real.log_le_log hyp hupper
    rw [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _), Real.log_exp] at hlog
    apply EReal.coe_le_coe_iff.mpr
    apply (le_div_iff₀ ht).mpr
    have he : (c - Real.log C / t) * t = c * t - Real.log C := by
      field_simp
    rw [he]
    linarith

theorem logarithmicSlope_upper {y t C c : ℝ} (ht : 0 < t) (hC : 0 < C)
    (hlower : C * Real.exp (-c * t) ≤ y) :
    logarithmicSlope y t ≤ ((c - Real.log C / t : ℝ) : EReal) := by
  have hyp : 0 < y := (mul_pos hC (Real.exp_pos _)).trans_le hlower
  rw [logarithmicSlope, ite_eq_right (ne_of_gt hyp)]
  have hlog := Real.log_le_log (mul_pos hC (Real.exp_pos _)) hlower
  rw [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _), Real.log_exp] at hlog
  apply EReal.coe_le_coe_iff.mpr
  apply (div_le_iff₀ ht).mpr
  have he : (c - Real.log C / t) * t = c * t - Real.log C := by field_simp
  rw [he]
  linarith

theorem observableExponent_ge_of_exp_bound {y : ℝ → ℝ} {C c : ℝ} (hC : 0 < C)
    (h : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ C * Real.exp (-c * t)) :
    (c : EReal) ≤ observableExponent y := by
  have hlim : Tendsto (fun t : ℝ => c - Real.log C / t) atTop (𝓝 c) := by
    have hh : Tendsto (fun t : ℝ => Real.log C / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using tendsto_const_nhds.sub hh
  have hlim' := (EReal.tendsto_coe.mpr hlim).liminf_eq
  rw [← hlim']
  refine Filter.liminf_le_liminf ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact logarithmicSlope_lower ht hC (h t ht.le).1 (h t ht.le).2

theorem observableExponent_eq_of_two_sided_exp_bounds {y : ℝ → ℝ} {C₁ C₂ c : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (h : ∀ t : ℝ, 0 ≤ t → C₁ * Real.exp (-c * t) ≤ y t ∧ y t ≤ C₂ * Real.exp (-c * t)) :
    observableExponent y = (c : EReal) := by
  apply le_antisymm
  · have hlim : Tendsto (fun t : ℝ => c - Real.log C₁ / t) atTop (𝓝 c) := by
      have hh : Tendsto (fun t : ℝ => Real.log C₁ / t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using tendsto_const_nhds.sub hh
    have hlim' := (EReal.tendsto_coe.mpr hlim).liminf_eq
    rw [← hlim']
    refine Filter.liminf_le_liminf ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact logarithmicSlope_upper ht hC₁ (h t ht.le).1
  · apply observableExponent_ge_of_exp_bound hC₂
    intro t ht
    exact ⟨(mul_pos hC₁ (Real.exp_pos _)).le.trans (h t ht).1, (h t ht).2⟩

theorem observableExponent_exact_exp {y : ℝ → ℝ} {C c : ℝ} (hC : 0 < C)
    (h : ∀ t : ℝ, 0 ≤ t → y t = C * Real.exp (-c * t)) :
    observableExponent y = (c : EReal) := by
  apply observableExponent_eq_of_two_sided_exp_bounds hC hC
  intro t ht
  rw [h t ht]
  exact ⟨le_rfl, le_rfl⟩

section Hilbert

variable [InnerProductSpace ℝ E] [CompleteSpace E]

theorem lyapunov_nonneg {θ m c : ℝ} {f : E → ℝ} (hf : Objective m f)
    (hd : 0 ≤ delta θ m c) (x v : E) : 0 ≤ lyapunov θ m c f x v := by
  dsimp [lyapunov]
  exact add_nonneg (add_nonneg (hf.remainder_nonneg x)
    (mul_nonneg (by positivity) (sq_nonneg _))) (by positivity)

/-- A global exponential norm estimate with a positive constant, derived
from the actual Lyapunov state estimate. -/
theorem IsSolution.norm_exp_bound {θ m c : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Objective m f) (hx : IsSolution θ f x v) (hc : 0 ≤ c)
    (hct : c ≤ θ / 3) (hd : 0 < delta θ m c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖x t‖ + ‖v t‖ ≤ C * Real.exp (-c * t) := by
  let D := coercivityConstant θ m c * lyapunov θ m c f (x 0) (v 0)
  have hD : 0 ≤ D := mul_nonneg (coercivityConstant_pos hd).le (lyapunov_nonneg hf hd.le _ _)
  refine ⟨D + 1, by linarith, ?_⟩
  intro t ht
  have hstate := hx.state_decay hf hc hct hd ht
  have he : Real.exp (-2 * c * t) = Real.exp (-c * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hstate' : ‖x t‖ ^ 2 + ‖v t‖ ^ 2 ≤ D * Real.exp (-c * t) ^ 2 := by
    rw [← he]
    dsimp [D]
    nlinarith
  have hsum : (‖x t‖ + ‖v t‖) ^ 2 ≤ 2 * (‖x t‖ ^ 2 + ‖v t‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x t‖ - ‖v t‖)]
  have hC : 2 * D ≤ (D + 1) ^ 2 := by nlinarith [sq_nonneg D]
  have hmul := mul_le_mul_of_nonneg_right hC (sq_nonneg (Real.exp (-c * t)))
  have hn : 0 ≤ ‖x t‖ + ‖v t‖ := by positivity
  have hr : 0 ≤ (D + 1) * Real.exp (-c * t) := by positivity
  apply (sq_le_sq₀ hn hr).mp
  nlinarith

theorem IsSolution.decayExponent_ge {θ m c : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Objective m f) (hx : IsSolution θ f x v) (hc : 0 ≤ c)
    (hct : c ≤ θ / 3) (hd : 0 < delta θ m c) :
    (c : EReal) ≤ decayExponent x v := by
  obtain ⟨C, hC, hbound⟩ := hx.norm_exp_bound hf hc hct hd
  apply observableExponent_ge_of_exp_bound hC
  exact fun t ht => ⟨by positivity, hbound t ht⟩

/-- Theorem flow(d), the universal lower bound for the literal state exponent. -/
theorem IsSolution.cF_le_decayExponent {θ m : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hθ : 0 < θ) (hf : Objective m f) (hx : IsSolution θ f x v) :
    (cF θ m : EReal) ≤ decayExponent x v := by
  by_contra h
  obtain ⟨c, hc, hcF⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hcF' : c < cF θ m := EReal.coe_lt_coe_iff.mp hcF
  have hpos := cF_pos hθ hf.m_pos
  let d := max c (cF θ m / 2)
  have hd : 0 < d := lt_of_lt_of_le (by linarith : 0 < cF θ m / 2) (le_max_right _ _)
  have hdF : d < cF θ m := max_lt hcF' (by linarith)
  obtain ⟨hthird, _, hdelta⟩ := (lt_cF_iff θ m d).mp hdF
  have hlow := hx.decayExponent_ge hf hd.le hthird.le hdelta
  have hcd : (c : EReal) ≤ (d : EReal) := EReal.coe_le_coe_iff.mpr (le_max_left _ _)
  exact (not_lt_of_ge (hcd.trans hlow)) hc

/-- The endpoint O(exp(-θt/3)) estimate in Theorem flow(d), with an actual
global bound for every nonnegative time. -/
theorem IsSolution.third_rate_bound {θ m : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hθ : 0 < θ) (hf : Objective m f) (hx : IsSolution θ f x v)
    (hdamp : θ < 3 * Real.sqrt (m / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖x t‖ + ‖v t‖ ≤ C * Real.exp (-(θ / 3) * t) := by
  apply hx.norm_exp_bound hf (by linarith) le_rfl
  have hs := Real.sq_sqrt (show 0 ≤ m / 2 by linarith [hf.m_pos])
  have ha := Real.sqrt_nonneg (m / 2)
  dsimp [delta]
  nlinarith

theorem objective_value_le_lyapunov {θ m c : ℝ} {f : E → ℝ} (hf : Objective m f)
    (hd : 0 < delta θ m c) (x v : E) :
    f x ≤ (1 + m / delta θ m c) * lyapunov θ m c f x v := by
  have hrem := hf.remainder_nonneg x
  have hx := sq_nonneg ‖x‖
  have hw := sq_nonneg ‖v + (θ - c) • x‖
  have hV := lyapunov_nonneg hf hd.le x v
  have hmodel : remainder m f x + delta θ m c / 2 * ‖x‖ ^ 2 ≤ lyapunov θ m c f x v := by
    dsimp [lyapunov]
    linarith
  have hremV : remainder m f x ≤ lyapunov θ m c f x v := by
    nlinarith [mul_nonneg hd.le hx]
  have hxV : delta θ m c / 2 * ‖x‖ ^ 2 ≤ lyapunov θ m c f x v := by linarith
  have hm := mul_le_mul_of_nonneg_left hxV hf.m_pos.le
  have hremd := mul_le_mul_of_nonneg_left hremV hd.le
  have hmul : delta θ m c * f x ≤ (delta θ m c + m) * lyapunov θ m c f x v := by
    dsimp [remainder] at hremd
    nlinarith
  have he : (1 + m / delta θ m c) * lyapunov θ m c f x v =
      ((delta θ m c + m) * lyapunov θ m c f x v) / delta θ m c := by
    field_simp
  rw [he]
  apply (le_div_iff₀ hd).mpr
  nlinarith

/-- The same Lyapunov estimate bounds both the actual gap and mechanical
energy with the doubled exponent, without a global smoothness assumption. -/
theorem IsSolution.value_energy_exp_bound {θ m c : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Objective m f) (hx : IsSolution θ f x v) (hc : 0 ≤ c)
    (hct : c ≤ θ / 3) (hd : 0 < delta θ m c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      (0 ≤ f (x t) ∧ f (x t) ≤ C * Real.exp (-(2 * c) * t)) ∧
      (0 ≤ energy f (x t) (v t) ∧ energy f (x t) (v t) ≤ C * Real.exp (-(2 * c) * t)) := by
  let A := 1 + m / delta θ m c
  let K := coercivityConstant θ m c
  let V := lyapunov θ m c f (x 0) (v 0)
  have hA : 0 < A := by
    have hm := hf.m_pos
    dsimp [A]
    positivity
  have hK : 0 < K := coercivityConstant_pos hd
  have hV : 0 ≤ V := lyapunov_nonneg hf hd.le _ _
  refine ⟨(A + K) * V + 1, by positivity, ?_⟩
  intro t ht
  have hdec := hx.lyapunov_decay hf hc hct hd.le ht
  have hstate := hx.state_decay hf hc hct hd ht
  rw [show -2 * c * t = -(2 * c) * t by ring] at hdec hstate
  have hobj := objective_value_le_lyapunov hf hd (x t) (v t)
  have hval : f (x t) ≤ A * (Real.exp (-(2 * c) * t) * V) := by
    have hh := mul_le_mul_of_nonneg_left hdec hA.le
    dsimp [A, V] at *
    nlinarith
  have hvel : ‖v t‖ ^ 2 ≤ K * Real.exp (-(2 * c) * t) * V := by
    dsimp [K, V]
    nlinarith [sq_nonneg ‖x t‖]
  have hfnonneg : 0 ≤ f (x t) := (mul_nonneg (by linarith [hf.m_pos])
    (sq_nonneg ‖x t‖)).trans (hf.quadratic_lower (x t))
  have henergy : 0 ≤ energy f (x t) (v t) := by dsimp [energy]; positivity
  have hexp := Real.exp_pos (-(2 * c) * t)
  have hKV := mul_nonneg hK.le hV
  refine ⟨⟨hfnonneg, ?_⟩, henergy, ?_⟩
  · nlinarith [mul_nonneg hKV hexp.le]
  · dsimp [energy]
    nlinarith

theorem IsSolution.value_energy_exponents_ge {θ m : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hθ : 0 < θ) (hf : Objective m f) (hx : IsSolution θ f x v) :
    ((2 * cF θ m : ℝ) : EReal) ≤ observableExponent (fun t => f (x t)) ∧
      ((2 * cF θ m : ℝ) : EReal) ≤ observableExponent (fun t => energy f (x t) (v t)) := by
  have hpos := cF_pos hθ hf.m_pos
  have hbound (c : ℝ) (hc : 0 < c) (hcF : c < cF θ m) :
      ((2 * c : ℝ) : EReal) ≤ observableExponent (fun t => f (x t)) ∧
        ((2 * c : ℝ) : EReal) ≤ observableExponent (fun t => energy f (x t) (v t)) := by
    obtain ⟨hthird, _, hdelta⟩ := (lt_cF_iff θ m c).mp hcF
    obtain ⟨C, hC, h⟩ := hx.value_energy_exp_bound hf hc.le hthird.le hdelta
    exact ⟨observableExponent_ge_of_exp_bound hC (fun t ht => (h t ht).1),
      observableExponent_ge_of_exp_bound hC (fun t ht => (h t ht).2)⟩
  have horder (z : EReal) (hz : ∀ c : ℝ, 0 < c → c < cF θ m → ((2 * c : ℝ) : EReal) ≤ z) :
      ((2 * cF θ m : ℝ) : EReal) ≤ z := by
    by_contra h
    obtain ⟨a, hza, ha⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
    have ha' : a < 2 * cF θ m := EReal.coe_lt_coe_iff.mp ha
    let c := max (a / 2) (cF θ m / 2)
    have hc : 0 < c := lt_of_lt_of_le (by linarith : 0 < cF θ m / 2) (le_max_right _ _)
    have hcF : c < cF θ m := max_lt (by linarith) (by linarith)
    have hac : a ≤ 2 * c := by have hh := le_max_left (a / 2) (cF θ m / 2); linarith
    exact (not_lt_of_ge ((EReal.coe_le_coe_iff.mpr hac).trans (hz c hc hcF))) hza
  exact ⟨horder _ (fun c hc hcF => (hbound c hc hcF).1),
    horder _ (fun c hc hcF => (hbound c hc hcF).2)⟩

end Hilbert

end nesterov.Flow
