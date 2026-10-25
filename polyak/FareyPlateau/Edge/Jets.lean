import polyak.FareyPlateau.Edge.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Literal frequency jets of arbitrary signed lags at the two tight Farey
classes. These identities precede every finite-symbol curvature comparison. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels Filter
open scoped Topology BigOperators

theorem lag_second {θ : ℝ → ℝ} {ω : ℝ} (hθ : AnalyticAt ℝ θ ω) (n : ℤ) :
    deriv^[2] (Geometry.extendedLag θ n) ω =
      -deriv^[2] θ ω * Real.sin (θ ω) - (deriv θ ω)^2 * Real.cos (θ ω) -
        deriv^[2] θ ω * Real.sin ((n : ℝ) * ω - θ ω) +
        ((n : ℝ) - deriv θ ω)^2 * Real.cos ((n : ℝ) * ω - θ ω) := by
  have he : deriv (Geometry.extendedLag θ n) =ᶠ[𝓝 ω] Geometry.extendedLagFirst θ n := by
    filter_upwards [hθ.eventually_analyticAt] with x hx
    exact (hasDerivAt_lag_phase hx.differentiableAt.hasDerivAt n).deriv
  have hv := hθ.deriv.differentiableAt.hasDerivAt
  have ht := hθ.differentiableAt.hasDerivAt
  have hl : HasDerivAt (fun x : ℝ => (n : ℝ) * x - θ x) ((n : ℝ) - deriv θ ω) ω := by
    convert ((hasDerivAt_id ω).const_mul (n : ℝ)).sub ht using 1 <;> first | rfl | ring
  have hh := (hv.neg.mul ht.sin).add (((hasDerivAt_const ω (n : ℝ)).sub hv).mul hl.sin)
  change deriv (deriv (Geometry.extendedLag θ n)) ω = _
  rw [he.deriv_eq]
  convert hh.deriv using 1
  · rfl
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Pi.neg_apply, Pi.sub_apply]
    ring

theorem lag_first_position_one {θ : ℝ → ℝ} {ω c : ℝ}
    (hθ : AnalyticAt ℝ θ ω) (hc : θ ω = c) (n : ℤ)
    (hs : Real.sin ((n : ℝ) * ω - θ ω) = Real.sin c) :
    deriv (Geometry.extendedLag θ n) ω = Real.sin c * ((n : ℝ) - 2 * deriv θ ω) := by
  unfold Geometry.extendedLag
  rw [(hasDerivAt_lag_phase hθ.differentiableAt.hasDerivAt n).deriv, hs, hc]
  ring

theorem lag_second_position_one {θ : ℝ → ℝ} {ω c : ℝ}
    (hθ : AnalyticAt ℝ θ ω) (hc : θ ω = c) (n : ℤ)
    (hs : Real.sin ((n : ℝ) * ω - θ ω) = Real.sin c)
    (hcos : Real.cos ((n : ℝ) * ω - θ ω) = Real.cos c) :
    deriv^[2] (Geometry.extendedLag θ n) ω =
      Real.cos c * (n : ℝ) * ((n : ℝ) - 2 * deriv θ ω) -
        2 * Real.sin c * deriv^[2] θ ω := by
  rw [lag_second hθ, hs, hcos, hc]
  ring

theorem lag_first_position_zero {θ : ℝ → ℝ} {ω c : ℝ}
    (hθ : AnalyticAt ℝ θ ω) (hc : θ ω = c) (n : ℤ)
    (hs : Real.sin ((n : ℝ) * ω - θ ω) = -Real.sin c) :
    deriv (Geometry.extendedLag θ n) ω = -Real.sin c * (n : ℝ) := by
  unfold Geometry.extendedLag
  rw [(hasDerivAt_lag_phase hθ.differentiableAt.hasDerivAt n).deriv, hs, hc]
  ring

theorem lag_second_position_zero {θ : ℝ → ℝ} {ω c : ℝ}
    (hθ : AnalyticAt ℝ θ ω) (hc : θ ω = c) (n : ℤ)
    (hs : Real.sin ((n : ℝ) * ω - θ ω) = -Real.sin c)
    (hcos : Real.cos ((n : ℝ) * ω - θ ω) = Real.cos c) :
    deriv^[2] (Geometry.extendedLag θ n) ω =
      Real.cos c * (n : ℝ) * ((n : ℝ) - 2 * deriv θ ω) := by
  rw [lag_second hθ, hs, hcos, hc]
  ring

/-- The exact barycentric second moment of adjacent lags. -/
theorem adjacent_variance (n k t : ℝ) :
    (1 - t) * n * (n - (n + t * k)) +
      t * (n + k) * (n + k - (n + t * k)) = k^2 * t * (1 - t) := by
  ring

theorem adjacent_curvature (n k t c d : ℝ) :
    -(1 / 2 : ℝ) * ((1 - t) * (Real.cos c * n * (n - (n + t * k)) - 2 * Real.sin c * d) +
      t * (Real.cos c * (n + k) * (n + k - (n + t * k)) - 2 * Real.sin c * d)) =
      Real.sin c * d - (1 / 2 : ℝ) * Real.cos c * k^2 * t * (1 - t) := by
  ring

def symbol (θ : ℝ → ℝ) (n₁ n₂ : ℤ) (t : ℝ) (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ((1 - t) * Geometry.extendedLag θ n₁ x +
    t * Geometry.extendedLag θ n₂ x)

theorem symbol_first {θ : ℝ → ℝ} {ω c k t : ℝ} {n₁ n₂ : ℤ}
    (hθ : AnalyticAt ℝ θ ω) (hc : θ ω = c)
    (hn₂ : (n₂ : ℝ) = (n₁ : ℝ) + k)
    (hmean : 2 * deriv θ ω = (n₁ : ℝ) + t * k)
    (hs : ∀ n ∈ ({n₁, n₂} : Finset ℤ),
      Real.sin ((n : ℝ) * ω - θ ω) = Real.sin c) :
    deriv (symbol θ n₁ n₂ t) ω = 0 := by
  have h₁ := hasDerivAt_lag_phase hθ.differentiableAt.hasDerivAt n₁
  have h₂ := hasDerivAt_lag_phase hθ.differentiableAt.hasDerivAt n₂
  have hd := (((h₁.const_mul (1 - t)).add (h₂.const_mul t)).const_mul (-(1 / 2 : ℝ))).deriv
  change deriv (symbol θ n₁ n₂ t) ω = _ at hd
  rw [hd, hs n₁ (by simp), hs n₂ (by simp), hc, hn₂]
  have he : deriv θ ω = ((n₁ : ℝ) + t * k) / 2 := by linarith
  rw [he]
  ring

theorem symbol_second {θ : ℝ → ℝ} {ω c k t : ℝ} {n₁ n₂ : ℤ}
    (hθ : AnalyticAt ℝ θ ω) (hc : θ ω = c)
    (hn₂ : (n₂ : ℝ) = (n₁ : ℝ) + k)
    (hmean : 2 * deriv θ ω = (n₁ : ℝ) + t * k)
    (hs : ∀ n ∈ ({n₁, n₂} : Finset ℤ),
      Real.sin ((n : ℝ) * ω - θ ω) = Real.sin c)
    (hcos : ∀ n ∈ ({n₁, n₂} : Finset ℤ),
      Real.cos ((n : ℝ) * ω - θ ω) = Real.cos c) :
    deriv^[2] (symbol θ n₁ n₂ t) ω =
      Real.sin c * deriv^[2] θ ω - (1 / 2 : ℝ) * Real.cos c * k^2 * t * (1 - t) := by
  have hlag (n : ℤ) : AnalyticAt ℝ (Geometry.extendedLag θ n) ω :=
    (Real.analyticAt_cos.comp hθ).sub
      (Real.analyticAt_cos.comp ((analyticAt_const.mul analyticAt_id).sub hθ))
  have hadd : iteratedDeriv 2 (fun x => (1 - t) * Geometry.extendedLag θ n₁ x +
      t * Geometry.extendedLag θ n₂ x) ω =
      iteratedDeriv 2 (fun x => (1 - t) * Geometry.extendedLag θ n₁ x) ω +
      iteratedDeriv 2 (fun x => t * Geometry.extendedLag θ n₂ x) ω :=
    iteratedDeriv_fun_add
      ((analyticAt_const.mul (hlag n₁)).contDiffAt :
        ContDiffAt ℝ 2 (fun x => (1 - t) * Geometry.extendedLag θ n₁ x) ω)
      ((analyticAt_const.mul (hlag n₂)).contDiffAt :
        ContDiffAt ℝ 2 (fun x => t * Geometry.extendedLag θ n₂ x) ω)
  unfold symbol
  rw [← iteratedDeriv_eq_iterate, iteratedDeriv_const_mul_field, hadd,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate]
  rw [lag_second_position_one hθ hc n₁ (hs n₁ (by simp)) (hcos n₁ (by simp)),
    lag_second_position_one hθ hc n₂ (hs n₂ (by simp)) (hcos n₂ (by simp))]
  rw [hmean, hn₂]
  exact adjacent_curvature _ _ _ _ _

end polyak.FareyPlateau.Edge
