import nesterov.Flow.Model
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Article: Theorem `flow`(a), Equation (identity), and the energy estimate used
to continue solutions.  Every derivative is proved for the genuine objective
and actual velocity, rather than postulated for an abstract energy variable.
-/

noncomputable section

namespace nesterov.Flow

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The three nonnegative contributions in the Lyapunov identity. -/
def dissipation (θ m c : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  (θ - 2 * c) * delta θ m c * ‖x‖ ^ 2 +
    (θ - c) * (⟪remainderGradient m f x, x⟫_ℝ - remainder m f x) +
    (θ - 3 * c) * remainder m f x

/-- Cancellation of the gradient--velocity terms in Appendix B. -/
theorem lyapunov_balance (θ m c : ℝ) (f : E → ℝ) (x v : E) :
    ⟪remainderGradient m f x, v⟫_ℝ + delta θ m c * ⟪x, v⟫_ℝ +
      ⟪v + (θ - c) • x, -c • v - m • x - remainderGradient m f x⟫_ℝ +
      2 * c * lyapunov θ m c f x v = -dissipation θ m c f x := by
  dsimp [lyapunov, dissipation, delta]
  simp only [inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right,
    norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
  have h1 : ⟪v, remainderGradient m f x⟫_ℝ = ⟪remainderGradient m f x, v⟫_ℝ :=
    real_inner_comm _ _
  have h2 : ⟪x, remainderGradient m f x⟫_ℝ = ⟪remainderGradient m f x, x⟫_ℝ :=
    real_inner_comm _ _
  have h3 : ⟪v, x⟫_ℝ = ⟪x, v⟫_ℝ := real_inner_comm _ _
  rw [h1, h2, h3]
  ring

theorem IsSolution.hasDerivAt_lyapunov {θ m c : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Differentiable ℝ f) (hx : IsSolution θ f x v) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => lyapunov θ m c f (x s) (v s))
      (-2 * c * lyapunov θ m c f (x t) (v t) - dissipation θ m c f (x t)) t := by
  have hp := hx.position_derivative t ht
  have hv := hx.velocity_derivative t ht
  have hrem := (hasGradientAt_remainder (m := m) hf (x t)).hasFDerivAt.comp_hasDerivAt t hp
  have hrem' : HasDerivAt (fun s => remainder m f (x s))
      ⟪remainderGradient m f (x t), v t⟫_ℝ t := by
    simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hrem
  have hw := hv.add (hp.const_smul (θ - c))
  have he : (-θ • v t - gradient f (x t)) + (θ - c) • v t =
      -c • v t - m • x t - remainderGradient m f (x t) := by
    dsimp [remainderGradient]
    module
  rw [he] at hw
  have hh := (hrem'.add ((hp.norm_sq).const_mul (delta θ m c / 2))).add
    ((hw.norm_sq).div_const 2)
  simp only [Pi.add_apply, Pi.smul_apply] at hh
  convert hh using 1
  · rfl
  · have h := lyapunov_balance θ m c f (x t) (v t)
    linarith

/-- Equation (identity): the exact exponentially weighted Lyapunov derivative. -/
theorem IsSolution.hasDerivAt_weighted_lyapunov {θ m c : ℝ} {f : E → ℝ}
    {x v : ℝ → E} (hf : Differentiable ℝ f) (hx : IsSolution θ f x v)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => Real.exp (2 * c * s) * lyapunov θ m c f (x s) (v s))
      (-Real.exp (2 * c * t) * dissipation θ m c f (x t)) t := by
  have he := ((hasDerivAt_id t).const_mul (2 * c)).exp
  have hh := he.mul (hx.hasDerivAt_lyapunov hf ht (m := m) (c := c))
  convert hh using 1
  · rfl
  · dsimp only [id]
    ring

theorem dissipation_nonneg {θ m c : ℝ} {f : E → ℝ} (hf : Objective m f)
    (hc : 0 ≤ c) (hct : c ≤ θ / 3) (hd : 0 ≤ delta θ m c) (x : E) :
    0 ≤ dissipation θ m c f x := by
  dsimp [dissipation]
  exact add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg (by linarith) hd) (sq_nonneg _))
    (mul_nonneg (by linarith) (hf.remainder_support_nonneg x)))
    (mul_nonneg (by linarith) (hf.remainder_nonneg x))

/-- The weighted Lyapunov function is nonincreasing on the whole half-line. -/
theorem IsSolution.weighted_lyapunov_antitone {θ m c : ℝ} {f : E → ℝ}
    {x v : ℝ → E} (hf : Objective m f) (hx : IsSolution θ f x v)
    (hc : 0 ≤ c) (hct : c ≤ θ / 3) (hd : 0 ≤ delta θ m c) :
    AntitoneOn (fun t => Real.exp (2 * c * t) * lyapunov θ m c f (x t) (v t))
      (Set.Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
  · intro t ht
    exact (hx.hasDerivAt_weighted_lyapunov hf.differentiable ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hx.hasDerivAt_weighted_lyapunov hf.differentiable
      ((interior_subset ht) : t ∈ Set.Ici 0)).hasDerivWithinAt
  · intro t _
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le)
      (dissipation_nonneg hf hc hct hd (x t))

theorem IsSolution.lyapunov_decay {θ m c : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Objective m f) (hx : IsSolution θ f x v) (hc : 0 ≤ c)
    (hct : c ≤ θ / 3) (hd : 0 ≤ delta θ m c) {t : ℝ} (ht : 0 ≤ t) :
    lyapunov θ m c f (x t) (v t) ≤
      Real.exp (-2 * c * t) * lyapunov θ m c f (x 0) (v 0) := by
  have h := hx.weighted_lyapunov_antitone hf hc hct hd (by simp) ht ht
  simp only [mul_zero, Real.exp_zero, one_mul] at h
  have he : Real.exp (-2 * c * t) * Real.exp (2 * c * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-2 * c * t)).le
  rwa [← mul_assoc, he, one_mul] at hh

/-- An explicit coercivity constant, depending solely on θ,m,c. -/
def coercivityConstant (θ m c : ℝ) : ℝ :=
  (2 + 4 * (θ - c) ^ 2 + 4 * delta θ m c) / delta θ m c

theorem coercivityConstant_pos {θ m c : ℝ} (hd : 0 < delta θ m c) :
    0 < coercivityConstant θ m c := by
  unfold coercivityConstant
  positivity

/-- The uniform state coercivity asserted in Theorem flow(a). -/
theorem lyapunov_coercive {θ m c : ℝ} {f : E → ℝ} (hf : Objective m f)
    (hd : 0 < delta θ m c) (x v : E) :
    ‖x‖ ^ 2 + ‖v‖ ^ 2 ≤ coercivityConstant θ m c * lyapunov θ m c f x v := by
  let w := v + (θ - c) • x
  have hV : delta θ m c / 2 * ‖x‖ ^ 2 + ‖w‖ ^ 2 / 2 ≤ lyapunov θ m c f x v := by
    dsimp [lyapunov, w]
    linarith [hf.remainder_nonneg x]
  have hv : ‖v‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 + 2 * (θ - c) ^ 2 * ‖x‖ ^ 2 := by
    have he : v = w - (θ - c) • x := by dsimp [w]; module
    rw [he]
    have hh := norm_sub_le w ((θ - c) • x)
    rw [norm_smul, Real.norm_eq_abs] at hh
    have ha := abs_nonneg (θ - c)
    have hn := norm_nonneg w
    have hxn := norm_nonneg x
    have hs := (sq_le_sq₀ (norm_nonneg (w - (θ - c) • x))
      (add_nonneg hn (mul_nonneg ha hxn))).mpr hh
    nlinarith [sq_abs (θ - c), sq_nonneg (‖w‖ - |θ - c| * ‖x‖)]
  unfold coercivityConstant
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  have hx := mul_nonneg hd.le (sq_nonneg ‖x‖)
  have hw := sq_nonneg ‖w‖
  have h1 := mul_le_mul_of_nonneg_left hV (show 0 ≤ 2 + 4 * (θ - c) ^ 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hV (show 0 ≤ 4 * delta θ m c by positivity)
  nlinarith

/-- The actual state estimate in Theorem flow(a). -/
theorem IsSolution.state_decay {θ m c : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Objective m f) (hx : IsSolution θ f x v) (hc : 0 ≤ c)
    (hct : c ≤ θ / 3) (hd : 0 < delta θ m c) {t : ℝ} (ht : 0 ≤ t) :
    ‖x t‖ ^ 2 + ‖v t‖ ^ 2 ≤ coercivityConstant θ m c *
      Real.exp (-2 * c * t) * lyapunov θ m c f (x 0) (v 0) := by
  calc
    _ ≤ coercivityConstant θ m c * lyapunov θ m c f (x t) (v t) :=
      lyapunov_coercive hf hd _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hx.lyapunov_decay hf hc hct hd.le ht)
        (coercivityConstant_pos hd).le

/-- The local mechanical energy identity, requiring the equation at one time. -/
theorem hasDerivAt_energy_of_derivatives {θ : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Differentiable ℝ f) {t : ℝ} (hp : HasDerivAt x (v t) t)
    (hv : HasDerivAt v (-θ • v t - gradient f (x t)) t) :
    HasDerivAt (fun s => energy f (x s) (v s)) (-θ * ‖v t‖ ^ 2) t := by
  have hcomp := (hf (x t)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t hp
  have hcomp' : HasDerivAt (fun s => f (x s)) ⟪gradient f (x t), v t⟫_ℝ t := by
    simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hcomp
  have hh := hcomp'.add ((hv.norm_sq).div_const 2)
  convert hh using 1
  · rfl
  · simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm (v t) (gradient f (x t))]
    ring

/-- The mechanical energy identity used for the global continuation argument. -/
theorem IsSolution.hasDerivAt_energy {θ : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Differentiable ℝ f) (hx : IsSolution θ f x v) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => energy f (x s) (v s)) (-θ * ‖v t‖ ^ 2) t :=
  hasDerivAt_energy_of_derivatives hf (hx.position_derivative t ht) (hx.velocity_derivative t ht)

/-- Energy monotonicity on a partial solution interval, for continuation. -/
theorem energy_antitoneOn_Icc {θ a b : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Differentiable ℝ f) (hθ : 0 ≤ θ)
    (hp : ∀ t ∈ Set.Icc a b, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Set.Icc a b, HasDerivAt v (-θ • v t - gradient f (x t)) t) :
    AntitoneOn (fun t => energy f (x t) (v t)) (Set.Icc a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
  · intro t ht
    exact (hasDerivAt_energy_of_derivatives hf (hp t ht) (hv t ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (hasDerivAt_energy_of_derivatives hf (hp t (interior_subset ht))
      (hv t (interior_subset ht))).hasDerivWithinAt
  · intro t _
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) (sq_nonneg ‖v t‖)

theorem IsSolution.energy_antitone {θ : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Differentiable ℝ f) (hx : IsSolution θ f x v) (hθ : 0 ≤ θ) :
    AntitoneOn (fun t => energy f (x t) (v t)) (Set.Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
  · intro t ht
    exact (hx.hasDerivAt_energy hf ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hx.hasDerivAt_energy hf (interior_subset ht)).hasDerivWithinAt
  · intro t _
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) (sq_nonneg ‖v t‖)

theorem IsSolution.energy_le_initial {θ : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Differentiable ℝ f) (hx : IsSolution θ f x v) (hθ : 0 ≤ θ)
    {t : ℝ} (ht : 0 ≤ t) : energy f (x t) (v t) ≤ energy f (x 0) (v 0) :=
  hx.energy_antitone hf hθ (by simp) ht ht

theorem IsSolution.state_energy_bound {θ m : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Objective m f) (hx : IsSolution θ f x v) (hθ : 0 ≤ θ)
    {t : ℝ} (ht : 0 ≤ t) :
    m * ‖x t‖ ^ 2 + ‖v t‖ ^ 2 ≤ 2 * energy f (x 0) (v 0) := by
  have h := hx.energy_le_initial hf.differentiable hθ ht
  have hlower := hf.quadratic_lower (x t)
  dsimp [energy] at h ⊢
  linarith

end nesterov.Flow
