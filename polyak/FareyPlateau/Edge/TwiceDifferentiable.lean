import polyak.FareyPlateau.Edge.Jets

/-! Literal twice-differentiable generality of the edge identities.
The first derivative exists near the point and is differentiable at it;
no continuity of its derivative or analyticity is required. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels Filter
open scoped Topology

theorem lag_second_twice {θ : ℝ → ℝ} {ω : ℝ} (hθ : ∀ᶠ x in 𝓝 ω, DifferentiableAt ℝ θ x)
    (h₂ : DifferentiableAt ℝ (deriv θ) ω) (n : ℤ) :
    deriv^[2] (Geometry.extendedLag θ n) ω =
      -deriv^[2] θ ω * Real.sin (θ ω) - (deriv θ ω)^2 * Real.cos (θ ω) -
        deriv^[2] θ ω * Real.sin ((n : ℝ) * ω - θ ω) +
        ((n : ℝ) - deriv θ ω)^2 * Real.cos ((n : ℝ) * ω - θ ω) := by
  have he : deriv (Geometry.extendedLag θ n) =ᶠ[𝓝 ω] Geometry.extendedLagFirst θ n := by
    filter_upwards [hθ] with x hx
    exact (hasDerivAt_lag_phase hx.hasDerivAt n).deriv
  have hv := h₂.hasDerivAt
  have ht := hθ.self_of_nhds.hasDerivAt
  have hl : HasDerivAt (fun x : ℝ => (n : ℝ) * x - θ x) ((n : ℝ) - deriv θ ω) ω := by
    convert ((hasDerivAt_id ω).const_mul (n : ℝ)).sub ht using 1 <;> first | rfl | ring
  have hh := (hv.neg.mul ht.sin).add (((hasDerivAt_const ω (n : ℝ)).sub hv).mul hl.sin)
  change deriv (deriv (Geometry.extendedLag θ n)) ω = _
  rw [he.deriv_eq]
  convert hh.deriv using 1
  · rfl
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Pi.neg_apply, Pi.sub_apply]
    ring

theorem lag_first_position_one_twice {θ : ℝ → ℝ} {ω c : ℝ}
    (hθ : ∀ᶠ x in 𝓝 ω, DifferentiableAt ℝ θ x)
    (hc : θ ω = c) (n : ℤ)
    (hs : Real.sin ((n : ℝ) * ω - θ ω) = Real.sin c) :
    deriv (Geometry.extendedLag θ n) ω = Real.sin c * ((n : ℝ) - 2 * deriv θ ω) := by
  unfold Geometry.extendedLag
  rw [(hasDerivAt_lag_phase hθ.self_of_nhds.hasDerivAt n).deriv, hs, hc]
  ring

theorem lag_second_position_one_twice {θ : ℝ → ℝ} {ω c : ℝ}
    (hθ : ∀ᶠ x in 𝓝 ω, DifferentiableAt ℝ θ x)
    (h₂ : DifferentiableAt ℝ (deriv θ) ω) (hc : θ ω = c) (n : ℤ)
    (hs : Real.sin ((n : ℝ) * ω - θ ω) = Real.sin c)
    (hcos : Real.cos ((n : ℝ) * ω - θ ω) = Real.cos c) :
    deriv^[2] (Geometry.extendedLag θ n) ω =
      Real.cos c * (n : ℝ) * ((n : ℝ) - 2 * deriv θ ω) -
        2 * Real.sin c * deriv^[2] θ ω := by
  rw [lag_second_twice hθ h₂, hs, hcos, hc]
  ring

theorem lag_first_position_zero_twice {θ : ℝ → ℝ} {ω c : ℝ}
    (hθ : ∀ᶠ x in 𝓝 ω, DifferentiableAt ℝ θ x)
    (hc : θ ω = c) (n : ℤ)
    (hs : Real.sin ((n : ℝ) * ω - θ ω) = -Real.sin c) :
    deriv (Geometry.extendedLag θ n) ω = -Real.sin c * (n : ℝ) := by
  unfold Geometry.extendedLag
  rw [(hasDerivAt_lag_phase hθ.self_of_nhds.hasDerivAt n).deriv, hs, hc]
  ring

theorem lag_second_position_zero_twice {θ : ℝ → ℝ} {ω c : ℝ}
    (hθ : ∀ᶠ x in 𝓝 ω, DifferentiableAt ℝ θ x)
    (h₂ : DifferentiableAt ℝ (deriv θ) ω) (hc : θ ω = c) (n : ℤ)
    (hs : Real.sin ((n : ℝ) * ω - θ ω) = -Real.sin c)
    (hcos : Real.cos ((n : ℝ) * ω - θ ω) = Real.cos c) :
    deriv^[2] (Geometry.extendedLag θ n) ω =
      Real.cos c * (n : ℝ) * ((n : ℝ) - 2 * deriv θ ω) := by
  rw [lag_second_twice hθ h₂, hs, hcos, hc]
  ring


end polyak.FareyPlateau.Edge
