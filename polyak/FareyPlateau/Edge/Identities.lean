import polyak.FareyPlateau.Edge.Jets

/-! Exact edge identities before taking derivatives. The displacement is
arbitrary and all signed lags in the two tight classes are retained. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open Levels

theorem position_one_identity {j k : ℕ} (hk : 0 < k) (hjk : 2 * j ≤ k)
    (θ : ℝ → ℝ) (n : ℤ) (hn : (n * j) % k = 1) (δ : ℝ) :
    Geometry.extendedLag θ n ((atom j k hk hjk : ℝ) + δ) =
      2 * Real.sin (Real.pi / k + (n : ℝ) * δ / 2) *
        Real.sin (Real.pi / k + (n : ℝ) * δ / 2 - θ ((atom j k hk hjk : ℝ) + δ)) := by
  let x := (atom j k hk hjk : ℝ) + δ
  have hr := (lag_trig_reduce hk hjk n (θ x - (n : ℝ) * δ)).1
  rw [hn] at hr
  simp only [Int.cast_one, mul_one] at hr
  have he₁ : (n : ℝ) * x - θ x =
      (n : ℝ) * (atom j k hk hjk : ℝ) - (θ x - (n : ℝ) * δ) := by dsimp [x]; ring
  have he₂ : 2 * Real.pi / k - (θ x - (n : ℝ) * δ) =
      (2 * Real.pi / k + (n : ℝ) * δ) - θ x := by ring
  change Real.cos (θ x) - Real.cos ((n : ℝ) * x - θ x) = _
  rw [he₁, hr, he₂]
  have hval := Lattice.lagValue_eq_sines (θ x) (2 * Real.pi / k + (n : ℝ) * δ)
  unfold Lattice.lagValue at hval
  rw [hval]
  rw [show (2 * Real.pi / (k : ℝ) + (n : ℝ) * δ) / 2 =
    Real.pi / k + (n : ℝ) * δ / 2 by ring]

theorem position_zero_identity {j k : ℕ} (hk : 0 < k) (hjk : 2 * j ≤ k)
    (θ : ℝ → ℝ) (n : ℤ) (hn : (n * j) % k = 0) (δ : ℝ) :
    Geometry.extendedLag θ n ((atom j k hk hjk : ℝ) + δ) =
      2 * Real.sin ((n : ℝ) * δ / 2) *
        Real.sin ((n : ℝ) * δ / 2 - θ ((atom j k hk hjk : ℝ) + δ)) := by
  let x := (atom j k hk hjk : ℝ) + δ
  have hr := (lag_trig_reduce hk hjk n (θ x - (n : ℝ) * δ)).1
  rw [hn] at hr
  simp only [Int.cast_zero, mul_zero, zero_div, zero_sub, Real.cos_neg] at hr
  have he₁ : (n : ℝ) * x - θ x =
      (n : ℝ) * (atom j k hk hjk : ℝ) - (θ x - (n : ℝ) * δ) := by dsimp [x]; ring
  change Real.cos (θ x) - Real.cos ((n : ℝ) * x - θ x) = _
  rw [he₁, hr, show θ x - (n : ℝ) * δ = -((n : ℝ) * δ - θ x) by ring, Real.cos_neg]
  exact Lattice.lagValue_eq_sines _ _

end polyak.FareyPlateau.Edge
