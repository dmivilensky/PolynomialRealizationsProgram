import polyak.FareyPlateau.FanAnalysis.Constraint

/-! Uniform perturbation bounds on the entire phase circle, independent
of the grid size and lag. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter
open scoped Topology

def cosineDefect (θ a : ℝ) : ℝ := Real.cos a - Real.cos (θ - a)

theorem cosineDefect_abs (θ a : ℝ) : |cosineDefect θ a| ≤ 2 := by
  unfold cosineDefect
  exact (abs_sub _ _).trans (by linarith [Real.abs_cos_le_one a, Real.abs_cos_le_one (θ - a)])

theorem cosineDefect_lipschitz (θ a b : ℝ) :
    |cosineDefect θ a - cosineDefect θ b| ≤ 2 * |a - b| := by
  have he : cosineDefect θ a - cosineDefect θ b =
      (Real.cos a - Real.cos b) - (Real.cos (θ - a) - Real.cos (θ - b)) := by unfold cosineDefect; ring
  rw [he]
  have h₁ := Real.abs_cos_sub_cos_le a b
  have h₂ := Real.abs_cos_sub_cos_le (θ - a) (θ - b)
  have he' : (θ - a) - (θ - b) = -(a - b) := by ring
  rw [he', abs_neg] at h₂
  exact (abs_sub _ _).trans (by linarith)

def baseline (m c θ : ℝ) : ℝ := m * cosineDefect θ c + cosineDefect (-m * θ) c

theorem constraint_eq (m z : ℝ) (a c : ℝ → ℝ) (δ θ : ℝ) :
    constraint m z a c δ θ = (m + z * δ) * cosineDefect θ (a δ) + cosineDefect (-m * θ) (c δ) := by
  unfold constraint cosineDefect
  rw [show -m * θ - c δ = -(m * θ + c δ) by ring, Real.cos_neg]
  ring

theorem uniform_constraint_bound {m z c₀ : ℝ} (hm : 0 ≤ m)
    (a c : ℝ → ℝ) (δ θ : ℝ) :
    |constraint m z a c δ θ - baseline m c₀ θ| ≤
      2 * |z * δ| + 2 * m * |a δ - c₀| + 2 * |c δ - c₀| := by
  have he : constraint m z a c δ θ - baseline m c₀ θ =
      z * δ * cosineDefect θ (a δ) + m * (cosineDefect θ (a δ) - cosineDefect θ c₀) +
        (cosineDefect (-m * θ) (c δ) - cosineDefect (-m * θ) c₀) := by
    rw [constraint_eq]
    unfold baseline
    ring
  rw [he]
  have h₁ : |z * δ * cosineDefect θ (a δ)| ≤ 2 * |z * δ| := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left (cosineDefect_abs θ (a δ)) (abs_nonneg (z * δ))]
  have h₂ : |m * (cosineDefect θ (a δ) - cosineDefect θ c₀)| ≤ 2 * m * |a δ - c₀| := by
    rw [abs_mul, abs_of_nonneg hm]
    nlinarith [mul_le_mul_of_nonneg_left (cosineDefect_lipschitz θ (a δ) c₀) hm]
  have h₃ := cosineDefect_lipschitz (-m * θ) (c δ) c₀
  have ht₁ := abs_add_le (z * δ * cosineDefect θ (a δ)) (m * (cosineDefect θ (a δ) - cosineDefect θ c₀))
  have ht₂ := abs_add_le (z * δ * cosineDefect θ (a δ) + m * (cosineDefect θ (a δ) - cosineDefect θ c₀))
    (cosineDefect (-m * θ) (c δ) - cosineDefect (-m * θ) c₀)
  linarith

theorem eventually_uniform_constraint_close {m z c₀ : ℝ} (hm : 0 ≤ m)
    {a c : ℝ → ℝ} (ha : ContinuousAt a 0) (hc : ContinuousAt c 0)
    (ha0 : a 0 = c₀) (hc0 : c 0 = c₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ in 𝓝 0, ∀ θ : ℝ, |constraint m z a c δ θ - baseline m c₀ θ| < ε := by
  have hE : ContinuousAt (fun δ => 2 * |z * δ| + 2 * m * |a δ - c₀| + 2 * |c δ - c₀|) 0 := by
    fun_prop
  have hzero : 2 * |z * (0 : ℝ)| + 2 * m * |a 0 - c₀| + 2 * |c 0 - c₀| = 0 := by
    simp only [mul_zero, abs_zero, ha0, hc0, sub_self, mul_zero, add_zero]
  have he := hE.eventually (eventually_lt_nhds (show 2 * |z * (0 : ℝ)| + 2 * m * |a 0 - c₀| + 2 * |c 0 - c₀| < ε by rwa [hzero]))
  filter_upwards [he] with δ hδ θ
  exact (uniform_constraint_bound hm a c δ θ).trans_lt hδ

end polyak.FareyPlateau.FanAnalysis
