import polyak.FareyPlateau.Edge.LatticeCurvature

/-! Exact max--min problem in the fan's quadratic limit. All lattice sites
are retained; the two adjacent sites are proved to be optimal. -/
noncomputable section
namespace polyak.FareyPlateau.Fan

def quadratic (u v E N z y : ℝ) : ℝ :=
  u * (y^2 - N * y) + v * z * (y - N) - v * E

def optimalWeight (u v N k t : ℝ) : ℝ := -(u * (N + k * (1 - 2 * t))) / v

def optimalValue (u v E k t : ℝ) : ℝ := u * k^2 * t * (1 - t) - v * E

theorem optimal_quadratic {u v E n k t : ℝ} (hv : v ≠ 0) (y : ℝ) :
    quadratic u v E (n + t * k) (optimalWeight u v (n + t * k) k t) y =
      optimalValue u v E k t + u * (y - n) * (y - (n + k)) := by
  unfold quadratic optimalWeight optimalValue
  field_simp
  ring

theorem lattice_minimum {u v E n k t : ℝ} (hu : 0 ≤ u) (hv : v ≠ 0) (m : ℤ) :
    optimalValue u v E k t ≤ quadratic u v E (n + t * k)
      (optimalWeight u v (n + t * k) k t) (n + (m : ℝ) * k) := by
  rw [optimal_quadratic hv]
  have hp := mul_nonneg hu (Edge.adjacent_lattice_product (n₁ := n) (k := k) m)
  nlinarith only [hp]

theorem left_attains {u v E n k t : ℝ} (hv : v ≠ 0) :
    quadratic u v E (n + t * k) (optimalWeight u v (n + t * k) k t) n =
      optimalValue u v E k t := by
  rw [optimal_quadratic hv]
  ring

theorem right_attains {u v E n k t : ℝ} (hv : v ≠ 0) :
    quadratic u v E (n + t * k) (optimalWeight u v (n + t * k) k t) (n + k) =
      optimalValue u v E k t := by
  rw [optimal_quadratic hv]
  ring

/-- No other mass correction can improve both adjacent constraints. -/
theorem adjacent_max_min {u v E n k t : ℝ} (hk : 0 < k)
    (ht0 : 0 < t) (ht1 : t < 1) (z : ℝ) :
    min (quadratic u v E (n + t * k) z n)
      (quadratic u v E (n + t * k) z (n + k)) ≤ optimalValue u v E k t := by
  have he : (1 - t) * quadratic u v E (n + t * k) z n +
      t * quadratic u v E (n + t * k) z (n + k) = optimalValue u v E k t := by
    unfold quadratic optimalValue
    ring
  have hl := min_le_left (quadratic u v E (n + t * k) z n)
    (quadratic u v E (n + t * k) z (n + k))
  have hr := min_le_right (quadratic u v E (n + t * k) z n)
    (quadratic u v E (n + t * k) z (n + k))
  have hl' := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr ht1.le)
  have hr' := mul_le_mul_of_nonneg_left hr ht0.le
  have _ := hk
  nlinarith only [he, hl', hr']

theorem optimal_coefficient (k t c d e : ℝ) :
    optimalValue (k * (k - 1) * Real.cos c / 4) (Real.sin c / 2)
      (k * (k - 1) * d + 2 * k * (Real.sin c)^2 * e) k t =
      k / 2 * (-(k - 1) * (Real.sin c * d - Real.cos c * k^2 * t * (1 - t) / 2) -
        2 * (Real.sin c)^3 * e) := by
  unfold optimalValue
  ring

end polyak.FareyPlateau.Fan
