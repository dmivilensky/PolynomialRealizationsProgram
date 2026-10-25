import polyak.FareyPlateau.FanAnalysis.Constraint

/-! Actual finite fan tests with the optimal mass correction. These are
the local inputs to the all-grid convexity argument. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Actual
open General Levels ModeLocking Filter
open scoped Topology
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

def u (_A : Edge.AdjacentData q j k) : ℝ := ((k : ℝ) - 1) * k * Real.cos (Real.pi / k) / 4
def v (_A : Edge.AdjacentData q j k) : ℝ := Real.sin (Real.pi / k) / 2
def energy (e : ℝ) : ℝ := (k : ℝ) * ((k : ℝ) - 1) * second A + 2 * k * (Real.sin (Real.pi / k))^2 * e
def correction : ℝ := Fan.optimalWeight (u A) (v A) (2 * first A) k A.mix
def minimum (e : ℝ) : ℝ := Fan.optimalValue (u A) (v A) (energy A e) k A.mix
def critical : ℝ := -((k : ℝ) - 1) * deriv^[2] A.function A.frequency / (2 * (Real.sin (Real.pi / k))^3)

def phi (e δ θ : ℝ) : ℝ := constraint ((k : ℝ) - 1) (correction A) (nearAngle A e) (farAngle A e) δ θ

include A in
theorem sin_positive : 0 < Real.sin (Real.pi / k) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
  exact Real.sin_pos_of_pos_of_lt_pi (by positivity)
    ((div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos]))

include A in
theorem cos_positive : 0 < Real.cos (Real.pi / k) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
  exact Real.cos_pos_of_mem_Ioo ⟨by
      have hp : 0 < Real.pi / k := by positivity
      linarith [Real.pi_pos],
    (div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos])⟩

theorem u_positive : 0 < u A := by
  unfold u
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
  exact div_pos (mul_pos (mul_pos (by linarith) (by linarith)) (cos_positive A)) (by norm_num)

theorem v_positive : 0 < v A := div_pos (sin_positive A) (by norm_num)

theorem slope : 2 * first A = (A.lower : ℝ) + A.mix * k := by
  rw [first_actual A]
  exact A.slope

theorem minimum_source (e : ℝ) : minimum A e = (k : ℝ) / 2 *
    (-((k : ℝ) - 1) * deriv^[2] A.function A.frequency - 2 * (Real.sin (Real.pi / k))^3 * e) := by
  have hF := A.second
  rw [← second_actual A] at hF
  unfold minimum u v energy Fan.optimalValue
  rw [hF]
  ring

theorem minimum_positive {e : ℝ} (he : e < critical A) : 0 < minimum A e := by
  have hden : 0 < 2 * (Real.sin (Real.pi / k))^3 := mul_pos (by norm_num) (pow_pos (sin_positive A) _)
  have he' := (lt_div_iff₀ hden).mp he
  rw [minimum_source]
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := A.period_ge; omega)
  exact mul_pos (div_pos hkR (by norm_num)) (by linarith)

theorem edge_site_limit (e : ℝ) (m : ℤ) :
    Tendsto (fun δ => phi A e δ (2 * Real.pi / k + ((A.lower : ℝ) + (m : ℝ) * k) * δ) / (2 * δ^2))
      (𝓝[≠] 0) (𝓝 (minimum A e + u A * (((A.lower : ℝ) + (m : ℝ) * k) - A.lower) *
        (((A.lower : ℝ) + (m : ℝ) * k) - ((A.lower : ℝ) + k)))) := by
  have hh := near_edge_limit A e (correction A) ((A.lower : ℝ) + (m : ℝ) * k)
  have heq := Fan.optimal_quadratic (u := u A) (v := v A) (E := energy A e)
    (n := (A.lower : ℝ)) (k := (k : ℝ)) (t := A.mix) (v_positive A).ne' ((A.lower : ℝ) + (m : ℝ) * k)
  rw [← slope A] at heq
  change Fan.quadratic (u A) (v A) (energy A e) (2 * first A) (correction A) _ = _ at heq
  have hscaled (δ : ℝ) : phi A e δ (2 * Real.pi / k + ((A.lower : ℝ) + (m : ℝ) * k) * δ) =
      scaledConstraint ((k : ℝ) - 1) (correction A) (2 * Real.pi / k)
        ((A.lower : ℝ) + (m : ℝ) * k) (nearAngle A e) (farAngle A e) δ :=
    constraint_scaled _ _ _ _ _ _ δ
  simp only [← hscaled] at hh
  change Tendsto _ _ (𝓝 (Fan.quadratic (u A) (v A) (energy A e) (2 * first A) (correction A) _)) at hh
  rwa [heq] at hh

theorem eventually_pos_of_quadratic_limit {f : ℝ → ℝ} {a : ℝ}
    (hlim : Tendsto (fun δ => f δ / (2 * δ^2)) (𝓝[≠] 0) (𝓝 a)) (ha : 0 < a) :
    ∀ᶠ δ in 𝓝[≠] 0, 0 < f δ := by
  have hp := hlim.eventually (eventually_gt_nhds ha)
  filter_upwards [hp, self_mem_nhdsWithin] with δ hδ hn
  have hn' : δ ≠ 0 := hn
  have hden : 0 < 2 * δ^2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hn')
  simpa only [zero_mul] using (lt_div_iff₀ hden).mp hδ

theorem core_tests {e : ℝ} (he : e < critical A) :
    ∀ᶠ δ in 𝓝[≠] 0,
      0 < phi A e δ (2 * Real.pi / k + (A.lower : ℝ) * δ) ∧
      0 < phi A e δ (2 * Real.pi / k + ((A.lower : ℝ) + k) * δ) := by
  have h₀ := edge_site_limit A e 0
  have h₁ := edge_site_limit A e 1
  simp only [Int.cast_zero, zero_mul, add_zero, sub_self, mul_zero, Int.cast_one, one_mul] at h₀ h₁
  exact (eventually_pos_of_quadratic_limit h₀ (minimum_positive A he)).and
    (eventually_pos_of_quadratic_limit h₁ (minimum_positive A he))

def site (e : ℝ) (n : ℤ) (δ : ℝ) : ℝ :=
  phi A e δ (2 * Real.pi / k + ((A.lower : ℝ) + (n : ℝ) * k) * δ)

theorem site_limit (e : ℝ) (n : ℤ) :
    Tendsto (fun δ => site A e n δ / (2 * δ^2)) (𝓝[≠] 0)
      (𝓝 (minimum A e + u A * (k : ℝ)^2 * n * ((n : ℝ) - 1))) := by
  have hh := edge_site_limit A e n
  have heq : minimum A e + u A * (((A.lower : ℝ) + (n : ℝ) * k) - A.lower) *
      (((A.lower : ℝ) + (n : ℝ) * k) - ((A.lower : ℝ) + k)) =
      minimum A e + u A * (k : ℝ)^2 * n * ((n : ℝ) - 1) := by ring
  rw [heq] at hh
  exact hh

theorem outer_tests (e : ℝ) : ∀ᶠ δ in 𝓝[≠] 0,
    site A e 0 δ ≤ site A e (-1) δ ∧ site A e 1 δ ≤ site A e 2 δ := by
  have hleft := (site_limit A e (-1)).sub (site_limit A e 0)
  have hright := (site_limit A e 2).sub (site_limit A e 1)
  have hleft' : Tendsto (fun δ => (site A e (-1) δ - site A e 0 δ) / (2 * δ^2)) (𝓝[≠] 0)
      (𝓝 (2 * u A * (k : ℝ)^2)) := by
    convert hleft using 1 <;> (ext δ; ring)
  have hright' : Tendsto (fun δ => (site A e 2 δ - site A e 1 δ) / (2 * δ^2)) (𝓝[≠] 0)
      (𝓝 (2 * u A * (k : ℝ)^2)) := by
    convert hright using 1 <;> (ext δ; ring)
  have hp : 0 < 2 * u A * (k : ℝ)^2 := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := A.period_ge; omega)
    exact mul_pos (mul_pos (by norm_num) (u_positive A)) (sq_pos_of_pos hkR)
  filter_upwards [eventually_pos_of_quadratic_limit hleft' hp,
    eventually_pos_of_quadratic_limit hright' hp] with δ hl hr
  exact ⟨by linarith, by linarith⟩

theorem correction_balance : v A * correction A =
    -(u A * (2 * first A + k * (1 - 2 * A.mix))) := by
  unfold correction Fan.optimalWeight
  exact mul_div_cancel₀ _ (v_positive A).ne'

theorem zero_neighbors (e : ℝ) : ∀ᶠ δ in 𝓝[≠] 0,
    0 < phi A e δ ((k : ℝ) * δ) ∧ 0 < phi A e δ (-((k : ℝ) * δ)) := by
  have hplus := near_zero_limit A e (correction A) (k : ℝ)
  have hminus := near_zero_limit A e (correction A) (-(k : ℝ))
  have heplus : u A * ((k : ℝ)^2 - 2 * first A * k) - v A * correction A * k =
      2 * u A * (k : ℝ)^2 * (1 - A.mix) := by
    linear_combination -(k : ℝ) * correction_balance A
  have heminus : u A * ((-(k : ℝ))^2 - 2 * first A * (-(k : ℝ))) - v A * correction A * (-(k : ℝ)) =
      2 * u A * (k : ℝ)^2 * A.mix := by
    linear_combination (k : ℝ) * correction_balance A
  have hefun (y δ : ℝ) : phi A e δ (y * δ) =
      scaledConstraint ((k : ℝ) - 1) (correction A) 0 y (nearAngle A e) (farAngle A e) δ := by
    change constraint ((k : ℝ) - 1) (correction A) (nearAngle A e) (farAngle A e) δ (y * δ) = _
    simpa only [zero_add] using constraint_scaled ((k : ℝ) - 1) (correction A) 0 y (nearAngle A e) (farAngle A e) δ
  simp only [← hefun] at hplus hminus
  change Tendsto _ _ (𝓝 (u A * ((k : ℝ)^2 - 2 * first A * k) - v A * correction A * k)) at hplus
  change Tendsto _ _ (𝓝 (u A * ((-(k : ℝ))^2 - 2 * first A * (-(k : ℝ))) - v A * correction A * (-(k : ℝ)))) at hminus
  rw [heplus] at hplus
  rw [heminus] at hminus
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := A.period_ge; omega)
  have hp : 0 < 2 * u A * (k : ℝ)^2 := mul_pos (mul_pos (by norm_num) (u_positive A)) (sq_pos_of_pos hkR)
  have h₁ := eventually_pos_of_quadratic_limit hplus (mul_pos hp (sub_pos.mpr A.mix_lt))
  have h₂ := eventually_pos_of_quadratic_limit hminus (mul_pos hp A.mix_pos)
  simpa only [neg_mul] using h₁.and h₂

end polyak.FareyPlateau.FanAnalysis.Actual
