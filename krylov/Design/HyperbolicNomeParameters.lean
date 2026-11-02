import krylov.Design.ShiftedPoisson
import krylov.Design.SechLatticeSquare

/-!
Article: main_krylov, apC:lem:poisson, genuine hyperbolic elliptic-modulus parameters.
Use: construct the modulus from actual ordinary/alternating sech masses, prove
its strict real domain and true complementary square root, and evaluate the
actual large-spacing limits needed by the integral-preserving Gauss iteration.
Source: actual half-lattice Poisson positivity, exact integer parity, and the
independently proved exponentially decaying primary series.
-/

namespace krylov.Design
noncomputable section
open Real Filter Set jacobi.Young
open scoped Topology

/-- The actual odd-lattice projection of any absolutely convergent integer series.
Article: main_krylov, apC:lem:poisson. -/
theorem tsum_integer_odd_projection (f : ℤ → ℝ) (hf : Summable f) :
    (∑' n : ℤ, f n) - (∑' n : ℤ, (-1 : ℝ) ^ n * f n) =
      2 * ∑' n : ℤ, f (2 * n + 1) := by
  have ha := alternating_integer_summable f hf
  rw [← hf.tsum_sub ha, tsum_integer_even_odd _ (hf.sub ha), ← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : (-1 : ℝ) ^ (2 * n) = 1 := Even.neg_one_zpow ⟨n, by ring⟩
  have ho : (-1 : ℝ) ^ (2 * n + 1) = -1 := Odd.neg_one_zpow ⟨n, by ring⟩
  rw [he, ho]
  ring

/-- The true half-lattice mass is exactly the odd projection of the ordinary/alternating masses.
Article: main_krylov, apC:lem:poisson, the complementary period dictionary. -/
theorem latticeSechMass_sub_alternating {θ : ℝ} (hθ : 0 < θ) :
    latticeSechMass θ - latticeSechAlternatingMass θ = 2 * latticeSechHalfMass (2 * θ) := by
  have h := tsum_integer_odd_projection (fun n : ℤ => sech ((n : ℝ) * θ)) (sech_integer_summable hθ)
  have he : (∑' n : ℤ, sech ((((2 * n + 1 : ℤ)) : ℝ) * θ)) = latticeSechHalfMass (2 * θ) := by
    apply tsum_congr
    intro n
    rw [show (((2 * n + 1 : ℤ)) : ℝ) * θ = ((n : ℝ) + 1 / 2) * (2 * θ) by push_cast; ring]
  simpa only [latticeSechMass, latticeSechAlternatingMass, he] using h

/-- Actual ordinary and alternating sech masses have the strict positive ordering needed for a real elliptic modulus.
Article: main_krylov, apC:lem:poisson. -/
theorem latticeSechMass_strict_domain {θ : ℝ} (hθ : 0 < θ) :
    0 < latticeSechAlternatingMass θ ∧ latticeSechAlternatingMass θ < latticeSechMass θ := by
  refine ⟨latticeSechAlternatingMass_pos hθ, ?_⟩
  have h := latticeSechHalfMass_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hθ)
  have he := latticeSechMass_sub_alternating hθ
  linarith

/-- The actual modulus determined by genuine hyperbolic lattice masses.
Article: main_krylov, apC:lem:poisson.
This is a physical square-root ratio; the complete elliptic integral keeps its
independently defined integral meaning. -/
def sechModulus (θ : ℝ) : ℝ :=
  sqrt (1 - (latticeSechAlternatingMass θ / latticeSechMass θ) ^ 2)

/-- The genuine hyperbolic mass ratio is strictly between zero and one.
Article: main_krylov, apC:lem:poisson, the actual elliptic modulus domain. -/
theorem sechMassRatio_mem {θ : ℝ} (hθ : 0 < θ) :
    latticeSechAlternatingMass θ / latticeSechMass θ ∈ Ioo 0 1 := by
  have h := latticeSechMass_strict_domain hθ
  have hA : 0 < latticeSechMass θ := h.1.trans h.2
  exact ⟨div_pos h.1 hA, (div_lt_one hA).mpr h.2⟩

/-- The actual hyperbolic modulus lies in the strict real elliptic domain.
Article: main_krylov, apC:lem:poisson. -/
theorem sechModulus_mem {θ : ℝ} (hθ : 0 < θ) : sechModulus θ ∈ Ioo 0 1 := by
  have h := sechMassRatio_mem hθ
  unfold sechModulus
  refine ⟨sqrt_pos.mpr (by nlinarith [h.1, h.2]), ?_⟩
  have hs := Real.sqrt_lt_sqrt (show 0 ≤ 1 -
    (latticeSechAlternatingMass θ / latticeSechMass θ) ^ 2 by nlinarith [h.1, h.2])
    (show 1 - (latticeSechAlternatingMass θ / latticeSechMass θ) ^ 2 < 1 by nlinarith [h.1])
  simpa only [Real.sqrt_one] using hs

/-- The true complementary modulus is the actual alternating/ordinary mass ratio.
Article: main_krylov, apC:lem:poisson, the complementary K dictionary. -/
theorem sechModulus_complement {θ : ℝ} (hθ : 0 < θ) :
    sqrt (1 - sechModulus θ ^ 2) = latticeSechAlternatingMass θ / latticeSechMass θ := by
  have h := sechMassRatio_mem hθ
  unfold sechModulus
  rw [Real.sq_sqrt (by nlinarith [h.1, h.2]), sub_sub_cancel, Real.sqrt_sq h.1.le]

/-- The actual positive-degree sech series vanishes as spacing tends to infinity.
Article: main_krylov, apC:lem:poisson, the normalization endpoint for the elliptic nome. -/
theorem sampledSech_tendsto_zero_atTop : Tendsto sampledSech atTop (𝓝 0) := by
  have he : Tendsto (fun θ : ℝ => 2 * exp (-θ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 2
  have h := sampledSech_exponential_asymptotic.mul he
  have ht : Tendsto (fun θ : ℝ => sampledSech θ / (2 * exp (-θ)) * (2 * exp (-θ))) atTop (𝓝 0) := by
    simpa only [one_mul] using! h
  simpa only [div_mul_cancel₀ _ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _))] using! ht

/-- The actual ordinary integer sech mass tends to one at infinite spacing.
Article: main_krylov, apC:lem:poisson, the true Gauss iteration endpoint. -/
theorem latticeSechMass_tendsto_one : Tendsto latticeSechMass atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add (sampledSech_tendsto_zero_atTop.const_mul 2)
  have ht : Tendsto (fun θ : ℝ => 1 + 2 * sampledSech θ) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using h
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
  exact (latticeSechMass_eq hθ).symm

/-- The genuine alternating mass has an explicit absolute tail bound.
Article: main_krylov, apC:lem:poisson, normalization at infinite spacing. -/
theorem latticeSechAlternatingMass_tail_bound {θ : ℝ} (hθ : 0 < θ) :
    |latticeSechAlternatingMass θ - 1| ≤ 2 * sampledSech θ := by
  let f : ℤ → ℝ := fun n => (-1 : ℝ) ^ n * sech ((n : ℝ) * θ)
  have hs : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := by
    exact (alternating_integer_summable _ (sech_integer_summable hθ)).comp_injective
      (fun n m h => by exact_mod_cast (add_right_cancel h : (n : ℤ) = (m : ℤ)))
  have he : ∀ n, f (-n) = f n := by
    intro n
    have hn : (-1 : ℝ) ^ (-n) = (-1 : ℝ) ^ n := by
      rw [zpow_neg, ← inv_zpow]
      simp
    simp only [f, hn, Int.cast_neg, neg_mul, sech_neg]
  have ht := tsum_even_integer_real f he hs
  have hn := norm_tsum_le_tsum_norm hs.norm
  have hnorm : (∑' n : ℕ, ‖f ((n : ℤ) + 1)‖) = sampledSech θ := by
    apply tsum_congr
    intro n
    simp only [f, norm_mul, Real.norm_eq_abs, abs_neg_one_zpow, one_mul,
      abs_of_pos (sech_pos _), Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [hnorm, Real.norm_eq_abs] at hn
  have hf0 : f 0 = 1 := by simp [f, sech]
  rw [hf0] at ht
  change latticeSechAlternatingMass θ = 1 + 2 * ∑' n : ℕ, f ((n : ℤ) + 1) at ht
  rw [ht, add_sub_cancel_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left hn (by norm_num)

/-- The actual alternating integer sech mass tends to one at infinite spacing.
Article: main_krylov, apC:lem:poisson, the true complementary Gauss coordinate endpoint. -/
theorem latticeSechAlternatingMass_tendsto_one : Tendsto latticeSechAlternatingMass atTop (𝓝 1) := by
  have he := sampledSech_tendsto_zero_atTop.const_mul 2
  have hl : Tendsto (fun θ : ℝ => 1 - 2 * sampledSech θ) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub he
  have hu : Tendsto (fun θ : ℝ => 1 + 2 * sampledSech θ) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add he
  apply hl.squeeze' hu
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
    have h := (abs_le.mp (latticeSechAlternatingMass_tail_bound hθ)).1
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
    have h := (abs_le.mp (latticeSechAlternatingMass_tail_bound hθ)).2
    linarith

end
end krylov.Design
