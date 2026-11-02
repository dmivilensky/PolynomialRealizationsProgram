import krylov.Design.HyperbolicProducts
import krylov.Design.PoissonSechSquared

/-!
Article: main_krylov, apC:lem:poisson, the second genuine elliptic duplication product.
Use: evaluate the actual square of the alternating integer sech mass by its
true convolution and the previously proved tanh telescoping formula.
Source: actual absolutely convergent hyperbolic convolutions and integer symmetry.
-/

namespace krylov.Design
noncomputable section
open Real Filter jacobi.Young

/-- Exact zero-plus-pairs decomposition of a genuine even summable integer series.
Article: main_krylov, apC:lem:poisson. -/
theorem tsum_even_integer_real (f : ℤ → ℝ) (he : ∀ n, f (-n) = f n)
    (hs : Summable (fun n : ℕ => f ((n : ℤ) + 1))) :
    (∑' n : ℤ, f n) = f 0 + 2 * ∑' n : ℕ, f ((n : ℤ) + 1) := by
  have hn : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by simpa only [he] using hs
  rw [tsum_of_add_one_of_neg_add_one (f := f) hs hn]
  simp only [he]
  ring

/-- The true integer sech mass is exactly the source zero mode plus symmetric positive samples.
Article: main_krylov, apC:lem:poisson. -/
theorem latticeSechMass_eq {θ : ℝ} (hθ : 0 < θ) :
    latticeSechMass θ = 1 + 2 * sampledSech θ := by
  have hs : Summable (fun n : ℕ => sech ((((n : ℤ) + 1 : ℤ) : ℝ) * θ)) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using sampledSech_summable hθ
  have h := tsum_even_integer_real (fun n : ℤ => sech ((n : ℝ) * θ))
    (fun n => by simp only [Int.cast_neg, neg_mul, sech_neg]) hs
  simpa only [latticeSechMass, sampledSech, Int.cast_zero, zero_mul, sech, Real.cosh_zero,
    inv_one, Int.cast_add, Int.cast_natCast, Int.cast_one] using! h

/-- The true integer squared-sech mass is the source zero mode plus its symmetric samples.
Article: main_krylov, apC:lem:poisson. -/
theorem latticeSechSquaredMass_eq {θ : ℝ} (hθ : 0 < θ) :
    latticeSechSquaredMass θ = 1 + 2 * sampledSechSquared θ := by
  have hs : Summable (fun n : ℕ => sech ((((n : ℤ) + 1 : ℤ) : ℝ) * θ) ^ 2) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using sampledSechSquared_summable hθ
  have h := tsum_even_integer_real (fun n : ℤ => sech ((n : ℝ) * θ) ^ 2)
    (fun n => by simp only [Int.cast_neg, neg_mul, sech_neg]) hs
  simpa only [latticeSechSquaredMass, sampledSechSquared, Int.cast_zero, zero_mul, sech, Real.cosh_zero,
    inv_one, one_pow, Int.cast_add, Int.cast_natCast, Int.cast_one] using! h

/-- The actual positive alternating weighted-cosecant series.
Article: main_krylov, apC:lem:poisson, the intermediate duplication Lambert series. -/
def sampledAlternatingWeightedCsch (θ : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ ((n : ℤ) + 1) * (((n : ℝ) + 1) / sinh (((n : ℝ) + 1) * θ))

/-- The actual alternating weighted-cosecant series is absolutely summable.
Article: main_krylov, apC:lem:poisson. -/
theorem sampledAlternatingWeightedCsch_summable {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℕ => (-1 : ℝ) ^ ((n : ℤ) + 1) *
      (((n : ℝ) + 1) / sinh (((n : ℝ) + 1) * θ))) := by
  apply (sampledWeightedCsch_summable hθ).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_neg_one_zpow, one_mul,
    abs_of_pos (div_pos (by positivity) (Real.sinh_pos_iff.mpr (by positivity)))]

/-- The exact actual lattice convolution at every nonzero integer translate.
Article: main_krylov, apC:lem:poisson. -/
theorem sech_lattice_convolution {θ : ℝ} (hθ : 0 < θ) {k : ℤ} (hk : k ≠ 0) :
    HasSum (fun n : ℤ => sech ((n : ℝ) * θ) * sech (((k - n : ℤ) : ℝ) * θ))
      (2 * (k : ℝ) / sinh ((k : ℝ) * θ)) := by
  have hs := (Equiv.neg ℤ).hasSum_iff.mpr (sech_lattice_correlation hθ hk)
  simpa only [Function.comp_def, Equiv.neg_apply, Int.cast_neg, neg_mul, sech_neg,
    neg_add_eq_sub] using! hs

/-- The actual alternating-mass square has the exact weighted-cosecant correction.
Article: main_krylov, apC:lem:poisson, the remaining arithmetic ingredient of AGM duplication. -/
theorem latticeSechAlternatingMass_square {θ : ℝ} (hθ : 0 < θ) :
    latticeSechAlternatingMass θ ^ 2 = latticeSechSquaredMass θ + 4 * sampledAlternatingWeightedCsch θ := by
  let f : ℤ → ℝ := fun n => (-1 : ℝ) ^ n * sech ((n : ℝ) * θ)
  let F : ℤ → ℝ := fun k => ∑' n : ℤ, f n * f (k - n)
  have hf : Summable f := alternating_integer_summable _ (sech_integer_summable hθ)
  have hconv : latticeSechAlternatingMass θ ^ 2 = ∑' k : ℤ, F k := by
    rw [pow_two]
    exact tsum_integer_convolution f f hf hf
  have hnonzero (k : ℤ) (hk : k ≠ 0) :
      F k = (-1 : ℝ) ^ k * (2 * (k : ℝ) / sinh ((k : ℝ) * θ)) := by
    have hterm (n : ℤ) : f n * f (k - n) =
        (-1 : ℝ) ^ k * (sech ((n : ℝ) * θ) * sech (((k - n : ℤ) : ℝ) * θ)) := by
      have hpow : (-1 : ℝ) ^ n * (-1 : ℝ) ^ (k - n) = (-1 : ℝ) ^ k := by
        rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), add_sub_cancel]
      dsimp [f]
      calc
        _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ (k - n)) *
          (sech ((n : ℝ) * θ) * sech (((k - n : ℤ) : ℝ) * θ)) := by ring
        _ = _ := by rw [hpow]
    dsimp [F]
    simp_rw [hterm]
    rw [tsum_mul_left, (sech_lattice_convolution hθ hk).tsum_eq]
  have hzero : F 0 = latticeSechSquaredMass θ := by
    dsimp [F, f, latticeSechSquaredMass]
    apply tsum_congr
    intro n
    have hn : (-1 : ℝ) ^ n * (-1 : ℝ) ^ (-n) = 1 := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
    simp only [zero_sub, Int.cast_neg, neg_mul, sech_neg]
    calc
      _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ (-n)) * sech ((n : ℝ) * θ) ^ 2 := by ring
      _ = _ := by rw [hn, one_mul]
  have heven : ∀ k, F (-k) = F k := by
    intro k
    by_cases hk : k = 0
    · simp only [hk, neg_zero]
    rw [hnonzero (-k) (neg_ne_zero.mpr hk), hnonzero k hk]
    have hn : (-1 : ℝ) ^ (-k) = (-1 : ℝ) ^ k := by
      rw [zpow_neg, ← inv_zpow]
      simp
    rw [hn]
    simp [Int.cast_neg, neg_mul, Real.sinh_neg, div_neg]
    ring
  have hpos : (fun n : ℕ => F ((n : ℤ) + 1)) =
      (fun n : ℕ => 2 * ((-1 : ℝ) ^ ((n : ℤ) + 1) *
        (((n : ℝ) + 1) / sinh (((n : ℝ) + 1) * θ)))) := by
    funext n
    rw [hnonzero _ (by omega)]
    push_cast
    ring
  have hsPos : Summable (fun n : ℕ => F ((n : ℤ) + 1)) := by
    rw [hpos]
    exact (sampledAlternatingWeightedCsch_summable hθ).mul_left 2
  rw [hconv, tsum_even_integer_real F heven hsPos, hzero, hpos, tsum_mul_left]
  dsimp [sampledAlternatingWeightedCsch]
  ring

end
end krylov.Design
