import krylov.Design.IntegerLatticeSums

/-!
Article: main_krylov, apC:lem:poisson, the hyperbolic AGM duplication proof.
Use: prove actual alternating secant correlations vanish at every nonzero
integer translate. Even translates telescope after genuine even/odd pairing;
odd translates cancel under reflection. All actual sums are absolutely convergent.
Source: elementary hyperbolic addition and unconditional-series rearrangement.
-/

namespace krylov.Design
noncomputable section
open Real Filter jacobi.Young

/-- The exact paired hyperbolic product is a difference of tanh increments.
Article: main_krylov, apC:lem:poisson, even-shift alternating cancellation. -/
theorem sech_pair_telescope (x y c : ℝ) :
    sinh y * (sech x * sech (y - x) - sech (x + c) * sech (y - x - c)) =
      (tanh x - tanh (x + c)) - (tanh (x - y) - tanh (x + c - y)) := by
  have h1 := tanh_sub_eq_sech_product x (x - y)
  have h2 := tanh_sub_eq_sech_product (x + c) (x + c - y)
  rw [show x - (x - y) = y by ring] at h1
  rw [show x + c - (x + c - y) = y by ring] at h2
  rw [show y - x - c = -(x + c - y) by ring, sech_neg,
    show y - x = -(x - y) by ring, sech_neg]
  nlinarith [h1, h2]

/-- The actual even/odd tanh difference on the integer lattice.
Article: main_krylov, apC:lem:poisson, a summable primitive for even-shift cancellation. -/
def pairedTanh (θ : ℝ) (n : ℤ) : ℝ :=
  tanh ((2 * (n : ℝ)) * θ) - tanh ((2 * (n : ℝ) + 1) * θ)

/-- The actual paired tanh primitive is genuinely absolutely summable.
Article: main_krylov, apC:lem:poisson. -/
theorem pairedTanh_summable {θ : ℝ} (hθ : 0 < θ) : Summable (pairedTanh θ) := by
  have hs := (sech_lattice_correlation hθ (k := 1) (by decide)).summable
  have he := hs.comp_injective (show Function.Injective (fun n : ℤ => 2 * n) from by
    intro n m h
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h)
  convert! he.mul_left (-sinh θ) using 1
  funext n
  rw [pairedTanh, tanh_sub_eq_sech_product,
    show 2 * (n : ℝ) * θ - (2 * (n : ℝ) + 1) * θ = -θ by ring, Real.sinh_neg]
  simp only [Function.comp_def, Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_one]
  ring

/-- Every even nonzero actual alternating correlation vanishes.
Article: main_krylov, apC:lem:poisson, the nontrivial even part of AGM duplication. -/
theorem alternating_sech_convolution_even {θ : ℝ} (hθ : 0 < θ) {j : ℤ} (hj : j ≠ 0) :
    (∑' n : ℤ, (-1 : ℝ) ^ n *
      (sech ((n : ℝ) * θ) * sech (((2 * j - n : ℤ) : ℝ) * θ))) = 0 := by
  let f : ℤ → ℝ := fun n => (-1 : ℝ) ^ n *
    (sech ((n : ℝ) * θ) * sech (((2 * j - n : ℤ) : ℝ) * θ))
  have hs : Summable f := alternating_sech_product_summable hθ (2 * j)
  have hp := tsum_integer_even_odd f hs
  have hpair (n : ℤ) : sinh (2 * (j : ℝ) * θ) * (f (2 * n) + f (2 * n + 1)) =
      pairedTanh θ n - pairedTanh θ (n - j) := by
    have he : (-1 : ℝ) ^ (2 * n) = 1 := Even.neg_one_zpow ⟨n, by ring⟩
    have ho : (-1 : ℝ) ^ (2 * n + 1) = -1 := Odd.neg_one_zpow ⟨n, by ring⟩
    simp only [f, he, ho, one_mul, neg_one_mul, Int.cast_sub, Int.cast_mul, Int.cast_add,
      Int.cast_ofNat, Int.cast_one, pairedTanh]
    have hp := sech_pair_telescope (2 * (n : ℝ) * θ) (2 * (j : ℝ) * θ) θ
    convert! hp using 1 <;> congr 2 <;> ring_nf
  have hshift : Summable (fun n : ℤ => pairedTanh θ (n - j)) := by
    simpa only [Function.comp_def] using!
      (pairedTanh_summable hθ).comp_injective (Equiv.subRight j).injective
  have ht := (pairedTanh_summable hθ).tsum_sub hshift
  have hz : (∑' n : ℤ, (pairedTanh θ n - pairedTanh θ (n - j))) = 0 := by
    rw [ht]
    have he : (∑' n : ℤ, pairedTanh θ (n - j)) = ∑' n : ℤ, pairedTanh θ n := by
      have he := (Equiv.subRight j).tsum_eq (pairedTanh θ)
      change (∑' n : ℤ, pairedTanh θ (n - j)) = ∑' n : ℤ, pairedTanh θ n at he
      exact he
    rw [he, sub_self]
  have heq : sinh (2 * (j : ℝ) * θ) * ∑' n : ℤ, f n = 0 := by
    rw [hp, ← tsum_mul_left, tsum_congr hpair, hz]
  have hne : sinh (2 * (j : ℝ) * θ) ≠ 0 := by
    apply Real.sinh_ne_zero.mpr
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr hj)) hθ.ne'
  exact (mul_eq_zero.mp heq).resolve_left hne

/-- Every odd actual alternating correlation vanishes by genuine reflected-series cancellation.
Article: main_krylov, apC:lem:poisson, the odd part of AGM duplication. -/
theorem alternating_sech_convolution_odd {θ : ℝ} {k : ℤ} (hk : Odd k) :
    (∑' n : ℤ, (-1 : ℝ) ^ n *
      (sech ((n : ℝ) * θ) * sech (((k - n : ℤ) : ℝ) * θ))) = 0 := by
  let f : ℤ → ℝ := fun n => (-1 : ℝ) ^ n *
    (sech ((n : ℝ) * θ) * sech (((k - n : ℤ) : ℝ) * θ))
  have hsym (n : ℤ) : f (k - n) = -f n := by
    have hkpow : (-1 : ℝ) ^ k = -1 := hk.neg_one_zpow
    have hn : (-1 : ℝ) ^ (-n) = (-1 : ℝ) ^ n := by
      rw [zpow_neg, ← inv_zpow]
      simp
    dsimp [f]
    rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), hkpow, hn]
    rw [show k - (k + -n) = n by ring]
    ring
  have he := (Equiv.subLeft k).tsum_eq f
  change (∑' n : ℤ, f (k - n)) = ∑' n : ℤ, f n at he
  have hn : (∑' n : ℤ, f (k - n)) = -(∑' n : ℤ, f n) := by
    simp_rw [hsym]
    rw [tsum_neg]
  rw [hn] at he
  linarith

/-- Every actual alternating secant correlation vanishes at every nonzero integer translate.
Article: main_krylov, apC:lem:poisson, the complete alternating convolution identity. -/
theorem alternating_sech_convolution {θ : ℝ} (hθ : 0 < θ) {k : ℤ} (hk : k ≠ 0) :
    (∑' n : ℤ, (-1 : ℝ) ^ n *
      (sech ((n : ℝ) * θ) * sech (((k - n : ℤ) : ℝ) * θ))) = 0 := by
  rcases Int.even_or_odd k with he | ho
  · obtain ⟨j, hj⟩ := he
    have hk2 : k = 2 * j := by linarith
    rw [hk2]
    exact alternating_sech_convolution_even hθ (by intro hz; simp [hz] at hk2; exact hk hk2)
  · exact alternating_sech_convolution_odd ho

end
end krylov.Design
