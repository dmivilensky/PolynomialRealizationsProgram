import krylov.Tensor.FlatDyadicLayers
import krylov.Tensor.CubicBanach
import Mathlib.Algebra.Field.GeomSum

/-!
Article: main_krylov, apG:flat, summation of the genuine dyadic tensor cost.
Use: sum the actual level-pair Cauchy bounds into the sharp order n log n.
The finite geometric sum is evaluated explicitly; no nuclear-cost estimate
or dyadic decomposition is postulated.
Source: the actual dyadic decomposition and the standard geometric-series identity.
-/

namespace krylov.Tensor
noncomputable section
open Finset krylov.Functions
open scoped BigOperators InnerProductSpace
variable {N L : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine rank-one decomposition cost at two actual dyadic levels.
Article: main_krylov, apG:flat. -/
def flatDyadicLayerCost (e : Fin N → E) (k l : Fin L) (u : E) : ℝ :=
  ∑ r : Fin (2 ^ (L - (k.val + 1))), ∑ s : Fin (2 ^ (L - (l.val + 1))),
    ‖flagComponent e (dyadicHalf N k.val r.val true ∩ dyadicHalf N l.val s.val true) u‖ *
      ‖dyadicLeftVector e (⟨k, r⟩ : DyadicPrefixIndex L)‖ * ‖dyadicLeftVector e (⟨l, s⟩ : DyadicPrefixIndex L)‖

/-- The actual dyadic layer cost is symmetric in its two levels.
Article: main_krylov, apG:flat, the two level orders. -/
theorem flatDyadicLayerCost_symm (e : Fin N → E) (k l : Fin L) (u : E) :
    flatDyadicLayerCost e k l u = flatDyadicLayerCost e l k u := by
  unfold flatDyadicLayerCost
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro r _
  rw [Finset.inter_comm]
  ring

/-- The genuine dyadic block square-root lengths are exactly powers of sqrt two.
Article: main_krylov, apG:flat, geometric level weights. -/
theorem sqrt_nat_two_pow (k : ℕ) : Real.sqrt (2 ^ k : ℕ) = (Real.sqrt 2) ^ k := by
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k), ih, pow_succ]

/-- Every ordered actual dyadic layer pair has the genuine geometric cost bound printed in the article.
Article: main_krylov, apG:flat, 2^((L+k')/2).
Proof: use the proved actual pairwise layer Cauchy estimate and enlarge the
true number of fine blocks by at most the harmless factor sqrt two. -/
theorem flatDyadicLayerCost_ordered_le (e : Fin N → E) (he : Orthonormal ℝ e)
    (k l : Fin L) (hkl : k.val ≤ l.val) (u : E) :
    flatDyadicLayerCost e k l u ≤ (Real.sqrt 2) ^ (L + l.val) * ‖u‖ := by
  have hb := flatDyadic_layer_cost_le e he k l hkl u
  simp_rw [sqrt_nat_two_pow] at hb
  have hq : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hpow := pow_le_pow_right₀ hq (by omega : L - (k.val + 1) ≤ L - k.val)
  apply hb.trans
  calc
    _ ≤ (Real.sqrt 2) ^ k.val * (Real.sqrt 2) ^ l.val * (Real.sqrt 2) ^ (L - k.val) * ‖u‖ := by gcongr
    _ = _ := by
      rw [← pow_add, ← pow_add]
      congr 2
      omega

/-- A common bound for either order of the two actual dyadic levels.
Article: main_krylov, apG:flat, summation over both level orders. -/
theorem flatDyadicLayerCost_le (e : Fin N → E) (he : Orthonormal ℝ e) (k l : Fin L) (u : E) :
    flatDyadicLayerCost e k l u ≤ (Real.sqrt 2) ^ L *
      ((Real.sqrt 2) ^ k.val + (Real.sqrt 2) ^ l.val) * ‖u‖ := by
  have hq : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  rcases le_total k.val l.val with hkl | hlk
  · exact (flatDyadicLayerCost_ordered_le e he k l hkl u).trans (by
      rw [pow_add]
      gcongr
      exact le_add_of_nonneg_left (pow_nonneg hq _))
  · rw [flatDyadicLayerCost_symm]
    exact (flatDyadicLayerCost_ordered_le e he l k hlk u).trans (by
      rw [pow_add]
      gcongr
      exact le_add_of_nonneg_right (pow_nonneg hq _))

/-- The full genuine dyadic decomposition has the article's actual O(2^L L) rank-one cost.
Article: main_krylov, apG:flat, ‖X₁‖_*≤2L2^L/(sqrt2−1).
Proof: the real level-pair bounds give twice L copies of the actual finite
geometric series. Evaluate that series and identify (sqrt2)^(2L)=2^L. -/
theorem flatDyadic_total_cost_le (e : Fin N → E) (he : Orthonormal ℝ e) (u : E) :
    ∑ k : Fin L, ∑ l : Fin L, flatDyadicLayerCost e k l u ≤
      (2 * (L : ℝ) * (2 : ℝ) ^ L / (Real.sqrt 2 - 1)) * ‖u‖ := by
  let q := Real.sqrt 2
  have hq : 1 < q := by dsimp only [q]; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hsum : (∑ j : Fin L, q ^ j.val) ≤ q ^ L / (q - 1) := by
    apply (le_div_iff₀ (by linarith : 0 < q - 1)).mpr
    rw [Fin.sum_univ_eq_sum_range]
    have heq := geom_sum_mul q L
    linarith
  calc
    _ ≤ ∑ k : Fin L, ∑ l : Fin L, q ^ L * (q ^ k.val + q ^ l.val) * ‖u‖ :=
      sum_le_sum (fun k _ => sum_le_sum (fun l _ => flatDyadicLayerCost_le e he k l u))
    _ = 2 * (L : ℝ) * q ^ L * (∑ j : Fin L, q ^ j.val) * ‖u‖ := by
      simp_rw [mul_add, add_mul, sum_add_distrib]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ 2 * (L : ℝ) * q ^ L * (q ^ L / (q - 1)) * ‖u‖ := by gcongr
    _ = _ := by
      have hsq : q ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      calc
        _ = (2 * (L : ℝ) / (q - 1)) * (q ^ L * q ^ L) * ‖u‖ := by ring
        _ = _ := by
          rw [show q ^ L * q ^ L = (2 : ℝ) ^ L by rw [← mul_pow, ← pow_two, hsq]]
          dsimp only [q]
          ring

end
end krylov.Tensor
