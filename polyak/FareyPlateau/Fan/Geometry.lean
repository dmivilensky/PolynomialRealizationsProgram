import polyak.Farey.Geometry.Fans

/-! The two signed fan families of an arbitrary reduced fraction. -/
noncomputable section
namespace polyak.FareyPlateau.Fan

structure Data where
  j : ℤ
  k : ℤ
  L : ℤ
  J : ℤ
  sign : ℤ
  period_ge : 3 ≤ k
  order_gt : k < L
  sign_unit : sign = 1 ∨ sign = -1
  incidence : k * J - j * L = -sign

namespace Data
variable (P : Data)

def center : ℝ := 2 * Real.pi * P.j / P.k
def near : ℝ := 2 * Real.pi * P.J / P.L
def far : ℝ := 2 * Real.pi * (P.J + P.sign) / P.L
def delta : ℝ := -2 * Real.pi * P.sign / (P.k * P.L)

theorem near_reduced : IsCoprime P.J P.L := by
  rcases P.sign_unit with h | h
  · exact ⟨-P.k, P.j, by linear_combination -P.incidence + h⟩
  · exact ⟨P.k, -P.j, by linear_combination P.incidence - h⟩

theorem near_displacement : P.near - P.center = P.delta := by
  have hk : (P.k : ℝ) ≠ 0 := by exact_mod_cast (show P.k ≠ 0 by have := P.period_ge; omega)
  have hL : (P.L : ℝ) ≠ 0 := by exact_mod_cast (show P.L ≠ 0 by have := P.period_ge; have := P.order_gt; omega)
  have he : (P.k : ℝ) * P.J - P.j * P.L = -(P.sign : ℝ) := by exact_mod_cast P.incidence
  unfold near center delta
  field_simp
  linear_combination he

theorem resonance : ((P.k : ℝ) - 1) * P.near + P.far = 2 * Real.pi * P.j := by
  have hL : (P.L : ℝ) ≠ 0 := by exact_mod_cast (show P.L ≠ 0 by have := P.period_ge; have := P.order_gt; omega)
  have he : (P.k : ℝ) * P.J - P.j * P.L = -(P.sign : ℝ) := by exact_mod_cast P.incidence
  unfold near far
  field_simp
  linear_combination he

theorem far_displacement : P.far = P.center - ((P.k : ℝ) - 1) * P.delta := by
  have he : (P.k : ℝ) * P.center = 2 * Real.pi * P.j := by
    unfold center
    have hk : (P.k : ℝ) ≠ 0 := by exact_mod_cast (show P.k ≠ 0 by have := P.period_ge; omega)
    field_simp
  have := P.resonance
  rw [show P.near = P.center + P.delta by linarith [P.near_displacement]] at this
  linarith

theorem barycenter : (((P.k : ℝ) - 1) * P.near + P.far) / P.k = P.center := by
  rw [P.resonance]
  rfl

theorem companion_gcd_dvd : (Int.gcd (P.J + P.sign) P.L : ℤ) ∣ P.k - 1 := by
  let g : ℤ := Int.gcd (P.J + P.sign) P.L
  have hJ : g ∣ P.J + P.sign := Int.gcd_dvd_left _ _
  have hL : g ∣ P.L := Int.gcd_dvd_right _ _
  have hcomb : g ∣ P.sign * (P.k - 1) := by
    convert dvd_sub (dvd_mul_of_dvd_right hJ P.k) (dvd_mul_of_dvd_right hL P.j) using 1
    linear_combination -P.incidence
  change g ∣ P.k - 1
  rcases P.sign_unit with h | h
  · simpa only [h, one_mul] using hcomb
  · simpa only [h, neg_one_mul, dvd_neg] using hcomb

end Data
end polyak.FareyPlateau.Fan
