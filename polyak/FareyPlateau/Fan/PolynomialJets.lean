import polyak.FareyPlateau.Fan.Polynomial

noncomputable section
namespace polyak.FareyPlateau.Fan
open Filter
open scoped Topology

def polynomialFirst (k : ℕ) (θ : ℝ) : ℝ :=
  ((k : ℝ) - 1) * Real.sin (θ - Real.pi / k) +
    ((k : ℝ) - 1) * Real.sin (((k : ℝ) - 1) * θ + Real.pi / k)

theorem hasDerivAt_polynomial (k : ℕ) (θ : ℝ) :
    HasDerivAt (polynomial k) (polynomialFirst k θ) θ := by
  have h₁ := ((hasDerivAt_id θ).sub_const (Real.pi / k)).cos.const_mul ((k : ℝ) - 1)
  have h₂ := (((hasDerivAt_id θ).const_mul ((k : ℝ) - 1)).add_const (Real.pi / k)).cos
  convert ((hasDerivAt_const θ ((k : ℝ) * Real.cos (Real.pi / k))).sub h₁).sub h₂ using 1
  · rfl
  · simp only [polynomialFirst, id_eq]
    ring

theorem hasDerivAt_polynomialFirst (k : ℕ) (θ : ℝ) :
    HasDerivAt (polynomialFirst k)
      (((k : ℝ) - 1) * Real.cos (θ - Real.pi / k) +
        ((k : ℝ) - 1)^2 * Real.cos (((k : ℝ) - 1) * θ + Real.pi / k)) θ := by
  have h₁ := ((hasDerivAt_id θ).sub_const (Real.pi / k)).sin.const_mul ((k : ℝ) - 1)
  have h₂ := ((((hasDerivAt_id θ).const_mul ((k : ℝ) - 1)).add_const (Real.pi / k)).sin).const_mul ((k : ℝ) - 1)
  convert h₁.add h₂ using 1
  · rfl
  · simp only [id_eq]
    ring

theorem polynomial_second (k : ℕ) (θ : ℝ) :
    deriv^[2] (polynomial k) θ = ((k : ℝ) - 1) * Real.cos (θ - Real.pi / k) +
      ((k : ℝ) - 1)^2 * Real.cos (((k : ℝ) - 1) * θ + Real.pi / k) := by
  have he : deriv (polynomial k) = polynomialFirst k := by
    funext x
    exact (hasDerivAt_polynomial k x).deriv
  change deriv (deriv (polynomial k)) θ = _
  rw [he]
  exact (hasDerivAt_polynomialFirst k θ).deriv

theorem polynomial_second_zero (k : ℕ) :
    deriv^[2] (polynomial k) 0 = (k : ℝ) * ((k : ℝ) - 1) * Real.cos (Real.pi / k) := by
  rw [polynomial_second]
  simp only [zero_sub, Real.cos_neg, mul_zero, zero_add]
  ring

theorem polynomial_second_other {k : ℕ} (hk : 3 ≤ k) :
    deriv^[2] (polynomial k) (2 * Real.pi / k) =
      (k : ℝ) * ((k : ℝ) - 1) * Real.cos (Real.pi / k) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have h₁ : 2 * Real.pi / k - Real.pi / k = Real.pi / k := by ring
  have h₂ : ((k : ℝ) - 1) * (2 * Real.pi / k) + Real.pi / k =
      2 * Real.pi - Real.pi / k := by field_simp; ring
  rw [polynomial_second, h₁, h₂, Real.cos_two_pi_sub]
  ring

theorem polynomial_second_roots_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < deriv^[2] (polynomial k) 0 ∧ 0 < deriv^[2] (polynomial k) (2 * Real.pi / k) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 0 < Real.cos (Real.pi / k) := Real.cos_pos_of_mem_Ioo
    ⟨by have h : 0 < Real.pi / k := by positivity
        linarith [Real.pi_pos],
      (div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos])⟩
  rw [polynomial_second_zero, polynomial_second_other hk]
  have hp : 0 < (k : ℝ) * ((k : ℝ) - 1) * Real.cos (Real.pi / k) :=
    mul_pos (mul_pos (by linarith) (by linarith)) hc
  exact ⟨hp, hp⟩

end polyak.FareyPlateau.Fan
