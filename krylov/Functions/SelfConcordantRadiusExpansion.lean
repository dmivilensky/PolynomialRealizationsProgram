import krylov.Functions.SelfConcordantSublevel

/-!
Article: main_krylov, apG:sc(ii), the cubic remainder in the sublevel radius.
Use: justify the printed expansion rho(t)=t+(2/3)t^2+O(t^3) from the actual
inverse-potential equation, including the singular inverse derivative at zero.
Source: the elementary logarithmic potential comparison in Appendix G.
-/

namespace krylov.Functions
noncomputable section
open Set

/-- Ordered genuine scalar derivatives compare actual increments.
Article: main_krylov, apG:sc(ii), logarithmic Taylor remainder.
Proof: the actual difference has nonnegative derivative and is monotone. -/
theorem derivative_increment_comparison (f f' g g' : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt g (g' t) t)
    (hb : ∀ t ∈ Icc (0 : ℝ) r, f' t ≤ g' t) : f r - f 0 ≤ g r - g 0 := by
  have hd t (ht : t ∈ Icc (0 : ℝ) r) :
      HasDerivAt (fun t : ℝ => g t - f t) (g' t - f' t) t := (hg t ht).sub (hf t ht)
  have hm : MonotoneOn (fun t : ℝ => g t - f t) (Icc 0 r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => sub_nonneg.mpr (hb t (interior_subset ht)))
  have h := hm (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  linarith

/-- The lower potential has an explicit signed fourth-order Taylor remainder.
Article: main_krylov, apG:sc(ii).
Proof: its derivative lies between those of the cubic Taylor polynomial and
that polynomial plus t^4/4 on the nonnegative half-line. -/
theorem scOmega_cubic_remainder {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ scOmega r - (r ^ 2 / 2 - r ^ 3 / 3) ∧
      scOmega r - (r ^ 2 / 2 - r ^ 3 / 3) ≤ r ^ 4 / 4 := by
  let q := fun t : ℝ => t ^ 2 / 2 - t ^ 3 / 3
  let Q := fun t : ℝ => q t + t ^ 4 / 4
  have hq t : HasDerivAt q (t - t ^ 2) t := by
    convert! (((hasDerivAt_id t).pow 2).div_const 2).sub
      (((hasDerivAt_id t).pow 3).div_const 3) using 1
    all_goals dsimp
    all_goals ring
  have hQ t : HasDerivAt Q (t - t ^ 2 + t ^ 3) t := by
    convert! (hq t).add (((hasDerivAt_id t).pow 4).div_const 4) using 1
    all_goals dsimp
    all_goals ring
  have hlo := derivative_increment_comparison q (fun t => t - t ^ 2) scOmega
    (fun t => t / (1 + t)) hr (fun t _ => hq t)
    (fun t ht => scOmega_hasDerivAt (by linarith [ht.1])) (fun t ht => by
      apply (le_div_iff₀ (by linarith [ht.1] : 0 < 1 + t)).mpr
      nlinarith [pow_nonneg ht.1 3])
  have hhi := derivative_increment_comparison scOmega (fun t => t / (1 + t)) Q
    (fun t => t - t ^ 2 + t ^ 3) hr
    (fun t ht => scOmega_hasDerivAt (by linarith [ht.1])) (fun t _ => hQ t) (fun t ht => by
      apply (div_le_iff₀ (by linarith [ht.1] : 0 < 1 + t)).mpr
      nlinarith [pow_nonneg ht.1 4])
  simp only [q, Q, scOmega, add_zero, Real.log_one, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_div, sub_self, sub_zero,
    ] at hlo hhi ⊢
  constructor <;> linarith

/-- The upper potential has a signed fourth-order remainder on [0,1/2].
Article: main_krylov, apG:sc(ii).
Proof: the residual derivative t^3/(1-t) lies between zero and 2t^3. -/
theorem scOmegaStar_cubic_remainder {r : ℝ} (hr : 0 ≤ r) (hr₂ : r ≤ 1 / 2) :
    0 ≤ scOmegaStar r - (r ^ 2 / 2 + r ^ 3 / 3) ∧
      scOmegaStar r - (r ^ 2 / 2 + r ^ 3 / 3) ≤ r ^ 4 / 2 := by
  let q := fun t : ℝ => t ^ 2 / 2 + t ^ 3 / 3
  let Q := fun t : ℝ => q t + t ^ 4 / 2
  have hq t : HasDerivAt q (t + t ^ 2) t := by
    convert! (((hasDerivAt_id t).pow 2).div_const 2).add
      (((hasDerivAt_id t).pow 3).div_const 3) using 1
    all_goals dsimp
    all_goals ring
  have hQ t : HasDerivAt Q (t + t ^ 2 + 2 * t ^ 3) t := by
    convert! (hq t).add (((hasDerivAt_id t).pow 4).div_const 2) using 1
    all_goals dsimp
    all_goals ring
  have hlo := derivative_increment_comparison q (fun t => t + t ^ 2) scOmegaStar
    (fun t => t / (1 - t)) hr (fun t _ => hq t)
    (fun t ht => scOmegaStar_hasDerivAt (by linarith [ht.2])) (fun t ht => by
      apply (le_div_iff₀ (by linarith [ht.2] : 0 < 1 - t)).mpr
      nlinarith [pow_nonneg ht.1 3])
  have hhi := derivative_increment_comparison scOmegaStar (fun t => t / (1 - t)) Q
    (fun t => t + t ^ 2 + 2 * t ^ 3) hr
    (fun t ht => scOmegaStar_hasDerivAt (by linarith [ht.2])) (fun t _ => hQ t) (fun t ht => by
      apply (div_le_iff₀ (by linarith [ht.2] : 0 < 1 - t)).mpr
      nlinarith [mul_nonneg (pow_nonneg ht.1 3) (show 0 ≤ 1 - 2 * t by linarith [ht.2])])
  simp only [q, Q, scOmegaStar, sub_zero, Real.log_one, neg_zero,
    zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 4 ≠ 0), zero_div, sub_self, sub_zero, add_zero] at hlo hhi ⊢
  constructor <;> linarith

/-- The actual inverse-potential radius has the printed quadratic expansion,
with an explicit cubic remainder valid uniformly down to radius zero.
Article: main_krylov, apG:sc(ii), rho(t)=t+(2/3)t^2+O(t^3).
Proof: the exact potential equation and signed fourth-order remainders first
give t<=rho<=t+4t^2; substitution back into that same equation controls the
cubic error. This avoids differentiating the singular inverse at zero. -/
theorem scSublevelRadius_cubic_expansion {t : ℝ} (ht : 0 ≤ t) (ht₄ : t ≤ 1 / 4) :
    |scSublevelRadius t (by linarith) - t - (2 / 3 : ℝ) * t ^ 2| ≤ 32 * t ^ 3 := by
  let ρ := scSublevelRadius t (by linarith : t < 1)
  have hspec := scSublevelRadius_spec t (by linarith : t < 1)
  have hρ : 0 ≤ ρ := hspec.1
  have he : scOmega ρ = scOmegaStar t := hspec.2
  have hρt : ρ ≤ 2 * t := scSublevelRadius_le_double ht (by linarith)
  have hρ₂ : ρ ≤ 1 / 2 := by linarith
  have hlo := scOmega_cubic_remainder hρ
  have hhi := scOmegaStar_cubic_remainder ht (by linarith : t ≤ 1 / 2)
  have hρ₄ : ρ ^ 4 ≤ ρ ^ 3 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hρ₂ (pow_nonneg hρ 3)]
  have htr : t ≤ ρ := by
    have hsq : t ^ 2 ≤ ρ ^ 2 := by
      nlinarith only [hlo.2, hhi.1, he, hρ₄, pow_nonneg hρ 3, pow_nonneg ht 3]
    exact (sq_le_sq₀ ht hρ).mp hsq
  have hρ₃t : ρ ^ 3 ≤ 8 * t ^ 3 := by
    have h : ρ ^ 3 ≤ (2 * t) ^ 3 := by gcongr
    nlinarith
  have ht₄₃ : t ^ 4 ≤ t ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right (show t ≤ 1 by linarith) (pow_nonneg ht 3)]
  have hsqhi : ρ ^ 2 - t ^ 2 ≤ 7 * t ^ 3 := by
    nlinarith only [hlo.1, hhi.2, he, hρ₃t, ht₄₃]
  by_cases ht₀ : t = 0
  · have hρ₀ : ρ = 0 := by nlinarith
    change |ρ - t - (2 / 3 : ℝ) * t ^ 2| ≤ 32 * t ^ 3
    simp [ht₀, hρ₀]
  · have htpos : 0 < t := ht.lt_of_ne' ht₀
    have hΔ : ρ - t ≤ 4 * t ^ 2 := by
      apply (mul_le_mul_iff_right₀ htpos).mp
      nlinarith only [hsqhi, sq_nonneg (ρ - t), pow_nonneg ht 3]
    have hρsq : ρ ^ 2 ≤ 4 * t ^ 2 := by
      have h : ρ ^ 2 ≤ (2 * t) ^ 2 := by gcongr
      nlinarith only [h]
    have hρmul : ρ * t ≤ 2 * t ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hρt ht]
    have hquad : ρ ^ 2 + ρ * t + t ^ 2 ≤ 7 * t ^ 2 := by linarith only [hρsq, hρmul]
    have hΔ₀ : 0 ≤ ρ - t := sub_nonneg.mpr htr
    have hΔsq : (ρ - t) ^ 2 ≤ 16 * t ^ 4 := by
      have h := mul_self_le_mul_self hΔ₀ hΔ
      nlinarith only [h]
    have hcube : ρ ^ 3 - t ^ 3 ≤ 28 * t ^ 4 := by
      have h := mul_le_mul hΔ hquad (by positivity : 0 ≤ ρ ^ 2 + ρ * t + t ^ 2)
        (by positivity : 0 ≤ 4 * t ^ 2)
      nlinarith only [h]
    have hρfour : ρ ^ 4 ≤ 16 * t ^ 4 := by
      have h : ρ ^ 4 ≤ (2 * t) ^ 4 := by gcongr
      nlinarith only [h]
    have hehi : 2 * t * (ρ - t - (2 / 3 : ℝ) * t ^ 2) ≤ 20 * t ^ 4 := by
      nlinarith only [hlo.1, hhi.2, he, hcube, sq_nonneg (ρ - t)]
    have helo : -24 * t ^ 4 ≤ 2 * t * (ρ - t - (2 / 3 : ℝ) * t ^ 2) := by
      have hcubelo : t ^ 3 ≤ ρ ^ 3 := by gcongr
      nlinarith only [hlo.2, hhi.1, he, hcubelo, hΔsq, hρfour]
    change |ρ - t - (2 / 3 : ℝ) * t ^ 2| ≤ 32 * t ^ 3
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ htpos).mp
      nlinarith only [helo, pow_nonneg ht 4]
    · apply (mul_le_mul_iff_right₀ htpos).mp
      nlinarith only [hehi, pow_nonneg ht 4]

end
end krylov.Functions
