import krylov.Information.CentredRFC

/-!
Article: main_krylov, s4:cor-Q, genuine own-normalized instance comparison.
Use: Exact scalar algebra for the three actual instance-comparison losses.
Source: actual common-centre execution and robust radius, genuine compact
CG reference regularity and elementary real order and positive-ratio algebra.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator

/-- A robust two-scenario square-root radius yields the explicit linear inverse-model factor.
Use: Use the actual information radius with a true bound on its operator norm.
Article: main_krylov, s4:cor-Q, original instance factor and normalization.
Proof: The square root of 1+k^2 is at most 1+k for k nonnegative; multiply the genuine radius inequality by its strictly positive denominator. -/
theorem robust_radius_factor {x y k a : ℝ} (hy : 0≤y) (hk : 0≤k) (hka : k≤a)
    (h : x/Real.sqrt (1+k^2)≤y) : x≤(1+a)*y := by
  -- Bound the genuine positive square-root denominator before multiplying the radius.
  have hs : 0<Real.sqrt (1+k^2) := Real.sqrt_pos.mpr (by positivity)
  have hb : Real.sqrt (1+k^2)≤1+k := Real.sqrt_le_iff.mpr ⟨by linarith,by nlinarith⟩
  calc
    x ≤ y*Real.sqrt (1+k^2) := (div_le_iff₀ hs).mp h
    _ ≤ y*(1+a) := mul_le_mul_of_nonneg_left (hb.trans (by linarith)) hy
    _ = (1+a)*y := mul_comm _ _

/-- The reciprocal of three positive first-order loss factors is at least one minus their total losses.
Use: Preserve the exact printed additive first-order instance-comparison constant.
Article: main_krylov, s4:cor-Q, original instance factor and normalization.
Proof: Multiply successively by each positive factor; each cross-product error has nonpositive sign, leaving a bound of one. -/
theorem reciprocal_product_lower {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    1-(a+b+c)≤((1+a)*(1+b)*(1+c))⁻¹ := by
  -- All three genuine denominator factors are strictly positive.
  have hp : 0<(1+a)*(1+b)*(1+c) := by positivity
  rw [← one_div]
  apply (le_div_iff₀ hp).mpr
  calc
    _ = ((1-(a+b+c))*(1+a))*(1+b)*(1+c) := by ring
    _ ≤ (1-(b+c))*(1+b)*(1+c) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith : 0≤1+c)
      apply mul_le_mul_of_nonneg_right _ (by linarith : 0≤1+b)
      nlinarith [mul_nonneg ha (show 0≤a+b+c by positivity)]
    _ ≤ (1-c)*(1+c) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith : 0≤1+c)
      nlinarith [mul_nonneg hb (show 0≤b+c by positivity)]
    _ ≤ 1 := by nlinarith [sq_nonneg c]

/-- A true fixed-metric robust radius and actual metric and reference-error comparisons imply the original own-normalized instance bound.
Use: Separate the elementary real ratio algebra from actual executed residuals and their positive normalizations.
Article: main_krylov, s4:cor-Q, original instance factor and normalization.
Proof: Bound each true residual by the maximum of the actual two risks. The resulting product loss has the proved reciprocal lower bound, giving one minus the sum of the three original first-order losses. -/
theorem instance_ratio_factor {f s t u φ ψ a b c : ℝ}
    (hf : 0≤f) (hs : 0≤s) (hφ : 0<φ) (hψ : 0<ψ)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hr : f≤(1+a)*max s t) (hm : t≤(1+b)*u)
    (herror : ψ≤φ*(1+c)) :
    (1-(a+b+c))*(f/φ)≤max (s/φ) (u/ψ) := by
  -- The same maximum of the two genuine own-normalized risks controls both residuals.
  let R := max (s/φ) (u/ψ)
  have hR : 0≤R := (div_nonneg hs hφ.le).trans (le_max_left _ _)
  have hφs : s≤φ*R := by
    simpa only [mul_comm] using (div_le_iff₀ hφ).mp (le_max_left (s/φ) (u/ψ))
  have hψt : t≤(1+b)*φ*(1+c)*R := by
    calc
      _ ≤ (1+b)*u := hm
      _ ≤ (1+b)*(R*ψ) := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ hψ).mp (le_max_right (s/φ) (u/ψ))) (by positivity : 0≤1+b)
      _ = (1+b)*ψ*R := by ring
      _ ≤ (1+b)*(φ*(1+c))*R := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left herror (by positivity : 0≤1+b)) hR
      _ = _ := by ring
  have hmax : max s t≤φ*((1+b)*(1+c))*R := by
    apply max_le
    · have hp : 1≤(1+b)*(1+c) := by nlinarith [mul_nonneg hb hc]
      exact hφs.trans (by nlinarith [mul_nonneg (mul_nonneg hφ.le hR) (sub_nonneg.mpr hp)])
    · nlinarith [hψt]
  have hfr : f/φ≤((1+a)*(1+b)*(1+c))*R := by
    apply (div_le_iff₀ hφ).mpr
    exact hr.trans ((mul_le_mul_of_nonneg_left hmax (by positivity : 0≤1+a)).trans_eq (by ring))
  have hdiv : (f/φ)/((1+a)*(1+b)*(1+c))≤R :=
    (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hfr)
  calc
    _ ≤ ((1+a)*(1+b)*(1+c))⁻¹*(f/φ) :=
      mul_le_mul_of_nonneg_right (reciprocal_product_lower ha hb hc) (div_nonneg hf hφ.le)
    _ = (f/φ)/((1+a)*(1+b)*(1+c)) := by rw [div_eq_mul_inv]; exact mul_comm _ _
    _ ≤ R := hdiv

end
end krylov.Information
