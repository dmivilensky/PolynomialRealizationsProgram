import chebyshev1.Analysis.MidpointError
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Quantitative midpoint quadrature with an explicit second-derivative bound. -/
namespace chebyshev1.Analysis
noncomputable section
open Set Real MeasureTheory
open scoped BigOperators

theorem midpoint_integral_error_bound {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc a b, HasDerivAt f' (f'' t) t)
    (hbnd : ∀ t ∈ Icc a b, |f'' t| ≤ M) :
    |(b - a) * f ((a + b) / 2) - ∫ t in a..b, f t| ≤ M * (b - a) ^ 3 := by
  let m := (a + b) / 2
  have hm : m ∈ Icc a b := by dsimp [m]; constructor <;> linarith
  have hd (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : |x - y| ≤ b - a :=
    abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  have hfp (t : ℝ) (ht : t ∈ Icc a b) : |f' t - f' m| ≤ M * (b - a) := by
    have hh := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hf' u hu).hasDerivWithinAt)
      (fun u hu => by simpa only [Real.norm_eq_abs] using hbnd u hu) hm ht
    simp only [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hd t m ht hm) hM)
  let F : ℝ → ℝ := fun t => f t - f m - f' m * (t - m)
  have hFd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt F (f' t - f' m) t := by
    convert ((hf t ht).sub_const (f m)).sub
      (((hasDerivAt_id t).sub_const m).const_mul (f' m)) using 1
    · funext u; rfl
    · simp
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) : |F t| ≤ M * (b - a) ^ 2 := by
    have hh := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hFd u hu).hasDerivWithinAt)
      (fun u hu => by simpa only [Real.norm_eq_abs] using hfp u hu) hm ht
    have hz : F m = 0 := by simp [F]
    rw [hz, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hh
    calc
      _ ≤ M * (b - a) * |t - m| := hh
      _ ≤ M * (b - a) * (b - a) :=
        mul_le_mul_of_nonneg_left (hd t m ht hm) (mul_nonneg hM (sub_nonneg.mpr hab))
      _ = _ := by ring
  have hi : IntervalIntegrable f volume a b :=
    (show ContinuousOn f (Icc a b) from fun t ht => (hf t ht).continuousAt.continuousWithinAt)
      |>.intervalIntegrable_of_Icc hab
  have hl : IntervalIntegrable (fun t : ℝ => f' m * (t - m)) volume a b :=
    (by fun_prop : Continuous (fun t : ℝ => f' m * (t - m))).intervalIntegrable _ _
  have he : (∫ t in a..b, F t) = (∫ t in a..b, f t) - (b - a) * f m := by
    rw [show F = fun t => (f t - f m) - f' m * (t - m) from rfl,
      intervalIntegral.integral_sub (hi.sub intervalIntegrable_const) hl,
      intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (f := fun t : ℝ => t)
        (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const, intervalIntegral.integral_const]
    dsimp [m]
    ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (f := F) (a := a) (b := b)
    (fun t ht => by
      rw [uIoc_of_le hab] at ht
      simpa only [Real.norm_eq_abs] using hpoint t ⟨ht.1.le, ht.2⟩)
  rw [he, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)] at hb
  convert hb using 1
  ring

def midpointSum (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (1 / (N : ℝ)) * ∑ s ∈ Finset.range N, f (((s : ℝ) + 1 / 2) / N)

theorem midpointSum_error_bound {f f' f'' : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' t) t)
    (hbnd : ∀ t ∈ Icc (0 : ℝ) 1, |f'' t| ≤ M) (N : ℕ) (hN : 0 < N) :
    |midpointSum f N - ∫ t in (0 : ℝ)..1, f t| ≤ M / (N : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let a : ℕ → ℝ := fun s => (s : ℝ) / N
  have ha (s : ℕ) (hs : s ≤ N) : a s ∈ Icc (0 : ℝ) 1 := by
    dsimp [a]
    exact ⟨by positivity, (div_le_one hn).mpr (by exact_mod_cast hs)⟩
  have hab (s : ℕ) : a s ≤ a (s + 1) := by
    dsimp [a]
    gcongr
    exact_mod_cast (Nat.le_succ s)
  have hsub (s : ℕ) (hs : s < N) : Icc (a s) (a (s + 1)) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (ha s (by omega)).1 (ha (s + 1) (by omega)).2
  have hint (s : ℕ) (hs : s < N) : IntervalIntegrable f volume (a s) (a (s + 1)) :=
    (show ContinuousOn f (Icc (a s) (a (s + 1))) from
      fun t ht => (hf t (hsub s hs ht)).continuousAt.continuousWithinAt)
      |>.intervalIntegrable_of_Icc (hab s)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [a]
  have haN : a N = 1 := div_self hn.ne'
  rw [ha0, haN] at hsum
  have hlocal (s : ℕ) (hs : s < N) :
      |(1 / (N : ℝ)) * f (((s : ℝ) + 1 / 2) / N) -
          ∫ t in (a s)..(a (s + 1)), f t| ≤ M / (N : ℝ) ^ 3 := by
    have hh := midpoint_integral_error_bound (hab s) hM
      (fun t ht => hf t (hsub s hs ht))
      (fun t ht => hf' t (hsub s hs ht)) (fun t ht => hbnd t (hsub s hs ht))
    have hw : a (s + 1) - a s = 1 / (N : ℝ) := by dsimp [a]; push_cast; ring
    have hm : (a s + a (s + 1)) / 2 = ((s : ℝ) + 1 / 2) / N := by
      dsimp [a]; push_cast; ring
    rw [hw, hm] at hh
    convert hh using 1
    ring
  have he : midpointSum f N - (∫ t in (0 : ℝ)..1, f t) =
      ∑ s ∈ Finset.range N, ((1 / (N : ℝ)) * f (((s : ℝ) + 1 / 2) / N) -
        ∫ t in (a s)..(a (s + 1)), f t) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    rfl
  rw [he]
  calc
    _ ≤ ∑ s ∈ Finset.range N, |(1 / (N : ℝ)) * f (((s : ℝ) + 1 / 2) / N) -
        ∫ t in (a s)..(a (s + 1)), f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.range N, M / (N : ℝ) ^ 3 :=
      Finset.sum_le_sum (fun s hs => hlocal s (Finset.mem_range.mp hs))
    _ = M / (N : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hn.ne']

end
end chebyshev1.Analysis
