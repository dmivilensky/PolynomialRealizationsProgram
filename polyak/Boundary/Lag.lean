import polyak.Boundary.Chebyshev

/-!
Article: (LU), normalization of the positive-lag constraints.
Use: cancel the common scalar d=C sinh t with normalized nonnegative multipliers.
Proof: every U denominator is positive, including t=0, and the hyperbolic
Chebyshev identity is division-free.
-/

noncomputable section
open MeasureTheory
namespace polyak.Boundary
open Spectral

/-- Article: the strictly positive lag denominator Uₙ₋₁(G). -/
def lagDenominator (G : ℝ) (n : ℕ) : ℝ := chebU (n-1) G

/-- Article: normalized lower lag functional Lₙ. -/
def normalizedLower (u G : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  (g u c*(chebT n G-chebT n c)-lagB u n c)/lagDenominator G n

/-- Article: normalized upper lag functional Uₙ. -/
def normalizedUpper (u G : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  (g u c*(chebT n G-chebT n c)+lagB u n c)/lagDenominator G n

/-- Article: no normalized positive lag has a zero or negative denominator. -/
theorem lagDenominator_pos {G : ℝ} (hG : 1 ≤ G) (n : ℕ) (hn : 1 ≤ n) :
    0 < lagDenominator G n := by
  have h := degree_le_chebU (n-1) hG
  unfold lagDenominator
  have hn' : ((n-1 : ℕ) : ℝ)+1 = n := by exact_mod_cast Nat.sub_add_cancel hn
  rw [hn'] at h
  exact (Nat.cast_pos.mpr (by omega : 0 < n)).trans_le h

/-- Article: sinh(nt)=Uₙ₋₁(cosh t)sinh t, including t=0. -/
theorem lagDenominator_mul_sinh (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    lagDenominator (Real.cosh t) n*Real.sinh t = Real.sinh (n*t) := by
  have h := Polynomial.Chebyshev.U_real_cosh t ((n-1 : ℕ) : ℤ)
  have hn' : ((n-1 : ℕ) : ℝ)+1 = n := by exact_mod_cast Nat.sub_add_cancel hn
  simpa only [lagDenominator,chebU,Int.cast_natCast,hn'] using h

/-- Article: exact pointwise normalization of the lower lag, with its value constant. -/
theorem lower_normalization (u C t : ℝ) (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    lagA u t n c-lagB u n c+C*Real.sinh (n*t) =
      lagDenominator (Real.cosh t) n*(normalizedLower u (Real.cosh t) n c+C*Real.sinh t) := by
  have hD := (lagDenominator_pos (Real.one_le_cosh t) n hn).ne'
  unfold normalizedLower lagA lagD
  rw [chebT_cosh,← lagDenominator_mul_sinh t n hn]
  field_simp

/-- Article: exact pointwise normalization of the upper lag, with the opposite value sign. -/
theorem upper_normalization (u C t : ℝ) (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    lagA u t n c+lagB u n c-C*Real.sinh (n*t) =
      lagDenominator (Real.cosh t) n*(normalizedUpper u (Real.cosh t) n c-C*Real.sinh t) := by
  have hD := (lagDenominator_pos (Real.one_le_cosh t) n hn).ne'
  unfold normalizedUpper lagA lagD
  rw [chebT_cosh,← lagDenominator_mul_sinh t n hn]
  field_simp

/-- Article: normalized lower functional is continuous on the frequency interval. -/
@[fun_prop] theorem continuous_normalizedLower (u G : ℝ) (n : ℕ) :
    Continuous (normalizedLower u G n) := by
  unfold normalizedLower g lagB chebT chebU
  fun_prop

/-- Article: normalized upper functional is continuous on the frequency interval. -/
@[fun_prop] theorem continuous_normalizedUpper (u G : ℝ) (n : ℕ) :
    Continuous (normalizedUpper u G n) := by
  unfold normalizedUpper g lagB chebT chebU
  fun_prop

/-- Article: every feasible spectrum satisfies the normalized lower and upper inequalities.
Proof: integrate the exact normalization and divide by its positive denominator. -/
theorem _root_.polyak.Spectral.FeasibleU.normalized {u C t : ℝ} {ν : Spectrum} (h : FeasibleU u t ν C)
    (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ avg ν (fun c => normalizedLower u (Real.cosh t) n c)+C*Real.sinh t ∧
    0 ≤ avg ν (fun c => normalizedUpper u (Real.cosh t) n c)-C*Real.sinh t := by
  have hl := (h.2 n hn).1
  have hu := (h.2 n hn).2
  have hD := lagDenominator_pos (Real.one_le_cosh t) n hn
  have ha := integrable_continuous ν (show Continuous (fun c : Frequency => lagA u t n c) by
    unfold lagA lagD g chebT; fun_prop)
  have hb := integrable_continuous ν (show Continuous (fun c : Frequency => lagB u n c) by
    unfold lagB chebU; fun_prop)
  have hgL (c : Frequency) : normalizedLower u (Real.cosh t) n c =
      (lagA u t n c-lagB u n c)/lagDenominator (Real.cosh t) n := by
    simp [normalizedLower,lagA,lagD,chebT_cosh]
  have hgU (c : Frequency) : normalizedUpper u (Real.cosh t) n c =
      (lagA u t n c+lagB u n c)/lagDenominator (Real.cosh t) n := by
    simp [normalizedUpper,lagA,lagD,chebT_cosh]
  have haeq : (∫ c : Frequency, lagA u t n c ∂ν) = meanA ν u t n := (meanA_eq_integral ν u t n).symm
  have hbeq : (∫ c : Frequency, lagB u n c ∂ν) = meanB ν u n := (meanB_eq_integral ν u n).symm
  have hs := lagDenominator_mul_sinh t n hn
  constructor
  · simp_rw [hgL]
    unfold avg
    rw [integral_div,integral_sub ha hb]
    rw [haeq,hbeq]
    have he : (meanA ν u t n-meanB ν u n)/lagDenominator (Real.cosh t) n+C*Real.sinh t =
        (meanA ν u t n-meanB ν u n+C*Real.sinh (n*t))/lagDenominator (Real.cosh t) n := by
      rw [← hs]
      field_simp
    rw [he]
    exact div_nonneg hl hD.le
  · simp_rw [hgU]
    unfold avg
    rw [integral_div,integral_add ha hb]
    rw [haeq,hbeq]
    have he : (meanA ν u t n+meanB ν u n)/lagDenominator (Real.cosh t) n-C*Real.sinh t =
        (meanA ν u t n+meanB ν u n-C*Real.sinh (n*t))/lagDenominator (Real.cosh t) n := by
      rw [← hs]
      field_simp
    rw [he]
    exact div_nonneg hu hD.le

end polyak.Boundary
