import polyak.Dynamics.QuadraticRate
import Mathlib.Tactic

/-!
Article: §2 and Appendix A, characteristic polynomials and scalar quadratic facts.
Use: actual complex roots, including the negative determinant caused by extrapolation.
-/

noncomputable section
namespace nesterov.Quadratic

def queryPolynomial (τ : ℝ) (z : ℂ) : ℂ := (1 + τ : ℝ) * z - (τ : ℂ)

def characteristic (β τ h lam : ℝ) (z : ℂ) : ℂ :=
  (z - 1) * (z - (β : ℂ)) + (h * lam : ℝ) * queryPolynomial τ z

def S (β τ h lam : ℝ) : ℝ := 1 + β - h * lam * (1 + τ)
def Q (β τ h lam : ℝ) : ℝ := β - h * lam * τ

theorem characteristic_eq (β τ h lam : ℝ) (z : ℂ) :
    characteristic β τ h lam z = z ^ 2 - (S β τ h lam : ℂ) * z + (Q β τ h lam : ℂ) := by
  simp only [characteristic, queryPolynomial, S, Q, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one]
  ring

@[simp] theorem characteristic_one (β τ h lam : ℝ) :
    characteristic β τ h lam 1 = (h * lam : ℝ) := by
  simp [characteristic, queryPolynomial]

@[simp] theorem characteristic_neg_one (β τ h lam : ℝ) :
    characteristic β τ h lam (-1) = (2 * (1 + β) - h * lam * (1 + 2 * τ) : ℝ) := by
  simp only [characteristic, queryPolynomial, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_one]
  ring

/-- Scalar Jury sufficiency with a determinant of either sign. -/
theorem root_norm_lt_one {a q : ℝ} (hq : q < 1) (ha : |a| < 1 + q)
    {z : ℂ} (hz : z ^ 2 - (a : ℂ) * z + (q : ℂ) = 0) : ‖z‖ < 1 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, pow_two,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hre
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, pow_two,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
  have hapos := (abs_lt.mp ha).2
  have haneg := (abs_lt.mp ha).1
  have hnorm := Complex.sq_norm z
  rw [Complex.normSq_apply] at hnorm
  by_cases hi : z.im = 0
  · have hp : z.re ^ 2 - a * z.re + q = 0 := by simpa [hi, sq] using hre
    have hr1 : z.re < 1 := by
      by_contra hr
      have hr : 1 ≤ z.re := le_of_not_gt hr
      have := mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ z.re - q by linarith)
      nlinarith
    have hr0 : -1 < z.re := by
      by_contra hr
      have hr : z.re ≤ -1 := le_of_not_gt hr
      have := mul_nonneg (show 0 ≤ -z.re - 1 by linarith)
        (show 0 ≤ -z.re - q by linarith)
      nlinarith
    have hs : z.re ^ 2 < 1 := by nlinarith
    simp only [hi, mul_zero, add_zero] at hnorm
    nlinarith [norm_nonneg z]
  · have hlin : 2 * z.re - a = 0 :=
      (mul_eq_zero.mp (show z.im * (2 * z.re - a) = 0 by nlinarith)).resolve_left hi
    have hs : ‖z‖ ^ 2 = q := by nlinarith
    nlinarith [norm_nonneg z]

/-- A pair of roots is provided directly by Vieta, without a discriminant split. -/
theorem root_pair (a q : ℝ) : ∃ z w : ℂ,
    z ^ 2 - (a : ℂ) * z + (q : ℂ) = 0 ∧
    w ^ 2 - (a : ℂ) * w + (q : ℂ) = 0 ∧
    z + w = (a : ℂ) ∧ z * w = (q : ℂ) := by
  obtain ⟨z, hz⟩ := polyak.Dynamics.exists_complex_quadratic_root a q
  refine ⟨z, (a : ℂ) - z, hz, ?_, by ring, ?_⟩
  · linear_combination hz
  · linear_combination -hz

/-- Every conjugate-real root pair inside the radius supplies the endpoint
lower bound and the determinant upper bound used in the price theorem. -/
theorem endpoint_bounds {a q ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hroots : ∀ z : ℂ, z ^ 2 - (a : ℂ) * z + (q : ℂ) = 0 → ‖z‖ ≤ ρ) :
    (1 - ρ) ^ 2 ≤ 1 - a + q ∧ (1 - ρ) ^ 2 ≤ 1 + a + q ∧ q ≤ ρ ^ 2 := by
  obtain ⟨z, w, hz, hw, hsum, hprod⟩ := root_pair a q
  have hzρ := hroots z hz
  have hwρ := hroots w hw
  have hsumre := congrArg Complex.re hsum
  have hsumim := congrArg Complex.im hsum
  have hprodre := congrArg Complex.re hprod
  have hprodim := congrArg Complex.im hprod
  simp only [Complex.add_re, Complex.ofReal_re] at hsumre
  simp only [Complex.add_im, Complex.ofReal_im] at hsumim
  simp only [Complex.mul_re, Complex.ofReal_re] at hprodre
  simp only [Complex.mul_im, Complex.ofReal_im] at hprodim
  have hzre : |z.re| ≤ ρ := (Complex.abs_re_le_norm z).trans hzρ
  have hwre : |w.re| ≤ ρ := (Complex.abs_re_le_norm w).trans hwρ
  have hq : q ≤ ρ ^ 2 := by
    have hp := norm_mul_le z w
    rw [hprod, Complex.norm_real, Real.norm_eq_abs] at hp
    exact (le_abs_self q).trans (hp.trans (by nlinarith [norm_nonneg z, norm_nonneg w]))
  refine ⟨?_, ?_, hq⟩
  · by_cases hi : z.im = 0
    · have hwi : w.im = 0 := by linarith
      have hp := mul_nonneg (show 0 ≤ ρ - z.re from sub_nonneg.mpr (le_abs_self _ |>.trans hzre))
        (show 0 ≤ ρ - w.re from sub_nonneg.mpr (le_abs_self _ |>.trans hwre))
      rw [hi, hwi] at hprodre
      have hpos := mul_nonneg (show 0 ≤ 1 - ρ by linarith)
        (show 0 ≤ 2 * ρ - (z.re + w.re) by linarith [(abs_le.mp hzre).2, (abs_le.mp hwre).2])
      nlinarith
    · have hreal : z.re = w.re := by
        have hwi : w.im = -z.im := by linarith
        rw [hwi] at hprodim
        have he : z.im * (z.re - w.re) = 0 := by nlinarith only [hprodim]
        exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hi)
      have hn := Complex.sq_norm z
      rw [Complex.normSq_apply] at hn
      have hp := sq_nonneg (z.re - ρ)
      have hp2 := mul_nonneg (show 0 ≤ ρ - z.re by linarith [(abs_le.mp hzre).2])
        (show 0 ≤ 2 - ρ - z.re by linarith [(abs_le.mp hzre).2])
      have hwi : w.im = -z.im := by linarith
      rw [hwi, ← hreal] at hprodre
      nlinarith [sq_nonneg z.im]
  · by_cases hi : z.im = 0
    · have hwi : w.im = 0 := by linarith
      have hp := mul_nonneg (show 0 ≤ ρ + z.re by linarith [(abs_le.mp hzre).1])
        (show 0 ≤ ρ + w.re by linarith [(abs_le.mp hwre).1])
      rw [hi, hwi] at hprodre
      have hpos := mul_nonneg (show 0 ≤ 1 - ρ by linarith)
        (show 0 ≤ 2 * ρ + (z.re + w.re) by linarith [(abs_le.mp hzre).1, (abs_le.mp hwre).1])
      nlinarith
    · have hreal : z.re = w.re := by
        have hwi : w.im = -z.im := by linarith
        rw [hwi] at hprodim
        have he : z.im * (z.re - w.re) = 0 := by nlinarith only [hprodim]
        exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hi)
      have hn := Complex.sq_norm z
      rw [Complex.normSq_apply] at hn
      have hp := sq_nonneg (z.re + ρ)
      have hp2 := mul_nonneg (show 0 ≤ ρ + z.re by linarith [(abs_le.mp hzre).1])
        (show 0 ≤ 2 - ρ + z.re by linarith [(abs_le.mp hzre).1])
      have hwi : w.im = -z.im := by linarith
      rw [hwi, ← hreal] at hprodre
      nlinarith [sq_nonneg z.im]

/-- All roots of a monic quadratic belong to its Vieta pair. -/
theorem root_eq_or_eq {a q : ℝ} {z w r : ℂ}
    (hsum : z + w = (a : ℂ)) (hprod : z * w = (q : ℂ))
    (hr : r ^ 2 - (a : ℂ) * r + (q : ℂ) = 0) : r = z ∨ r = w := by
  have he : (r - z) * (r - w) = 0 := by
    rw [← hsum, ← hprod] at hr
    linear_combination hr
  exact (mul_eq_zero.mp he).imp sub_eq_zero.mp sub_eq_zero.mp

/-- An elementary Cauchy bound valid for either sign of the coefficients. -/
theorem root_norm_bound {a q : ℝ} {z : ℂ}
    (hz : z ^ 2 - (a : ℂ) * z + (q : ℂ) = 0) : ‖z‖ ≤ 1 + |a| + |q| := by
  have he : z ^ 2 = (a : ℂ) * z - (q : ℂ) := by linear_combination hz
  have hn := norm_sub_le ((a : ℂ) * z) (q : ℂ)
  rw [← he, norm_pow, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at hn
  by_contra h
  have hgt : 1 + |a| + |q| < ‖z‖ := lt_of_not_ge h
  have hgt1 : 1 < ‖z‖ := by linarith [abs_nonneg a, abs_nonneg q]
  have hp := mul_nonneg (abs_nonneg q) (show 0 ≤ ‖z‖ - 1 by linarith)
  have hp2 := mul_pos (show 0 < ‖z‖ - (1 + |a| + |q|) by linarith)
    (show 0 < ‖z‖ by linarith)
  nlinarith

/-- Exact scalar Schur criterion, with no sign restriction on the determinant. -/
theorem roots_stable_iff {a q : ℝ} :
    (∀ z : ℂ, z ^ 2 - (a : ℂ) * z + (q : ℂ) = 0 → ‖z‖ < 1) ↔
      q < 1 ∧ |a| < 1 + q := by
  constructor
  · intro h
    obtain ⟨z, w, hz, hw, hs, hp⟩ := root_pair a q
    let ρ := max ‖z‖ ‖w‖
    have hρ : 0 ≤ ρ := (norm_nonneg z).trans (le_max_left _ _)
    have hρ1 : ρ < 1 := max_lt (h z hz) (h w hw)
    have hb : ∀ r : ℂ, r ^ 2 - (a : ℂ) * r + (q : ℂ) = 0 → ‖r‖ ≤ ρ := by
      intro r hr
      rcases root_eq_or_eq hs hp hr with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _
    obtain ⟨hpos, hneg, hq⟩ := endpoint_bounds hρ hρ1 hb
    have hd : 0 < (1 - ρ) ^ 2 := sq_pos_of_pos (by linarith)
    refine ⟨by nlinarith, ?_⟩
    rw [abs_lt]
    constructor <;> linarith
  · rintro ⟨hq, ha⟩ z hz
    exact root_norm_lt_one hq ha hz

/-- Saturating the positive endpoint bound forces a double root at the radius. -/
theorem endpoint_equality {a q ρ : ℝ} (_hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hroots : ∀ z : ℂ, z ^ 2 - (a : ℂ) * z + (q : ℂ) = 0 → ‖z‖ ≤ ρ)
    (heq : 1 - a + q = (1 - ρ) ^ 2) : a = 2 * ρ ∧ q = ρ ^ 2 := by
  obtain ⟨z, w, hz, hw, hsum, hprod⟩ := root_pair a q
  have hzre : |z.re| ≤ ρ := (Complex.abs_re_le_norm z).trans (hroots z hz)
  have hwre : |w.re| ≤ ρ := (Complex.abs_re_le_norm w).trans (hroots w hw)
  have hsumre := congrArg Complex.re hsum
  have hsumim := congrArg Complex.im hsum
  have hprodre := congrArg Complex.re hprod
  have hprodim := congrArg Complex.im hprod
  simp only [Complex.add_re, Complex.ofReal_re] at hsumre
  simp only [Complex.add_im, Complex.ofReal_im] at hsumim
  simp only [Complex.mul_re, Complex.ofReal_re] at hprodre
  simp only [Complex.mul_im, Complex.ofReal_im] at hprodim
  by_cases hi : z.im = 0
  · have hwi : w.im = 0 := by linarith
    rw [hi, hwi] at hprodre
    have hza := (abs_le.mp hzre).2
    have hwa := (abs_le.mp hwre).2
    have hp := mul_nonneg (show 0 ≤ 1 - z.re by linarith)
      (show 0 ≤ ρ - w.re by linarith)
    have hzv : z.re = ρ := by nlinarith
    have hwv : w.re = ρ := by
      rw [hzv] at hprodre hsumre
      nlinarith
    constructor <;> nlinarith
  · have hwi : w.im = -z.im := by linarith
    rw [hwi] at hprodim hprodre
    have hreal : z.re = w.re := by
      have he : z.im * (z.re - w.re) = 0 := by nlinarith only [hprodim]
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hi)
    rw [← hreal] at hprodre hsumre
    have hza := (abs_le.mp hzre).2
    have hp := mul_nonneg (show 0 ≤ ρ - z.re by linarith)
      (show 0 ≤ 2 - ρ - z.re by linarith)
    have him0 : z.im = 0 := by nlinarith [sq_nonneg z.im]
    exact False.elim (hi him0)

end nesterov.Quadratic
