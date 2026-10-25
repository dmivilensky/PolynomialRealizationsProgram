import polyak.Dynamics.Tuning
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Article: polyaksiopt, eq:quad and Appendix A eq:Abound.
Use: exact stability of the scalar characteristic roots, including zero momentum.
-/

namespace polyak.Dynamics
noncomputable section

/-- Article: eq:quad. Use: scalar Jury criterion for every complex characteristic root.
Proof: nonreal conjugate roots have squared modulus β; real roots outside
the unit interval contradict the two strict endpoint polynomial signs. -/
theorem quadratic_root_norm_lt_one {a β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (ha : |a| < 1+β) {z : ℂ} (hz : z^2 - (a : ℂ)*z + (β : ℂ) = 0) :
    ‖z‖ < 1 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, pow_two,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hre
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, pow_two,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
  have hapos : a < 1+β := (abs_lt.1 ha).2
  have haneg : -(1+β) < a := (abs_lt.1 ha).1
  have hnorm := Complex.sq_norm z
  rw [Complex.normSq_apply] at hnorm
  by_cases hi : z.im = 0
  · have hp : z.re^2-a*z.re+β = 0 := by simpa [hi, sq] using hre
    have hr1 : z.re < 1 := by
      by_contra hr
      have hr : 1 ≤ z.re := le_of_not_gt hr
      have := mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 (hβ1.le.trans hr))
      nlinarith
    have hr0 : -1 < z.re := by
      by_contra hr
      have hr : z.re ≤ -1 := le_of_not_gt hr
      have := mul_nonneg (show 0 ≤ -z.re-1 by linarith)
        (show 0 ≤ -z.re-β by linarith)
      nlinarith
    have hs : z.re^2 < 1 := by nlinarith
    have hn := norm_nonneg z
    simp only [hi, mul_zero, add_zero] at hnorm
    nlinarith

  · have hlin : 2*z.re-a = 0 := by
      apply (mul_eq_zero.mp (show z.im*(2*z.re-a)=0 by nlinarith)).resolve_left hi
    have hs : ‖z‖^2 = β := by nlinarith
    have hn := norm_nonneg z
    nlinarith

/-- Article: eq:quad. Use: failure at the positive endpoint produces a real bad root. -/
theorem exists_real_root_ge_one {a β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (ha : 1+β ≤ a) : ∃ r : ℝ, 1 ≤ r ∧ r^2-a*r+β=0 := by
  have hd : 0 ≤ a^2-4*β := by nlinarith [sq_nonneg (1-β)]
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg (a^2-4*β)
  refine ⟨(a+Real.sqrt (a^2-4*β))/2, ?_, ?_⟩
  · by_cases ha2 : 2 ≤ a
    · linarith
    · have ha2 : a < 2 := lt_of_not_ge ha2
      have hcomp : (2-a)^2 ≤ a^2-4*β := by nlinarith
      have hh : 2-a ≤ Real.sqrt (a^2-4*β) := by nlinarith
      linarith
  · nlinarith

/-- Article: eq:quad. Use: the strict unit-disk criterion is necessary as well as sufficient. -/
theorem quadratic_roots_stable_iff {a β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) :
    (∀ z : ℂ, z^2-(a : ℂ)*z+(β : ℂ)=0 → ‖z‖ < 1) ↔ |a| < 1+β := by
  constructor
  · intro h
    by_contra ha
    have ha' : 1+β ≤ |a| := le_of_not_gt ha
    rcases le_total 0 a with ha0 | ha0
    · rw [abs_of_nonneg ha0] at ha'
      obtain ⟨r, hr, hp⟩ := exists_real_root_ge_one hβ hβ1 ha'
      have hz : (r : ℂ)^2-(a : ℂ)*(r : ℂ)+(β : ℂ)=0 := by
        exact_mod_cast hp
      have hh := h (r : ℂ) hz
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hh
      linarith
    · rw [abs_of_nonpos ha0] at ha'
      obtain ⟨r, hr, hp⟩ := exists_real_root_ge_one hβ hβ1 ha'
      have hz : ((-r : ℝ) : ℂ)^2-(a : ℂ)*((-r : ℝ) : ℂ)+(β : ℂ)=0 := by
        have hh : (-r)^2-a*(-r)+β=0 := by nlinarith
        exact_mod_cast hh
      have hh := h ((-r : ℝ) : ℂ) hz
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by linarith)] at hh
      linarith
  · exact fun ha z hz => quadratic_root_norm_lt_one hβ hβ1 ha hz

/-- Article: eq:Abound. Use: every curvature in the interval is strictly stable. -/
theorem curvature_abs_lt {μ L α β lam : ℝ} (hμ : 0 < μ) (hα : 0 < α)
    (hlam : μ ≤ lam) (hlamL : lam ≤ L)
    (hquad : α*L < 2*(1+β)) : |1+β-α*lam| < 1+β := by
  rw [abs_lt]
  constructor
  · have := mul_le_mul_of_nonneg_left hlamL hα.le
    linarith
  · have hlampos := hμ.trans_le hlam
    have := mul_pos hα hlampos
    linarith

/-- Article: eq:quad. Use: the original characteristic root is inside the unit disk. -/
theorem heavyBall_root_norm_lt_one {μ L α β lam : ℝ} (hμ : 0 < μ) (hα : 0 < α)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hlam : μ ≤ lam) (hlamL : lam ≤ L)
    (hquad : α*L < 2*(1+β)) {z : ℂ}
    (hz : z^2 - ((1+β-α*lam : ℝ) : ℂ)*z + (β : ℂ) = 0) : ‖z‖ < 1 :=
  quadratic_root_norm_lt_one hβ hβ1
    (curvature_abs_lt hμ hα hlam hlamL hquad) hz

/-- Article: eq:quad. Use: the exact stability condition over the whole curvature interval. -/
theorem heavyBall_quadratic_stable_iff {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β < 1) :
    (∀ lam ∈ Set.Icc μ L, ∀ z : ℂ,
      z^2-((1+β-α*lam : ℝ) : ℂ)*z+(β : ℂ)=0 → ‖z‖ < 1) ↔
      0 < α*L ∧ α*L < 2*(1+β) := by
  constructor
  · intro h
    have hlast := (quadratic_roots_stable_iff hβ hβ1).mp
      (h L ⟨hL.le, le_rfl⟩)
    exact ⟨mul_pos hα (hμ.trans hL), by linarith [(abs_lt.mp hlast).1]⟩
  · intro h lam hlam z hz
    exact heavyBall_root_norm_lt_one hμ hα hβ hβ1 hlam.1 hlam.2 h.2 hz

/-- Article: Appendix A eq:Abound. Use: the normalized comparison recurrence is strictly bounded. -/
theorem normalizedA_abs_add_B_lt {μ L α β : ℝ} (hμ : 0 < μ)
    (hα : 0 < α) (hquad : α*L < 2*(1+β)) :
    |normalizedA μ L α β| + normalizedB μ L α < 1+β := by
  by_cases ha : 0 ≤ normalizedA μ L α β
  · rw [abs_of_nonneg ha]
    dsimp [normalizedA, normalizedB]
    nlinarith [mul_pos hα hμ]
  · rw [abs_of_neg (lt_of_not_ge ha)]
    dsimp [normalizedA, normalizedB]
    linarith

/-- Article: eq:Abound. Use: the comparison norm is the larger endpoint modulus. -/
theorem abs_add_eq_max_endpoints (a b : ℝ) (hb : 0 ≤ b) :
    |a|+b = max |a+b| |a-b| := by
  apply le_antisymm
  · by_cases ha : 0 ≤ a
    · calc
        |a|+b = |a+b| := by rw [abs_of_nonneg ha, abs_of_nonneg (add_nonneg ha hb)]
        _ ≤ _ := le_max_left _ _
    · have ha : a < 0 := lt_of_not_ge ha
      calc
        |a|+b = |a-b| := by rw [abs_of_neg ha, abs_of_neg (by linarith)]; ring
        _ ≤ _ := le_max_right _ _
  · apply max_le
    · exact (abs_add_le a b).trans (by rw [abs_of_nonneg hb])
    · exact (abs_sub a b).trans (by rw [abs_of_nonneg hb])

/-- Article: eq:Abound. Use: exact endpoint identity before applying the stability inequality. -/
theorem normalizedA_abs_add_B_eq {μ L α β : ℝ} (hμL : μ ≤ L) (hα : 0 ≤ α) :
    |normalizedA μ L α β|+normalizedB μ L α =
      max |1+β-α*μ| |1+β-α*L| := by
  have hB : 0 ≤ normalizedB μ L α := by
    unfold normalizedB
    exact div_nonneg (mul_nonneg hα (sub_nonneg.2 hμL)) (by norm_num)
  have hp : normalizedA μ L α β+normalizedB μ L α=1+β-α*μ := by
    unfold normalizedA normalizedB
    ring
  have hm : normalizedA μ L α β-normalizedB μ L α=1+β-α*L := by
    unfold normalizedA normalizedB
    ring
  rw [abs_add_eq_max_endpoints _ _ hB, hp, hm]

/-- Article: eq:polyak. Use: balanced roots have exactly the quadratic factor.
Proof: real roots force zero discriminant; nonreal roots are conjugates. -/
theorem quadratic_root_norm_sq {a β : ℝ} (hdisc : a^2 ≤ 4*β)
    {z : ℂ} (hz : z^2-(a : ℂ)*z+(β : ℂ)=0) : ‖z‖^2 = β := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hre
  simp only [pow_two, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
  have hn := Complex.sq_norm z
  rw [Complex.normSq_apply] at hn
  by_cases hi : z.im = 0
  · have hs := sq_nonneg (2*z.re-a)
    have hp : z.re^2-a*z.re+β=0 := by simpa [hi, sq] using hre
    have hlin : 2*z.re-a=0 := by nlinarith [sq_nonneg (2*z.re-a)]
    nlinarith
  · have hlin : 2*z.re-a=0 := by
      exact (mul_eq_zero.mp (show z.im*(2*z.re-a)=0 by nlinarith)).resolve_left hi
    have har : a = 2*z.re := by linarith
    rw [har] at hre
    nlinarith

/-- Article: eq:polyak. Use: every curvature has the same quadratic root modulus q. -/
theorem polyak_root_norm {μ L lam : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hlam : μ ≤ lam) (hlamL : lam ≤ L) {z : ℂ}
    (hz : z^2 - ((1+polyakBeta μ L-polyakAlpha μ L*lam : ℝ) : ℂ)*z +
      (polyakBeta μ L : ℂ) = 0) : ‖z‖ = polyakQ μ L := by
  have ha := polyakAlpha_pos hμ hL
  have hq := polyakQ_pos hμ hL
  have hA := polyak_normalizedA hμ hL
  have hB := polyak_normalizedB hμ hL
  dsimp [normalizedA] at hA
  dsimp [normalizedB] at hB
  have hu := mul_le_mul_of_nonneg_left hlam ha.le
  have hl := mul_le_mul_of_nonneg_left hlamL ha.le
  have habs : |1+polyakBeta μ L-polyakAlpha μ L*lam| ≤ 2*polyakQ μ L := by
    rw [abs_le]
    constructor <;> nlinarith
  have hd : (1+polyakBeta μ L-polyakAlpha μ L*lam)^2 ≤ 4*polyakBeta μ L := by
    have := sq_le_sq₀ (abs_nonneg (1+polyakBeta μ L-polyakAlpha μ L*lam))
      (by positivity : 0 ≤ 2*polyakQ μ L)
    have hs := this.2 habs
    rw [sq_abs] at hs
    dsimp [polyakBeta] at hs ⊢
    nlinarith
  have hn := quadratic_root_norm_sq hd hz
  dsimp [polyakBeta] at hn
  have hn0 := norm_nonneg z
  nlinarith

end
end polyak.Dynamics
