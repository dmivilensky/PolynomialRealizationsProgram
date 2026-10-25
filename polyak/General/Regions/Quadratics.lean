import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Article: Corollary C and Appendix D, explicit quadratic sign criteria.
Use: exact tests on the full closed frequency interval, including linear and
zero-discriminant cases. No sampling of the frequency interval is involved.
-/

namespace polyak.General.Regions
noncomputable section

/-- The scalar quadratic used for all three explicit region tests. -/
def quadratic (a b d c : ℝ) : ℝ := a*c^2+b*c+d

/-- A positive quadratic is positive everywhere when its discriminant is negative. -/
theorem quadratic_pos_of_discriminant {a b d : ℝ} (ha : 0<a)
    (hdisc : b^2-4*a*d<0) (c : ℝ) : 0<quadratic a b d c := by
  have hid : 4*a*quadratic a b d c=(2*a*c+b)^2-(b^2-4*a*d) := by
    dsimp [quadratic]; ring
  have : 0<4*a*quadratic a b d c := by nlinarith [sq_nonneg (2*a*c+b)]
  exact pos_of_mul_pos_right this (by positivity)

/-- Nonpositive discriminant includes the tangency case. -/
theorem quadratic_nonneg_of_discriminant {a b d : ℝ} (ha : 0<a)
    (hdisc : b^2-4*a*d≤0) (c : ℝ) : 0≤quadratic a b d c := by
  have hid : 4*a*quadratic a b d c=(2*a*c+b)^2-(b^2-4*a*d) := by
    dsimp [quadratic]; ring
  have : 0≤4*a*quadratic a b d c := by nlinarith [sq_nonneg (2*a*c+b)]
  exact nonneg_of_mul_nonneg_right this (by positivity)

/-- A vertex to the left puts the minimum at the left endpoint. -/
theorem quadratic_left_min {a b d c : ℝ} (ha : 0≤a) (hb : 2*a≤b)
    (hc : -1≤c) : quadratic a b d (-1)≤quadratic a b d c := by
  have h1 : 0≤a*(c+1)^2 := mul_nonneg ha (sq_nonneg _)
  have h2 : 0≤(b-2*a)*(c+1) := mul_nonneg (sub_nonneg.mpr hb) (by linarith)
  dsimp [quadratic] at *
  nlinarith

/-- A vertex to the right puts the minimum at the right endpoint. -/
theorem quadratic_right_min {a b d c : ℝ} (ha : 0≤a) (hb : b≤ -2*a)
    (hc : c≤1) : quadratic a b d 1≤quadratic a b d c := by
  have h1 : 0≤a*(c-1)^2 := mul_nonneg ha (sq_nonneg _)
  have h2 : 0≤(-b-2*a)*(1-c) := mul_nonneg (by linarith) (by linarith)
  dsimp [quadratic] at *
  nlinarith

/-- Exact strict sign criterion for a convex quadratic on [-1,1]. -/
theorem convex_quadratic_pos_iff {a b d : ℝ} (ha : 0<a) :
    (∀ c∈Set.Icc (-1:ℝ) 1, 0<quadratic a b d c) ↔
      0<quadratic a b d (-1) ∧ 0<quadratic a b d 1 ∧
      (b≤ -2*a ∨ 2*a≤b ∨ b^2-4*a*d<0) := by
  constructor
  · intro h
    refine ⟨h (-1) (by norm_num),h 1 (by norm_num),?_⟩
    by_cases hright : b≤ -2*a
    · exact Or.inl hright
    by_cases hleft : 2*a≤b
    · exact Or.inr (Or.inl hleft)
    right; right
    have hv : -b/(2*a)∈Set.Icc (-1:ℝ) 1 := by
      constructor
      · apply (le_div_iff₀ (by positivity : 0<2*a)).mpr
        linarith
      · apply (div_le_iff₀ (by positivity : 0<2*a)).mpr
        linarith
    have hp := h _ hv
    have he : 4*a*quadratic a b d (-b/(2*a))=4*a*d-b^2 := by
      dsimp [quadratic]
      field_simp
      ring
    have : 0<4*a*quadratic a b d (-b/(2*a)) := mul_pos (by positivity) hp
    linarith
  · rintro ⟨hl,hr,hv⟩ c hc
    rcases hv with hb|hb|hd
    · exact lt_of_lt_of_le hr (quadratic_right_min ha.le hb hc.2)
    · exact lt_of_lt_of_le hl (quadratic_left_min ha.le hb hc.1)
    · exact quadratic_pos_of_discriminant ha hd c

/-- Exact weak sign criterion; unlike strict positivity its discriminant test is weak. -/
theorem convex_quadratic_nonneg_iff {a b d : ℝ} (ha : 0<a) :
    (∀ c∈Set.Icc (-1:ℝ) 1, 0≤quadratic a b d c) ↔
      0≤quadratic a b d (-1) ∧ 0≤quadratic a b d 1 ∧
      (b≤ -2*a ∨ 2*a≤b ∨ b^2-4*a*d≤0) := by
  constructor
  · intro h
    refine ⟨h (-1) (by norm_num),h 1 (by norm_num),?_⟩
    by_cases hright : b≤ -2*a
    · exact Or.inl hright
    by_cases hleft : 2*a≤b
    · exact Or.inr (Or.inl hleft)
    right; right
    have hv : -b/(2*a)∈Set.Icc (-1:ℝ) 1 := by
      constructor
      · apply (le_div_iff₀ (by positivity : 0<2*a)).mpr
        linarith
      · apply (div_le_iff₀ (by positivity : 0<2*a)).mpr
        linarith
    have hp := h _ hv
    have he : 4*a*quadratic a b d (-b/(2*a))=4*a*d-b^2 := by
      dsimp [quadratic]
      field_simp
      ring
    have : 0≤4*a*quadratic a b d (-b/(2*a)) := mul_nonneg (by positivity) hp
    linarith
  · rintro ⟨hl,hr,hv⟩ c hc
    rcases hv with hb|hb|hd
    · exact hr.trans (quadratic_right_min ha.le hb hc.2)
    · exact hl.trans (quadratic_left_min ha.le hb hc.1)
    · exact quadratic_nonneg_of_discriminant ha hd c

/-- Concave and linear quadratics are nonnegative iff both endpoint values are. -/
theorem concave_quadratic_nonneg_iff {a b d : ℝ} (ha : a≤0) :
    (∀ c∈Set.Icc (-1:ℝ) 1, 0≤quadratic a b d c) ↔
      0≤quadratic a b d (-1) ∧ 0≤quadratic a b d 1 := by
  constructor
  · intro h; exact ⟨h (-1) (by norm_num),h 1 (by norm_num)⟩
  · rintro ⟨hl,hr⟩ c hc
    have hs : c^2≤1 := (sq_le_one_iff_abs_le_one c).mpr (abs_le.mpr hc)
    have hm : 0≤a*(c^2-1) := mul_nonneg_of_nonpos_of_nonpos ha (by linarith)
    have h1 := mul_nonneg (by linarith [hc.2] : 0≤1-c) hl
    have h2 := mul_nonneg (by linarith [hc.1] : 0≤1+c) hr
    dsimp [quadratic] at *
    nlinarith

/-- Linear quadratics with positive endpoints are strictly positive throughout. -/
theorem linear_quadratic_pos {b d : ℝ} (hl : 0<quadratic 0 b d (-1))
    (hr : 0<quadratic 0 b d 1) (c : ℝ) (hc : c∈Set.Icc (-1:ℝ) 1) :
    0<quadratic 0 b d c := by
  by_cases hb : 0≤b
  · exact lt_of_lt_of_le hl (quadratic_left_min (by norm_num) (by simpa using hb) hc.1)
  · exact lt_of_lt_of_le hr (quadratic_right_min (by norm_num) (by linarith) hc.2)

end
end polyak.General.Regions
