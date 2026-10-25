import polyak.Numerics.KernelDecide
import polyak.Boundary.P2.Rational
import polyak.Boundary.P2.Source

/-!
Article: Lemma p2certs, exact single-center Taylor sign certificates on J.
Use: literal coefficient arrays certify rational source formulas through RationalCode.exact.
-/

namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial

/-- Article: a signed exact Taylor check, with the source interval fixed independently. -/
def signedTaylorCheck (p : QPoly) (sg : ℚ) : Bool :=
  Numerics.taylorPositiveCheck ((QPoly.constant sg).mul p) (6789/4000) (7/4000)

/-- Article: an exact Bernstein fallback uses the same independently fixed interval. -/
def signedPolynomialCheck (p : QPoly) (sg : ℚ) : Bool :=
  signedTaylorCheck p sg || QPoly.bernsteinCheck .strictLower
    ((QPoly.constant sg).mul p) 0 Numerics.transitionInterval 3

/-- Article: a successful literal check proves a uniform signed polynomial sign. -/
theorem signedTaylorCheck_positive {p : QPoly} {sg : ℚ}
    (hc : signedTaylorCheck p sg=true) {z : ℝ} (hz : z∈parameterInterval) :
    0 < (sg : ℝ)*aeval z p.toPoly := by
  let P : Numerics.PolynomialCode (((QPoly.constant sg).mul p).toPoly) := ⟨_,rfl⟩
  have hx : |z-(6789/4000 : ℝ)| ≤ (7/4000 : ℝ) := by
    rcases hz with ⟨hl,hu⟩
    apply abs_le.mpr
    constructor <;> linarith
  have hx' : |z-((6789/4000 : ℚ) : ℝ)| ≤ ((7/4000 : ℚ) : ℝ) := by norm_num; exact hx
  have h := P.positive_of_taylor (6789/4000) (7/4000) hc z hx'
  simpa [QPoly.toPoly_mul,QPoly.toPoly_constant] using h

/-- Article: a checked strict sign excludes denominator zero everywhere on J. -/
theorem signedTaylorCheck_ne_zero {p : QPoly} {sg : ℚ}
    (hc : signedTaylorCheck p sg=true) :
    ∀ z∈parameterInterval, aeval z p.toPoly≠0 := by
  intro z hz he
  have h := signedTaylorCheck_positive hc hz
  rw [he,mul_zero] at h
  exact (lt_irrefl 0) h

/-- Article: either exact sign method proves the same specified polynomial inequality. -/
theorem signedPolynomialCheck_positive {p : QPoly} {sg : ℚ}
    (hc : signedPolynomialCheck p sg=true) {z : ℝ} (hz : z∈parameterInterval) :
    0 < (sg : ℝ)*aeval z p.toPoly := by
  simp only [signedPolynomialCheck,Bool.or_eq_true] at hc
  rcases hc with ht | hb
  · exact signedTaylorCheck_positive ht hz
  · have hm : z∈Numerics.transitionInterval := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num [Numerics.transitionInterval]
      exact hz
    have h := QPoly.lt_aeval_of_bernsteinCheck hb z hm
    simpa [QPoly.toPoly_mul,QPoly.toPoly_constant] using h

/-- Article: either checked sign method excludes zero on the whole source interval. -/
theorem signedPolynomialCheck_ne_zero {p : QPoly} {sg : ℚ}
    (hc : signedPolynomialCheck p sg=true) :
    ∀ z∈parameterInterval, aeval z p.toPoly≠0 := by
  intro z hz he
  have h := signedPolynomialCheck_positive hc hz
  rw [he,mul_zero] at h
  exact (lt_irrefl 0) h

/-- Article: source positivity from two checked equal signs, with all divisions justified. -/
theorem RationalCode.positive {f : ℝ → ℝ} (F : RationalCode parameterInterval f) {sg : ℚ}
    (hs : sg=1 ∨ sg= -1)
    (hn : signedTaylorCheck F.numerator sg=true)
    (hd : signedTaylorCheck F.denominator sg=true) :
    ∀ z∈parameterInterval, 0 < f z := by
  intro z hz
  have hp := signedTaylorCheck_positive hn hz
  have hq := signedTaylorCheck_positive hd hz
  rw [F.exact z hz]
  rcases hs with rfl | rfl
  · simpa only [Rat.cast_one,one_mul] using div_pos hp hq
  · simp only [Rat.cast_neg,Rat.cast_one,neg_one_mul] at hp hq
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)

/-- Article: source positivity permits either exact finite polynomial sign method. -/
theorem RationalCode.positive_check {f : ℝ → ℝ} (F : RationalCode parameterInterval f) {sg : ℚ}
    (hs : sg=1 ∨ sg= -1)
    (hn : signedPolynomialCheck F.numerator sg=true)
    (hd : signedPolynomialCheck F.denominator sg=true) :
    ∀ z∈parameterInterval, 0 < f z := by
  intro z hz
  have hp := signedPolynomialCheck_positive hn hz
  have hq := signedPolynomialCheck_positive hd hz
  rw [F.exact z hz]
  rcases hs with rfl | rfl
  · simpa only [Rat.cast_one,one_mul] using div_pos hp hq
  · simp only [Rat.cast_neg,Rat.cast_one,neg_one_mul] at hp hq
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)

end
end polyak.Boundary.P2
