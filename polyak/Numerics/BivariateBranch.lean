import polyak.Numerics.SpiralBranch

/-!
Article: exact initialized-spiral signs on the physical algebraic branch.
Use: certify the independently specified low-degree bivariate numerators
directly, retaining correlations through rational q boxes at every ρ slab.
Proof: Bernstein coefficient enclosures, interval Horner evaluation, and the
proved root isolation by the original quartic on every leaf of the closed cover.
-/

namespace polyak.Numerics.BivariateBranch
open LeanCert.Core LeanCert.Engine ExecutableBranch

/-- Article: q coefficients, each an exact univariate rational polynomial in ρ. -/
abbrev Code := List QPoly

/-- Article: actual real evaluation of the specified bivariate polynomial. -/
noncomputable def value (p : Code) (r q : ℝ) : ℝ :=
  p.foldr (fun coefficient rest => Polynomial.aeval r coefficient.toPoly+q*rest) 0

/-- Article: interval Horner evaluation; coefficient intervals use Bernstein. -/
def enclosure (p : Code) (I J : IntervalRat) : IntervalRat :=
  p.foldr (fun coefficient rest => (QPoly.bernsteinEnclosure coefficient I).add (J.mul rest))
    ⟨0,0,le_rfl⟩

/-- Article: every actual bivariate value lies in the computed enclosure. -/
theorem value_mem_enclosure (p : Code) {I J : IntervalRat} {r q : ℝ}
    (hr : r∈I) (hq : q∈J) : value p r q∈enclosure p I J := by
  induction p with
  | nil => simp [value,enclosure,IntervalRat.mem_def]
  | cons coefficient rest ih =>
    exact IntervalRat.mem_add (QPoly.aeval_mem_bernsteinEnclosure coefficient I hr)
      (IntervalRat.mem_mul hq ih)

/-- Article: a slab checks both signs isolating the physical q and the numerator. -/
def leafCheck (p : Code) (I J : IntervalRat) : Bool :=
  decide (0<J.lo) && QPoly.bernsteinCheck .lower (quarticAt J.lo) 0 I 0 &&
    QPoly.bernsteinCheck .upper (quarticAt J.hi) 0 I 0 && decide (0<(enclosure p I J).lo)

/-- Article: leaf acceptance proves the source numerator positive on the physical branch. -/
theorem leafCheck_sound {p : Code} {I J : IntervalRat} (h : leafCheck p I J=true)
    {r q : ℝ} (hrI : r∈I) (hr : 0<r) (hq : 0<q)
    (hroot : Spiral.spiralPolynomial r q=0) : 0<value p r q := by
  simp only [leafCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha,hlo⟩,hhi⟩,hp⟩ := h
  have hla := QPoly.le_aeval_of_bernsteinCheck hlo r hrI
  have hha := QPoly.aeval_le_of_bernsteinCheck hhi r hrI
  rw [aeval_quarticAt] at hla hha
  norm_num only [Rat.cast_zero] at hla hha
  have has : (0 : ℝ)<J.lo := by exact_mod_cast ha
  have hbs : (0 : ℝ)<J.hi := has.trans_le (by exact_mod_cast J.le)
  have hqJ := spiral_branch_bounds hr hq has hbs hroot hla hha
  exact lt_of_lt_of_le (by exact_mod_cast hp) (value_mem_enclosure p hrI hqJ).1

/-- Article: an explicit finite dyadic cover with rational q bounds. -/
def check (p : Code) (I : IntervalRat) : Tree → Bool
  | .leaf J => leafCheck p I J
  | .split left right => check p (splitMid I).1 left && check p (splitMid I).2 right

/-- Article: a finite accepted tree proves the requested source sign on its entire domain. -/
theorem check_sound (tree : Tree) {p : Code} {I : IntervalRat}
    (h : check p I tree=true) {r q : ℝ} (hrI : r∈I) (hr : 0<r) (hq : 0<q)
    (hroot : Spiral.spiralPolynomial r q=0) : 0<value p r q := by
  induction tree generalizing I with
  | leaf J => exact leafCheck_sound h hrI hr hq hroot
  | split left right hl hr' =>
    simp only [check,Bool.and_eq_true] at h
    rcases mem_splitMid hrI with hleft | hright
    · exact hl h.1 hleft
    · exact hr' h.2 hright

end polyak.Numerics.BivariateBranch
