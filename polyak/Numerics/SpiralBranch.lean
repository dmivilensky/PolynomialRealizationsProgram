import polyak.Numerics.Polynomial
import polyak.Spiral.Threshold

/-!
Article: exact sign checks on the physical branch F(ρ,q)=0.
Use: rational boxes isolate q by the original quartic and bound a reduced
rational expression by Bernstein enclosures, without trusting an external
Sturm computation or confusing the two algebraic branches.
Proof: strict monotonicity in positive q and proved rational interval arithmetic.
-/

namespace polyak.Numerics
noncomputable section
open LeanCert.Core LeanCert.Engine

/-- Article: the physical branch is enclosed by two signs of its original polynomial. -/
theorem spiral_branch_bounds {r q a b : ℝ} (hr : 0<r) (hq : 0<q)
    (_ha : 0<a) (hb : 0<b) (hroot : Spiral.spiralPolynomial r q=0)
    (hlo : 0≤Spiral.spiralPolynomial r a) (hhi : Spiral.spiralPolynomial r b≤0) :
    a≤q ∧ q≤b := by
  constructor
  · by_contra hn
    have hlt := Spiral.spiralPolynomial_parameter_lt hr hq (lt_of_not_ge hn)
    rw [hroot] at hlt
    linarith
  · by_contra hn
    have hlt := Spiral.spiralPolynomial_parameter_lt hr hb (lt_of_not_ge hn)
    rw [hroot] at hlt
    linarith

/-- Article: an exact rational expression reduced to degree one in the physical q. -/
structure LinearBranchCode where
  /-- Article: q-independent numerator coefficients in ρ. -/
  constant : QPoly
  /-- Article: coefficient of q in the reduced numerator. -/
  linear : QPoly
  /-- Article: the actual denominator; its sign is checked separately. -/
  denominator : QPoly

/-- Article: evaluation of the exact reduced expression. -/
def LinearBranchCode.value (p : LinearBranchCode) (r q : ℝ) : ℝ :=
  (Polynomial.aeval r p.constant.toPoly+Polynomial.aeval r p.linear.toPoly*q)/
    Polynomial.aeval r p.denominator.toPoly

end
namespace ExecutableBranch
open LeanCert.Core LeanCert.Engine

/-- Article: the source quartic as a univariate polynomial at a rational q. -/
def quarticAt (q : ℚ) : QPoly :=
  ⟨#[-q^2,-2*q,1+2*q-q^2,-2*q,1]⟩

/-- Article: the executable quartic is linked to the original master polynomial. -/
theorem aeval_quarticAt (a : ℚ) (r : ℝ) :
    Polynomial.aeval r (quarticAt a).toPoly=Spiral.spiralPolynomial r a := by
  rw [QPoly.aeval_toPoly_eq_sum]
  norm_num [quarticAt,Finset.sum_range_succ,Spiral.spiralPolynomial]
  ring

/-- Article: a numerator enclosure retaining the independent q interval. -/
def numeratorEnclosure (p : LinearBranchCode) (I J : IntervalRat) : IntervalRat :=
  (QPoly.bernsteinEnclosure p.constant I).add ((QPoly.bernsteinEnclosure p.linear I).mul J)

/-- Article: exact finite acceptance test on one rational rectangle. -/
def positiveCheck (p : LinearBranchCode) (I J : IntervalRat) : Bool :=
  decide (0<(numeratorEnclosure p I J).lo ∧ 0<(QPoly.bernsteinEnclosure p.denominator I).lo)

/-- Article: acceptance proves positivity on the entire rectangle. -/
theorem positiveCheck_sound {p : LinearBranchCode} {I J : IntervalRat}
    (h : positiveCheck p I J=true) {r q : ℝ} (hr : r∈I) (hq : q∈J) :
    0<p.value r q := by
  have hn := IntervalRat.mem_add (QPoly.aeval_mem_bernsteinEnclosure p.constant I hr)
    (IntervalRat.mem_mul (QPoly.aeval_mem_bernsteinEnclosure p.linear I hr) hq)
  have hd := QPoly.aeval_mem_bernsteinEnclosure p.denominator I hr
  simp only [positiveCheck,decide_eq_true_eq] at h
  have hnp : 0<Polynomial.aeval r p.constant.toPoly+Polynomial.aeval r p.linear.toPoly*q :=
    lt_of_lt_of_le (by exact_mod_cast h.1) hn.1
  have hdp : 0<Polynomial.aeval r p.denominator.toPoly :=
    lt_of_lt_of_le (by exact_mod_cast h.2) hd.1
  exact div_pos hnp hdp

/-- Article: one slab checks the two root-isolating signs and the requested positivity. -/
def leafCheck (p : LinearBranchCode) (I J : IntervalRat) : Bool :=
  decide (0<J.lo) && QPoly.bernsteinCheck .lower (quarticAt J.lo) 0 I 0 &&
    QPoly.bernsteinCheck .upper (quarticAt J.hi) 0 I 0 && positiveCheck p I J

/-- Article: a physical-branch leaf certificate excludes the negative algebraic branch. -/
theorem leafCheck_sound {p : LinearBranchCode} {I J : IntervalRat}
    (h : leafCheck p I J=true) {r q : ℝ} (hrI : r∈I) (hr : 0<r) (hq : 0<q)
    (hroot : Spiral.spiralPolynomial r q=0) : 0<p.value r q := by
  simp only [leafCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha,hlo⟩,hhi⟩,hp⟩ := h
  have hla := QPoly.le_aeval_of_bernsteinCheck hlo r hrI
  have hha := QPoly.aeval_le_of_bernsteinCheck hhi r hrI
  rw [aeval_quarticAt] at hla hha
  norm_num only [Rat.cast_zero] at hla hha
  have has : (0 : ℝ)<J.lo := by exact_mod_cast ha
  have hbs : (0 : ℝ)<J.hi := has.trans_le (by exact_mod_cast J.le)
  have hqJ := spiral_branch_bounds hr hq has hbs hroot hla hha
  exact positiveCheck_sound hp hrI hqJ

/-- Article: a compact binary cover with an exact q enclosure at every leaf. -/
inductive Tree where
  /-- Article: a rational rectangle, certified against the actual master equation. -/
  | leaf (qInterval : IntervalRat)
  /-- Article: split the current ρ interval into its two closed halves. -/
  | split (left right : Tree)

/-- Article: acceptance recursively checks the whole interval, including shared endpoints. -/
def Tree.check (p : LinearBranchCode) (I : IntervalRat) : Tree → Bool
  | .leaf J => leafCheck p I J
  | .split left right => left.check p (splitMid I).1 && right.check p (splitMid I).2

/-- Article: one finite tree certifies the whole physical branch over its closed interval. -/
theorem Tree.check_sound (tree : Tree) {p : LinearBranchCode} {I : IntervalRat}
    (h : tree.check p I=true) {r q : ℝ} (hrI : r∈I) (hr : 0<r) (hq : 0<q)
    (hroot : Spiral.spiralPolynomial r q=0) : 0<p.value r q := by
  induction tree generalizing I with
  | leaf J => exact leafCheck_sound h hrI hr hq hroot
  | split left right hl hr' =>
    simp only [Tree.check,Bool.and_eq_true] at h
    rcases mem_splitMid hrI with hleft | hright
    · exact hl h.1 hleft
    · exact hr' h.2 hright

end ExecutableBranch
end polyak.Numerics
