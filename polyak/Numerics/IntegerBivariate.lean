import polyak.Numerics.BivariateBranch

/-!
Article: compact exact signs of the initialized-spiral bivariate numerators.
Use: arithmetic-graph annotations replace repeated rational normalization;
the same integer coefficient source is evaluated by the proved graph engine.
Proof: structural Horner semantics and the existing integer interval checker.
-/

namespace polyak.Numerics.IntegerBivariate
open LeanCert.Core LeanCert.Engine
open chebyshev2.Numerics.IntegerCertificate

/-- Article: exact integer q coefficients, each a polynomial in ρ. -/
abbrev Source := List (List ℤ)

/-- Article: one integer coefficient polynomial as an exact executable Horner polynomial. -/
def coefficientCode : List ℤ → QPoly
  | [] => QPoly.zero
  | a::as => (QPoly.constant a).add (QPoly.X.mul (coefficientCode as))

/-- Article: the same source as executable rational coefficient arrays. -/
def rationalCode (p : Source) : BivariateBranch.Code := p.map coefficientCode

/-- Article: the integer Horner expression for one coefficient polynomial. -/
def coefficientExpr : List ℤ → chebyshev2.Numerics.IntegerCertificate.Expr
  | [] => .literal 0 1
  | a::as => .add (.literal a 1) (.mul (.input 0) (coefficientExpr as))

/-- Article: the independently specified bivariate numerator expression. -/
def sourceExpr : Source → chebyshev2.Numerics.IntegerCertificate.Expr
  | [] => .literal 0 1
  | p::ps => .add (coefficientExpr p) (.mul (.input 1) (sourceExpr ps))

/-- Article: integer Horner evaluation equals the actual rational polynomial. -/
theorem coefficientExpr_value (p : List ℤ) (v : ℕ → ℝ) :
    (coefficientExpr p).value v=Polynomial.aeval (v 0)
      (coefficientCode p).toPoly := by
  induction p with
  | nil => simp [coefficientExpr,coefficientCode,chebyshev2.Numerics.IntegerCertificate.Expr.value]
  | cons a as ih =>
    simp only [coefficientExpr,chebyshev2.Numerics.IntegerCertificate.Expr.value,coefficientCode,
      QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
      map_add,map_mul,Polynomial.aeval_C,Polynomial.aeval_X,ih]
    simp

/-- Article: the graph source denotes the exact bivariate numerator. -/
theorem sourceExpr_value (p : Source) (v : ℕ → ℝ) :
    (sourceExpr p).value v=BivariateBranch.value (rationalCode p) (v 0) (v 1) := by
  induction p with
  | nil => simp [sourceExpr,rationalCode,BivariateBranch.value,
      chebyshev2.Numerics.IntegerCertificate.Expr.value]
  | cons a as ih =>
    change (coefficientExpr a).value v+v 1*(sourceExpr as).value v=
      Polynomial.aeval (v 0) (coefficientCode a).toPoly+
        v 1*BivariateBranch.value (rationalCode as) (v 0) (v 1)
    rw [coefficientExpr_value,ih]

/-- Article: a proposed arithmetic graph on two rational parameter intervals. -/
structure Witness where
  /-- Article: common positive integer scale. -/
  scale : ℕ
  /-- Article: input enclosure for the growth factor. -/
  radial : Bounds
  /-- Article: input enclosure for the physical q. -/
  physical : Bounds
  /-- Article: integer arithmetic annotations for the fixed source expression. -/
  nodes : List Node
  /-- Article: final numerator enclosure. -/
  result : Bounds

/-- Article: finite exact graph acceptance including source identity and a positive lower bound. -/
def Witness.check (w : Witness) (p : Source) (I J : IntervalRat) : Bool :=
  decide (0<w.scale) && rationalIntervalCheck w.scale I.lo I.hi w.radial &&
    rationalIntervalCheck w.scale J.lo J.hi w.physical &&
    programCheck w.scale [w.radial,w.physical] w.nodes &&
    expressionCheck w.nodes 0 (sourceExpr p) &&
    decide ((programBounds [w.radial,w.physical] w.nodes)[0]?=some w.result) &&
    decide (0<w.result.lo)

/-- Article: a successful integer graph proves the specified numerator positive everywhere in the box. -/
theorem Witness.check_sound (w : Witness) {p : Source} {I J : IntervalRat}
    (h : w.check p I J=true) {r q : ℝ} (hr : r∈I) (hq : q∈J) :
    0<BivariateBranch.value (rationalCode p) r q := by
  simp only [Witness.check,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hs,hi⟩,hj⟩,hc⟩,he⟩,hout⟩,hp⟩ := h
  let v : ℕ → ℝ := fun n => if n=0 then r else q
  have hv : Encloses w.scale [w.radial,w.physical] v := by
    intro n A hA
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hA
      subst A
      exact rationalIntervalCheck_sound hs hi hr.1 hr.2
    | succ n =>
      cases n with
      | zero =>
        simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hA
        subst A
        exact rationalIntervalCheck_sound hs hj hq.1 hq.2
      | succ n => simp at hA
  have hh := source_enclosed hs w.nodes hv hc he hout
  rw [sourceExpr_value] at hh
  change w.result.lo≤(w.scale : ℝ)*BivariateBranch.value (rationalCode p) r q ∧ _ at hh
  have hp' : (0 : ℝ)<w.result.lo := by exact_mod_cast hp
  have hs' : (0 : ℝ)<w.scale := by exact_mod_cast hs
  nlinarith [hh.1]

/-- Article: a finite closed cover of the actual physical branch. -/
inductive Tree where
  /-- Article: a physical q box and its integer numerator witness. -/
  | leaf (qInterval : IntervalRat) (witness : Witness)
  /-- Article: bisect the current growth-factor interval, retaining the midpoint in both halves. -/
  | split (left right : Tree)

/-- Article: root-isolation signs are checked in addition to the integer arithmetic graph. -/
def leafCheck (p : Source) (I J : IntervalRat) (w : Witness) : Bool :=
  decide (0<J.lo) && QPoly.bernsteinCheck .lower (ExecutableBranch.quarticAt J.lo) 0 I 0 &&
    QPoly.bernsteinCheck .upper (ExecutableBranch.quarticAt J.hi) 0 I 0 && w.check p I J

/-- Article: acceptance cannot certify a sign on the wrong algebraic branch. -/
theorem leafCheck_sound {p : Source} {I J : IntervalRat} {w : Witness}
    (h : leafCheck p I J w=true) {r q : ℝ} (hrI : r∈I) (hr : 0<r) (hq : 0<q)
    (hroot : Spiral.spiralPolynomial r q=0) : 0<BivariateBranch.value (rationalCode p) r q := by
  simp only [leafCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha,hlo⟩,hhi⟩,hp⟩ := h
  have hla := QPoly.le_aeval_of_bernsteinCheck hlo r hrI
  have hha := QPoly.aeval_le_of_bernsteinCheck hhi r hrI
  rw [ExecutableBranch.aeval_quarticAt] at hla hha
  norm_num only [Rat.cast_zero] at hla hha
  have has : (0 : ℝ)<J.lo := by exact_mod_cast ha
  have hbs : (0 : ℝ)<J.hi := has.trans_le (by exact_mod_cast J.le)
  exact w.check_sound hp hrI (spiral_branch_bounds hr hq has hbs hroot hla hha)

/-- Article: recursively verify the complete compact branch interval. -/
def check (p : Source) (I : IntervalRat) : Tree → Bool
  | .leaf J w => leafCheck p I J w
  | .split left right => check p (splitMid I).1 left && check p (splitMid I).2 right

/-- Article: finite literal annotations prove a uniform sign for the actual branch. -/
theorem check_sound (tree : Tree) {p : Source} {I : IntervalRat}
    (h : check p I tree=true) {r q : ℝ} (hrI : r∈I) (hr : 0<r) (hq : 0<q)
    (hroot : Spiral.spiralPolynomial r q=0) : 0<BivariateBranch.value (rationalCode p) r q := by
  induction tree generalizing I with
  | leaf J w => exact leafCheck_sound h hrI hr hq hroot
  | split left right hl hr' =>
    simp only [check,Bool.and_eq_true] at h
    rcases mem_splitMid hrI with hleft | hright
    · exact hl h.1 hleft
    · exact hr' h.2 hright

end polyak.Numerics.IntegerBivariate
