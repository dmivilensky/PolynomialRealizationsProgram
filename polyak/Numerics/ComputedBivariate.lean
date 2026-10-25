import polyak.Numerics.IntegerBivariate
import chebyshev2.Numerics.IntegerEval

/-!
Article: compact initialized-spiral sign witnesses.
Use: recompute integer enclosures from the literal source instead of storing
large intermediate annotation arrays or normalizing high-degree rationals.
Proof: each arithmetic step passes the existing proved integer checker.
-/

namespace polyak.Numerics.ComputedBivariate
open LeanCert.Core LeanCert.Engine
open chebyshev2.Numerics.IntegerCertificate
private abbrev IntExpr := chebyshev2.Numerics.IntegerCertificate.Expr

/-- Article: the checked arithmetic step discards only unused proposal witnesses. -/
def step (s : ℕ) (inputs : List Bounds) (op : Op) : Option Bounds :=
  (evalStep s inputs [] op).map Prod.fst

/-- Article: successful evaluation of one checked arithmetic operation is sound. -/
theorem step_sound {s : ℕ} (hs : 0<s) {inputs : List Bounds} {op : Op}
    {v : ℕ → ℝ} {R : Bounds} (hv : Encloses s inputs v) (h : step s inputs op=some R) :
    R.Mem s (op.value v) := by
  cases he : evalStep s inputs [] op with
  | none => simp [step,he] at h
  | some pair =>
    have hh : pair.1=R := by simpa only [step,he,Option.map_some,Option.some.injEq] using h
    subst R
    exact evalStep_sound hs hv he

/-- Article: the two input enclosures carry exactly their stated actual values. -/
theorem encloses_pair {s : ℕ} {A B : Bounds} {a b : ℝ} (ha : A.Mem s a) (hb : B.Mem s b) :
    Encloses s [A,B] (fun n => if n=0 then a else b) := by
  intro n C hn
  cases n with
  | zero =>
    have he : A=C := by simpa using hn
    subst C
    exact ha
  | succ n =>
    cases n with
    | zero =>
      have he : B=C := by simpa using hn
      subst C
      exact hb
    | succ n => simp at hn

/-- Article: only exact integer/rational literals, addition and multiplication are needed. -/
def eval (s : ℕ) (inputs : List Bounds) : IntExpr → Option Bounds
  | .input n => inputs[n]?
  | .literal n d => step s [] (.literal n d)
  | .add a b => do
    let A ← eval s inputs a
    let B ← eval s inputs b
    step s [A,B] (.add 0 1)
  | .mul a b => do
    let A ← eval s inputs a
    let B ← eval s inputs b
    step s [A,B] (.mul 0 1)
  | .neg _ | .inv _ | .cubic _ _ => none

/-- Article: computed integer Horner enclosures bound the actual source expression. -/
theorem eval_sound (e : IntExpr) {s : ℕ} (hs : 0<s) {inputs : List Bounds}
    {v : ℕ → ℝ} {R : Bounds} (hv : Encloses s inputs v) (h : eval s inputs e=some R) :
    R.Mem s (e.value v) := by
  induction e generalizing R with
  | input n => exact hv n R h
  | literal n d => exact step_sound (v := v) hs (by intro n I hn; simp at hn) h
  | add a b ia ib =>
    cases ha : eval s inputs a with
    | none => simp [eval,ha] at h
    | some A =>
      cases hb : eval s inputs b with
      | none => simp [eval,hb] at h
      | some B =>
        have hh : step s [A,B] (.add 0 1)=some R := by simpa [eval,ha,hb] using h
        exact step_sound hs (encloses_pair (ia ha) (ib hb)) hh
  | mul a b ia ib =>
    cases ha : eval s inputs a with
    | none => simp [eval,ha] at h
    | some A =>
      cases hb : eval s inputs b with
      | none => simp [eval,hb] at h
      | some B =>
        have hh : step s [A,B] (.mul 0 1)=some R := by simpa [eval,ha,hb] using h
        exact step_sound hs (encloses_pair (ia ha) (ib hb)) hh
  | neg => simp [eval] at h
  | inv => simp [eval] at h
  | cubic => simp [eval] at h

/-- Article: outward integer bounds for a stated exact rational interval. -/
def rationalBounds (s : ℕ) (I : IntervalRat) : Bounds :=
  ⟨I.lo.num*s/(I.lo.den : ℤ),ceilDiv (I.hi.num*s) I.hi.den⟩

/-- Article: compute and check a positive integer enclosure for the actual source. -/
def positiveCheck (s : ℕ) (p : IntegerBivariate.Source) (I J : IntervalRat) : Bool :=
  decide (0<s) && rationalIntervalCheck s I.lo I.hi (rationalBounds s I) &&
    rationalIntervalCheck s J.lo J.hi (rationalBounds s J) &&
      match eval s [rationalBounds s I,rationalBounds s J] (IntegerBivariate.sourceExpr p) with
      | none => false
      | some R => decide (0<R.lo)

/-- Article: acceptance implies positivity on the entire rational rectangle. -/
theorem positiveCheck_sound {s : ℕ} {p : IntegerBivariate.Source} {I J : IntervalRat}
    (h : positiveCheck s p I J=true) {r q : ℝ} (hr : r∈I) (hq : q∈J) :
    0<BivariateBranch.value (IntegerBivariate.rationalCode p) r q := by
  simp only [positiveCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hs,hi⟩,hj⟩,hout⟩ := h
  have hri := rationalIntervalCheck_sound hs hi hr.1 hr.2
  have hqi := rationalIntervalCheck_sound hs hj hq.1 hq.2
  cases he : eval s [rationalBounds s I,rationalBounds s J] (IntegerBivariate.sourceExpr p) with
  | none => simp [he] at hout
  | some R =>
    have hp : 0<R.lo := by simpa only [he,decide_eq_true_eq] using hout
    have hh := eval_sound (IntegerBivariate.sourceExpr p) hs (encloses_pair hri hqi) he
    rw [IntegerBivariate.sourceExpr_value] at hh
    change R.lo≤(s : ℝ)*BivariateBranch.value (IntegerBivariate.rationalCode p) r q ∧ _ at hh
    have hs' : (0 : ℝ)<s := by exact_mod_cast hs
    have hp' : (0 : ℝ)<R.lo := by exact_mod_cast hp
    nlinarith [hh.1]

/-- Article: the physical-branch isolation signs are checked alongside integer Horner positivity. -/
def leafCheck (s : ℕ) (p : IntegerBivariate.Source) (I J : IntervalRat) : Bool :=
  decide (0<J.lo) && QPoly.bernsteinCheck .lower (ExecutableBranch.quarticAt J.lo) 0 I 0 &&
    QPoly.bernsteinCheck .upper (ExecutableBranch.quarticAt J.hi) 0 I 0 && positiveCheck s p I J

/-- Article: physical-branch leaf acceptance is a mathematical source sign. -/
theorem leafCheck_sound {s : ℕ} {p : IntegerBivariate.Source} {I J : IntervalRat}
    (h : leafCheck s p I J=true) {r q : ℝ} (hrI : r∈I) (hr : 0<r) (hq : 0<q)
    (hroot : Spiral.spiralPolynomial r q=0) :
    0<BivariateBranch.value (IntegerBivariate.rationalCode p) r q := by
  simp only [leafCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha,hlo⟩,hhi⟩,hp⟩ := h
  have hla := QPoly.le_aeval_of_bernsteinCheck hlo r hrI
  have hha := QPoly.aeval_le_of_bernsteinCheck hhi r hrI
  rw [ExecutableBranch.aeval_quarticAt] at hla hha
  norm_num only [Rat.cast_zero] at hla hha
  have has : (0 : ℝ)<J.lo := by exact_mod_cast ha
  have hbs : (0 : ℝ)<J.hi := has.trans_le (by exact_mod_cast J.le)
  exact positiveCheck_sound hp hrI (spiral_branch_bounds hr hq has hbs hroot hla hha)

/-- Article: recompute the finite exact cover using compact integer intermediates. -/
def check (s : ℕ) (p : IntegerBivariate.Source) (I : IntervalRat) : ExecutableBranch.Tree → Bool
  | .leaf J => leafCheck s p I J
  | .split left right => check s p (splitMid I).1 left && check s p (splitMid I).2 right

/-- Article: an accepted finite cover proves the source numerator positive uniformly. -/
theorem check_sound (tree : ExecutableBranch.Tree) {s : ℕ} {p : IntegerBivariate.Source}
    {I : IntervalRat} (h : check s p I tree=true) {r q : ℝ} (hrI : r∈I) (hr : 0<r) (hq : 0<q)
    (hroot : Spiral.spiralPolynomial r q=0) :
    0<BivariateBranch.value (IntegerBivariate.rationalCode p) r q := by
  induction tree generalizing I with
  | leaf J => exact leafCheck_sound h hrI hr hq hroot
  | split left right hl hr' =>
    simp only [check,Bool.and_eq_true] at h
    rcases mem_splitMid hrI with hleft | hright
    · exact hl h.1 hleft
    · exact hr' h.2 hright

end polyak.Numerics.ComputedBivariate
