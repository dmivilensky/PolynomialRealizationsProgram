import polyak.Numerics.IntegerBivariate

/-!
Article: denominator signs in the exact initialized-spiral rational identities.
Use: a small coefficient check excludes every zero denominator on ρ,q>0.
Proof: positive-variable Horner evaluation of nonnegative integer coefficients.
-/

namespace polyak.Numerics.IntegerBivariate
open chebyshev2.Numerics.IntegerCertificate

/-- Article: every coefficient in one univariate row is nonnegative. -/
def nonnegativeRow (p : List ℤ) : Bool := p.all (fun c => decide (0≤c))

/-- Article: at least one coefficient in a row is strictly positive. -/
def positiveRow (p : List ℤ) : Bool := p.any (fun c => decide (0<c))

/-- Article: coefficient signs imply nonnegative evaluation at a nonnegative parameter. -/
theorem row_nonneg (p : List ℤ) (v : ℕ → ℝ) (hv : 0≤v 0)
    (h : nonnegativeRow p=true) : 0≤(coefficientExpr p).value v := by
  induction p with
  | nil => simp [coefficientExpr,Expr.value]
  | cons a as ih =>
    simp only [nonnegativeRow,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at h
    have ha : (0 : ℝ)≤a := by exact_mod_cast h.1
    have ht := ih h.2
    simp only [coefficientExpr,Expr.value,Nat.cast_one,div_one]
    positivity

/-- Article: a positive coefficient makes the entire row positive at a positive parameter. -/
theorem row_pos (p : List ℤ) (v : ℕ → ℝ) (hv : 0<v 0)
    (hn : nonnegativeRow p=true) (hp : positiveRow p=true) : 0<(coefficientExpr p).value v := by
  induction p with
  | nil => simp [positiveRow] at hp
  | cons a as ih =>
    simp only [nonnegativeRow,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at hn
    simp only [positiveRow,List.any_cons,Bool.or_eq_true,decide_eq_true_eq] at hp
    have ha : (0 : ℝ)≤a := by exact_mod_cast hn.1
    have ht : 0≤(coefficientExpr as).value v := row_nonneg as v hv.le hn.2
    simp only [coefficientExpr,Expr.value,Nat.cast_one,div_one]
    rcases hp with hp | hp
    · have ha' : (0 : ℝ)<a := by exact_mod_cast hp
      positivity
    · have ht' := ih hn.2 hp
      positivity

/-- Article: finite nonnegative coefficient check for a bivariate denominator. -/
def positiveCoefficients (p : Source) : Bool := p.all nonnegativeRow && p.any positiveRow

/-- Article: an accepted denominator is positive on the whole physical parameter quadrant. -/
theorem positiveCoefficients_sound (p : Source) (h : positiveCoefficients p=true)
    {r q : ℝ} (hr : 0<r) (hq : 0<q) : 0<BivariateBranch.value (rationalCode p) r q := by
  let v : ℕ → ℝ := fun n => if n=0 then r else q
  have hn (ps : Source) (hh : ps.all nonnegativeRow=true) : 0≤(sourceExpr ps).value v := by
    induction ps with
    | nil => simp [sourceExpr,Expr.value]
    | cons a as ih =>
      simp only [List.all_cons,Bool.and_eq_true] at hh
      have ha := row_nonneg a v hr.le hh.1
      have ht := ih hh.2
      simp only [sourceExpr,Expr.value]
      change 0≤(coefficientExpr a).value v+q*(sourceExpr as).value v
      positivity
  have hp (ps : Source) (ha : ps.all nonnegativeRow=true) (hb : ps.any positiveRow=true) :
      0<(sourceExpr ps).value v := by
    induction ps with
    | nil => simp at hb
    | cons a as ih =>
      simp only [List.all_cons,Bool.and_eq_true] at ha
      simp only [List.any_cons,Bool.or_eq_true] at hb
      have har := row_nonneg a v hr.le ha.1
      have htr := hn as ha.2
      change 0<(coefficientExpr a).value v+q*(sourceExpr as).value v
      rcases hb with hb | hb
      · have har' := row_pos a v hr ha.1 hb
        positivity
      · have htr' := ih ha.2 hb
        positivity
  have hh : p.all nonnegativeRow=true ∧ p.any positiveRow=true := by
    simpa only [positiveCoefficients,Bool.and_eq_true] using h
  have hh' := hp p hh.1 hh.2
  rw [sourceExpr_value] at hh'
  exact hh'

end polyak.Numerics.IntegerBivariate
