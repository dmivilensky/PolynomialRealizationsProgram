import polyak.Boundary.P1.Bernstein
import polyak.Numerics.TensorIdentity

/-! Exact bivariate coefficient reflection for the independently specified P1 slack. -/
noncomputable section
namespace polyak.Boundary.P1
open Numerics.BivariateIdentity Numerics.TensorBernstein

private def sub (a b : Expr) : Expr := .add a (.mul (.literal (-1)) b)
private def two (a : Expr) : Expr := .mul (.literal 2) a
private def square (a : Expr) : Expr := .pow a 2

private def radialTE : ℕ → Expr → Expr
  | 0,_ => .literal 1
  | 1,_ => .literal 1
  | n+2,z => sub (two (radialTE (n+1) z)) (.mul (square z) (radialTE n z))
private def radialUE : ℕ → Expr → Expr
  | 0,_ => .literal 1
  | 1,_ => .literal 2
  | n+2,z => sub (two (radialUE (n+1) z)) (.mul (square z) (radialUE n z))
private def plainTE : ℕ → Expr → Expr
  | 0,_ => .literal 1
  | 1,a => a
  | n+2,a => sub (.mul (two a) (plainTE (n+1) a)) (plainTE n a)
private def plainUE : ℕ → Expr → Expr
  | 0,_ => .literal 1
  | 1,a => two a
  | n+2,a => sub (.mul (two a) (plainUE (n+1) a)) (plainUE n a)

private theorem radialTE_value (n : ℕ) (z : Expr) (x y : ℝ) :
    (radialTE n z).value x y=radialT n (z.value x y) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [radialTE,Expr.value,radialT]
  | one => simp [radialTE,Expr.value,radialT]
  | more n ih ih1 =>
    simp only [radialTE,sub,two,square,Expr.value,ih,ih1,radialT,Rat.cast_neg,
      Rat.cast_one,Rat.cast_ofNat]
    ring
private theorem radialUE_value (n : ℕ) (z : Expr) (x y : ℝ) :
    (radialUE n z).value x y=radialU n (z.value x y) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [radialUE,Expr.value,radialU]
  | one => simp [radialUE,Expr.value,radialU]
  | more n ih ih1 =>
    simp only [radialUE,sub,two,square,Expr.value,ih,ih1,radialU,Rat.cast_neg,
      Rat.cast_one,Rat.cast_ofNat]
    ring
private theorem plainTE_value (n : ℕ) (a : Expr) (x y : ℝ) :
    (plainTE n a).value x y=plainT n (a.value x y) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [plainTE,Expr.value,plainT]
  | one => rfl
  | more n ih ih1 =>
    simp only [plainTE,sub,two,Expr.value,ih,ih1,plainT,Rat.cast_neg,
      Rat.cast_one,Rat.cast_ofNat]
    ring
private theorem plainUE_value (n : ℕ) (a : Expr) (x y : ℝ) :
    (plainUE n a).value x y=plainU n (a.value x y) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [plainUE,Expr.value,plainU]
  | one => simp [plainUE,two,Expr.value,plainU]
  | more n ih ih1 =>
    simp only [plainUE,sub,two,Expr.value,ih,ih1,plainU,Rat.cast_neg,
      Rat.cast_one,Rat.cast_ofNat]
    ring

private def polynomialSlackE (n : ℕ) (σ : ℚ) (z a : Expr) : Expr :=
  let oneza := Expr.add (.literal 1) (.mul z a)
  let D := Expr.add (.add (.literal 2) (.mul z a))
    (.mul (square z) (sub (square a) (.literal 1)))
  let E := Expr.add oneza (.mul (square z) (sub (two (square a)) (.literal 1)))
  sub (.add (sub (.mul oneza (radialTE n z))
    (.mul (.mul (.pow z n) oneza) (plainTE n a)))
    (.mul (.mul (.mul (.literal σ) (.pow z (n-1))) D) (plainUE (n-1) a)))
    (.mul (.mul (.literal σ) E) (radialUE (n-1) z))

private theorem polynomialSlackE_value (n : ℕ) (σ : ℚ) (z a : Expr) (x y : ℝ) :
    (polynomialSlackE n σ z a).value x y=
      polynomialSlack n (σ : ℝ) (z.value x y) (a.value x y) := by
  simp only [polynomialSlackE,sub,two,square,Expr.value,radialTE_value,radialUE_value,
    plainTE_value,plainUE_value,polynomialSlack,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat]
  ring

/-- The actual slack source, with independent Chebyshev recurrence syntax. -/
def slackExpression (n : ℕ) (σ : ℚ) : Expr :=
  let z := Expr.mul (.literal (3/4)) .x
  polynomialSlackE n σ z (.mul (.mul (.literal (-1)) .y) (.mul z (.literal (1/2))))

def factorExpression (n : ℕ) (σ : ℚ) : Expr :=
  if σ=1 ∧ 4≤n then .pow (.mul (.literal (3/4)) .x) 2 else .literal 1

theorem slackExpression_value (n : ℕ) (σ : ℚ) (x y : ℝ) :
    (slackExpression n σ).value x y=scaledSlack n σ ((3/4)*x) (-y*((3/4)*x)/2) := by
  unfold slackExpression
  rw [polynomialSlackE_value,polynomialSlack_eq]
  norm_num [Expr.value]
  congr 1
  ring

theorem factorExpression_value (n : ℕ) (σ : ℚ) (x y : ℝ) :
    (factorExpression n σ).value x y=if σ=1 ∧ 4≤n then ((3/4)*x)^2 else 1 := by
  unfold factorExpression
  split_ifs <;> norm_num [Expr.value]

/-- Executable rational coefficient equality, separate from the mathematical source. -/
def slackIdentityCheck (n : ℕ) (σ : ℚ) (c : Certificate) : Bool :=
  (slackExpression n σ).check (.mul (factorExpression n σ) c.expression)

theorem scaledSlack_pos_of_identity {n : ℕ} {σ : ℚ} (c : Certificate)
    (he : slackIdentityCheck n σ c=true) (hc : c.check=true)
    {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4) (ha : -z/2≤a ∧ a≤0) :
    0<scaledSlack n σ z a := by
  let x : ℝ := 4*z/3
  let y : ℝ := -2*a/z
  have hx : x∈Set.Icc 0 1 := by dsimp [x]; constructor <;> linarith
  have hy : y∈Set.Icc 0 1 := by
    dsimp [y]
    constructor
    · exact div_nonneg (by linarith) hz.le
    · rw [div_le_one hz]
      linarith [ha.1]
  have hxz : (3/4 : ℝ)*x=z := by dsimp [x]; ring
  have hya : -y*z/2=a := by dsimp [y]; field_simp
  have hp := c.value_pos hc hx hy
  have hs := Expr.check_sound he x y
  rw [slackExpression_value,Expr.value,factorExpression_value,c.expression_value,hxz,hya] at hs
  rw [hs]
  split_ifs <;> positivity

end polyak.Boundary.P1
