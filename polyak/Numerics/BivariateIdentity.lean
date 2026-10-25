import LeanCert.Engine.Algebra.QPoly
import Mathlib.Tactic

/-! Exact executable bivariate identities, with independent real polynomial semantics. -/
namespace polyak.Numerics.BivariateIdentity
open LeanCert.Engine

abbrev Code := List QPoly

noncomputable def value : Code → ℝ → ℝ → ℝ
  | [],_,_ => 0
  | a::as,x,y => Polynomial.aeval x a.toPoly+y*value as x y

def add : Code → Code → Code
  | [],q => q
  | p,[] => p
  | a::as,b::bs => a.add b::add as bs

def scale (a : QPoly) (p : Code) : Code := p.map (QPoly.mul a)

def mul : Code → Code → Code
  | [],_ => []
  | a::as,b => add (scale a b) (QPoly.zero::mul as b)

def constant (a : ℚ) : Code := [QPoly.constant a]
def X : Code := [QPoly.X]
def Y : Code := [QPoly.zero,QPoly.constant 1]

def equal : Code → Code → Bool
  | [],bs => bs.all fun b => decide (QPoly.zero.trim=b.trim)
  | a::as,[] => decide (a.trim=QPoly.zero.trim) && equal as []
  | a::as,b::bs => decide (a.trim=b.trim) && equal as bs

theorem value_add (a b : Code) (x y : ℝ) : value (add a b) x y=value a x y+value b x y := by
  induction a generalizing b with
  | nil => simp [add,value]
  | cons a as ih =>
    cases b with
    | nil => simp [add,value]
    | cons b bs =>
      simp only [add,value,QPoly.toPoly_add,map_add,ih]
      ring

theorem value_scale (a : QPoly) (p : Code) (x y : ℝ) :
    value (scale a p) x y=Polynomial.aeval x a.toPoly*value p x y := by
  induction p with
  | nil => simp [scale,value]
  | cons b bs ih =>
    simp only [scale,List.map_cons,value,QPoly.toPoly_mul,map_mul] at *
    rw [ih]
    ring

theorem value_mul (a b : Code) (x y : ℝ) : value (mul a b) x y=value a x y*value b x y := by
  induction a with
  | nil => simp [mul,value]
  | cons a as ih =>
    simp only [mul,value_add,value_scale,value,QPoly.toPoly_zero,map_zero,zero_add,ih]
    ring

theorem value_constant (a : ℚ) (x y : ℝ) : value (constant a) x y=(a : ℝ) := by
  simp [constant,value,QPoly.toPoly_constant]
theorem value_X (x y : ℝ) : value X x y=x := by simp [X,value,QPoly.toPoly_X]
theorem value_Y (x y : ℝ) : value Y x y=y := by
  simp [Y,value,QPoly.toPoly_zero,QPoly.toPoly_constant]

theorem equal_sound {a b : Code} (h : equal a b=true) (x y : ℝ) : value a x y=value b x y := by
  induction a generalizing b with
  | nil =>
    induction b with
    | nil => rfl
    | cons b bs ih =>
      simp only [equal,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at h
      have he := congrArg QPoly.toPoly h.1
      simp only [QPoly.toPoly_trim,QPoly.toPoly_zero] at he
      simp only [value,← he,map_zero,zero_add,← ih (by simpa only [equal] using h.2)]
      ring
  | cons a as ih =>
    cases b with
    | nil =>
      simp only [equal,Bool.and_eq_true,decide_eq_true_eq] at h
      have he := congrArg QPoly.toPoly h.1
      simp only [QPoly.toPoly_trim,QPoly.toPoly_zero] at he
      simp only [value,he,map_zero,zero_add,ih h.2]
      ring
    | cons b bs =>
      simp only [equal,Bool.and_eq_true,decide_eq_true_eq] at h
      have he := congrArg QPoly.toPoly h.1
      simp only [QPoly.toPoly_trim] at he
      simp only [value,he,ih h.2]

inductive Expr where
  | literal (q : ℚ)
  | x
  | y
  | add (a b : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (n : ℕ)
  deriving Repr

noncomputable def Expr.value : Expr → ℝ → ℝ → ℝ
  | .literal q,_,_ => q
  | .x,xi,_ => xi
  | .y,_,yi => yi
  | .add a b,xi,yi => a.value xi yi+b.value xi yi
  | .mul a b,xi,yi => a.value xi yi*b.value xi yi
  | .pow a n,xi,yi => a.value xi yi^n

def power (a : Code) : ℕ → Code
  | 0 => constant 1
  | n+1 => mul (power a n) a

def Expr.code : Expr → Code
  | .literal q => constant q
  | .x => X
  | .y => Y
  | .add a b => BivariateIdentity.add a.code b.code
  | .mul a b => BivariateIdentity.mul a.code b.code
  | .pow a n => power a.code n

theorem value_power (a : Code) (n : ℕ) (x y : ℝ) : value (power a n) x y=value a x y^n := by
  induction n with
  | zero => simp [power,value_constant]
  | succ n ih => rw [power,value_mul,ih,pow_succ]

theorem Expr.code_value (e : Expr) (x y : ℝ) : BivariateIdentity.value e.code x y=e.value x y := by
  induction e with
  | literal q => exact value_constant q x y
  | x => exact value_X x y
  | y => exact value_Y x y
  | add a b ih ih1 => simp only [Expr.code,value_add,Expr.value,ih,ih1]
  | mul a b ih ih1 => simp only [Expr.code,value_mul,Expr.value,ih,ih1]
  | pow a n ih => simp only [Expr.code,value_power,Expr.value,ih]

def Expr.check (a b : Expr) : Bool := equal a.code b.code

theorem Expr.check_sound {a b : Expr} (h : a.check b=true) (x y : ℝ) :
    a.value x y=b.value x y := by
  rw [← a.code_value,← b.code_value]
  exact equal_sound h x y

def Expr.sum : List Expr → Expr
  | [] => .literal 0
  | a::as => .add a (Expr.sum as)

theorem Expr.sum_value (es : List Expr) (x y : ℝ) :
    (Expr.sum es).value x y=(es.map (fun e=>e.value x y)).sum := by
  induction es with
  | nil => simp [Expr.sum,Expr.value]
  | cons a as ih => simp [Expr.sum,Expr.value,ih]

end polyak.Numerics.BivariateIdentity
