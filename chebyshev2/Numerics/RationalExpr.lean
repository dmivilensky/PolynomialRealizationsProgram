import chebyshev2.Numerics.IntervalExpr
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
Article: chebyshev2, Appendix F.2.
`chebyshev2.Numerics.IntervalExpr.polynomial` compiles finite polynomial expressions into the
sound rational interval-expression language.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.IntervalExpr.enclose_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics.IntervalExpr
set_option autoImplicit false
variable {d : ℕ}
/--
Supplies the typeclass structure specified by `OfNat (IntervalExpr d) n`. This lets subsequent
generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
scoped instance (n : ℕ) : OfNat (IntervalExpr d) n := ⟨.literal n⟩
/--
Supplies the typeclass structure specified by `Add (IntervalExpr d)`. This lets subsequent
generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
scoped instance : Add (IntervalExpr d) := ⟨.add⟩
/--
Supplies the typeclass structure specified by `Neg (IntervalExpr d)`. This lets subsequent
generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
scoped instance : Neg (IntervalExpr d) := ⟨.neg⟩
/--
Supplies the typeclass structure specified by `Sub (IntervalExpr d)`. This lets subsequent
generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
scoped instance : Sub (IntervalExpr d) := ⟨fun a b => .add a (.neg b)⟩
/--
Supplies the typeclass structure specified by `Mul (IntervalExpr d)`. This lets subsequent
generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
scoped instance : Mul (IntervalExpr d) := ⟨.mul⟩
/--
Supplies the typeclass structure specified by `Div (IntervalExpr d)`. This lets subsequent
generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
scoped instance : Div (IntervalExpr d) := ⟨fun a b => .mul a (.inverse b)⟩
/--
Supplies the typeclass structure specified by `Pow (IntervalExpr d) ℕ`. This lets subsequent
generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
scoped instance : Pow (IntervalExpr d) ℕ := ⟨.power⟩
open scoped IntervalExpr

/--
Exact identity `(ofNat(n) : IntervalExpr d).value x=n`.

Use: `chebyshev2.Numerics.IntervalExpr.value_sum` uses this identity to establish exact
identity `(sum f n).value x=∑ i∈Finset.range n,(f i).value x`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
@[simp] theorem value_nat (x : Fin d → ℝ) (n : ℕ) : (ofNat(n) : IntervalExpr d).value x=n := by
  change ((n:ℚ):ℝ)=n
  exact Rat.cast_natCast n
/--
Exact identity `(a+b).value x=a.value x+b.value x`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem value_add (x : Fin d → ℝ) (a b : IntervalExpr d) :
    (a+b).value x=a.value x+b.value x := rfl
/--
The precise assertion is `(-a).value x= -a.value x`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem value_neg (x : Fin d → ℝ) (a : IntervalExpr d) : (-a).value x= -a.value x := rfl
/--
Exact identity `(a-b).value x=a.value x-b.value x`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem value_sub (x : Fin d → ℝ) (a b : IntervalExpr d) :
    (a-b).value x=a.value x-b.value x := rfl
/--
Exact identity `(a*b).value x=a.value x*b.value x`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem value_mul (x : Fin d → ℝ) (a b : IntervalExpr d) :
    (a*b).value x=a.value x*b.value x := rfl
/--
Exact identity `(a/b).value x=a.value x/b.value x`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem value_div (x : Fin d → ℝ) (a b : IntervalExpr d) :
    (a/b).value x=a.value x/b.value x := rfl
/--
Exact identity `(a^n).value x=(a.value x)^n`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem value_pow (x : Fin d → ℝ) (a : IntervalExpr d) (n : ℕ) :
    (a^n).value x=(a.value x)^n := rfl
/--
Exact identity `(.literal q : IntervalExpr d).value x=q`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem value_literal (x : Fin d → ℝ) (q : ℚ) : (.literal q : IntervalExpr d).value x=q := rfl
/--
Exact identity `(.variable i : IntervalExpr d).value x=x i`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem value_variable (x : Fin d → ℝ) (i : Fin d) :
    (.variable i : IntervalExpr d).value x=x i := rfl

/--
Defines `sum` by pattern matching with result type `ℕ → IntervalExpr d`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntervalExpr.polynomial` uses this definition in the displayed
construction of `polynomial`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def sum (f : ℕ → IntervalExpr d) : ℕ → IntervalExpr d
  | 0 => 0
  | n+1 => sum f n+f n

/--
Exact identity `(sum f n).value x=∑ i∈Finset.range n,(f i).value x`.

Use: `chebyshev2.Numerics.IntervalExpr.value_polynomial` rewrites with this identity to
establish exact identity `(polynomial P a).value x=P.aeval (a.value x)`.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
@[simp] theorem value_sum (x : Fin d → ℝ) (f : ℕ → IntervalExpr d) (n : ℕ) :
    (sum f n).value x=∑ i∈Finset.range n,(f i).value x := by
  induction n with
  | zero => simp [sum]
  | succ n ih => simp [sum,ih,Finset.sum_range_succ]

/--
Defines `polynomial` of type `IntervalExpr d` by `sum (fun i => .literal (P.coeff i)*a^i)
(P.natDegree+1)`.

Use: `chebyshev2.Numerics.IntervalExpr.value_polynomial` rewrites with this definition to
establish exact identity `(polynomial P a).value x=P.aeval (a.value x)`.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def polynomial (P : Polynomial ℚ) (a : IntervalExpr d) : IntervalExpr d :=
  sum (fun i => .literal (P.coeff i)*a^i) (P.natDegree+1)

/--
Exact identity `(polynomial P a).value x=P.aeval (a.value x)`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.IntervalExpr.value_sum` with the
arguments shown in the proof.
-/
@[simp] theorem value_polynomial (x : Fin d → ℝ) (P : Polynomial ℚ) (a : IntervalExpr d) :
    (polynomial P a).value x=P.aeval (a.value x) := by
  simp only [polynomial,value_sum,value_mul,value_literal,value_pow,
    Polynomial.aeval_eq_sum_range,Algebra.smul_def]
  rfl

end chebyshev2.Numerics.IntervalExpr
