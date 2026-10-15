import «2610.05164v2».Numerics.CubicRoot
import «2610.05164v2».Numerics.HighPrecision

/-!
Article: 2610.05164v2, Lemma 19.
Executable interval Newton refinement for Lemma 19.
Result: `«2610.05164v2».Numerics.cubicNewton_sound` supplies the stated article conclusion.
-/
namespace «2610.05164v2».Numerics
open Set LeanCert.Core
set_option autoImplicit false

/--
Defines `cubicSlopeInterval` of type `IntervalRat` by `IntervalRat.sub (IntervalRat.mul
(IntervalRat.singleton 3) (powerHigh X 2)) A`.

Use: `«2610.05164v2».Numerics.cubicNewton` uses this definition in the displayed construction
of `cubicNewton`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 19 via `«2610.05164v2».Numerics.cubicNewton_sound`.
-/
def cubicSlopeInterval (A X : IntervalRat) : IntervalRat :=
  IntervalRat.sub (IntervalRat.mul (IntervalRat.singleton 3) (powerHigh X 2)) A

/--
Membership in the specified domain/enclosure: `3*x^2-a∈cubicSlopeInterval A X`.

Use: `«2610.05164v2».Numerics.cubicNewton_sound` uses this assertion to establish membership in
the specified domain/enclosure: `positiveCubic a b∈J`.

Article: 2610.05164v2, Lemma 19 via `«2610.05164v2».Numerics.cubicNewton_sound`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.mem_powerHigh` with the arguments
shown in the proof.
-/
theorem mem_cubicSlopeInterval {A X : IntervalRat} {a x : ℝ} (ha : a∈A) (hx : x∈X) :
    3*x^2-a∈cubicSlopeInterval A X :=
  IntervalRat.mem_sub (IntervalRat.mem_mul (IntervalRat.mem_singleton 3) (mem_powerHigh hx 2)) ha

/--
Defines `cubicResidualInterval` of type `IntervalRat` by `IntervalRat.sub (IntervalRat.sub
(IntervalRat.singleton (m^3)) (IntervalRat.mul A (IntervalRat.singleton m))) B`.

Use: `«2610.05164v2».Numerics.cubicNewton` uses this definition in the displayed construction
of `cubicNewton`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 19 via `«2610.05164v2».Numerics.cubicNewton_sound`.
-/
def cubicResidualInterval (A B : IntervalRat) (m : ℚ) : IntervalRat :=
  IntervalRat.sub (IntervalRat.sub (IntervalRat.singleton (m^3))
    (IntervalRat.mul A (IntervalRat.singleton m))) B

/--
Membership in the specified domain/enclosure: `(m:ℝ)^3-a*m-b∈cubicResidualInterval A B m`.

Use: `«2610.05164v2».Numerics.cubicNewton_sound` uses this assertion to establish membership in
the specified domain/enclosure: `positiveCubic a b∈J`.

Article: 2610.05164v2, Lemma 19 via `«2610.05164v2».Numerics.cubicNewton_sound`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem mem_cubicResidualInterval {A B : IntervalRat} {a b : ℝ} (ha : a∈A) (hb : b∈B) (m : ℚ) :
    (m:ℝ)^3-a*m-b∈cubicResidualInterval A B m := by
  apply IntervalRat.mem_sub _ hb
  apply IntervalRat.mem_sub _ (IntervalRat.mem_mul ha (IntervalRat.mem_singleton m))
  simp only [IntervalRat.mem_def,IntervalRat.singleton,Rat.cast_pow,le_refl,and_self]

/--
Defines `cubicNewton` of type `Option IntervalRat` by `if _hm : X.lo≤m ∧ m≤X.hi then let D :=
cubicSlopeInterval A X if hd : 0<D.lo then let dn : IntervalRat.IntervalRatNonzero := ⟨D,fun h
=> (not_le_of_gt hd) h.1⟩ some (IntervalRat.sub (IntervalRat.singleton m) (IntervalRat.mul
(cubicResidualInterval A B m) (IntervalRat.invNonzero dn))) else none else none`.

Use: `«2610.05164v2».Numerics.cubicNewton_sound` uses this definition to establish membership
in the specified domain/enclosure: `positiveCubic a b∈J`.

Article: 2610.05164v2, Lemma 19 via `«2610.05164v2».Numerics.cubicNewton_sound`.
-/
def cubicNewton (A B X : IntervalRat) (m : ℚ) : Option IntervalRat :=
  if _hm : X.lo≤m ∧ m≤X.hi then
    let D := cubicSlopeInterval A X
    if hd : 0<D.lo then
      let dn : IntervalRat.IntervalRatNonzero := ⟨D,fun h => (not_le_of_gt hd) h.1⟩
      some (IntervalRat.sub (IntervalRat.singleton m)
        (IntervalRat.mul (cubicResidualInterval A B m) (IntervalRat.invNonzero dn)))
    else none
  else none

/--
Membership in the specified domain/enclosure: `positiveCubic a b∈J`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 19.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.mem_cubicSlopeInterval`,
`«2610.05164v2».Numerics.positiveCubic_newton`,
`«2610.05164v2».Numerics.mem_cubicResidualInterval` with the arguments shown in the proof.
-/
theorem cubicNewton_sound {A B X J : IntervalRat} {m : ℚ}
    (hcheck : cubicNewton A B X m=some J) {a b : ℝ} (ha : a∈A) (hb : b∈B)
    (hapos : 0≤a) (hbpos : 0<b) (hz : positiveCubic a b∈X) : positiveCubic a b∈J := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.mem_cubicSlopeInterval`,
  -- `«2610.05164v2».Numerics.positiveCubic_newton`,
  -- `«2610.05164v2».Numerics.mem_cubicResidualInterval` with the arguments shown in the proof.
  unfold cubicNewton at hcheck
  split at hcheck
  next hm =>
    dsimp only at hcheck
    split at hcheck
    next hd =>
      have hmreal : (m:ℝ)∈Icc (X.lo:ℝ) X.hi := by
        change (X.lo:ℝ)≤m ∧ (m:ℝ)≤X.hi
        exact_mod_cast hm
      have hpos : ∀ x∈Icc (X.lo:ℝ) X.hi,0<3*x^2-a := by
        intro x hx
        have hdreal : (0:ℝ)<(cubicSlopeInterval A X).lo := by exact_mod_cast hd
        exact hdreal.trans_le (mem_cubicSlopeInterval ha hx).1
      obtain ⟨ξ,hξ,he⟩ := positiveCubic_newton hapos hbpos hz hmreal hpos
      have hden := mem_cubicSlopeInterval ha hξ
      cases Option.some.inj hcheck
      rw [he,div_eq_mul_inv]
      exact IntervalRat.mem_sub (IntervalRat.mem_singleton m)
        (IntervalRat.mem_mul (mem_cubicResidualInterval ha hb m)
          (IntervalRat.mem_invNonzero hden (ne_of_gt (hpos ξ hξ))))
    next => contradiction
  next => contradiction

end «2610.05164v2».Numerics
