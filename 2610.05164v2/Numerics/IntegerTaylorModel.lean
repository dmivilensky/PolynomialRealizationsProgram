import «2610.05164v2».Numerics.IntegerConvolution

/-!
Article: 2610.05164v2, Section 4.1.
Bounded-degree interval polynomials.
Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.source_enclosed` feeds
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.sourceRange_sound` (source Range sound).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate.Poly
open Polynomial Set
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `At` of type `Prop` by `∃ p : ℝ[X], Rep s bs p ∧ p.eval x=value`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.Encloses` uses this definition in
the displayed construction of `Encloses`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def At (s : Nat) (bs : List Bounds) (x value : ℝ) : Prop :=
  ∃ p : ℝ[X], Rep s bs p ∧ p.eval x=value

/--
The precise assertion is `At s bs x (p.eval x)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalOp_sound` uses this assertion
to establish `At s out x (op.value v)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem Rep.at {s : Nat} {bs : List Bounds} {p : ℝ[X]}
    (h : Rep s bs p) (x : ℝ) : At s bs x (p.eval x) := ⟨p,h,rfl⟩

/--
Constructs witnesses with the exact properties `∃ lo hi : ℝ[X], Rep s (bs.take n) lo ∧ Rep s
(bs.drop n) hi ∧ p=lo+X^n*hi`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.truncate_sound` uses this identity to
establish the precise assertion is `At s out x v`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `n` while keeping `bs p` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem split_sound {s : Nat} {bs : List Bounds} {p : ℝ[X]} (h : Rep s bs p) (n : Nat) :
    ∃ lo hi : ℝ[X], Rep s (bs.take n) lo ∧ Rep s (bs.drop n) hi ∧ p=lo+X^n*hi := by
  -- Induct on `n` while keeping `bs p` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction n generalizing bs p with
  | zero => exact ⟨0,p,Rep.nil,h,by simp⟩
  | succ n ih =>
    cases h with
    | nil => exact ⟨0,0,Rep.nil,Rep.nil,by simp⟩
    | @cons b bs c p hc hp =>
      obtain ⟨lo,hi,hlo,hhi,he⟩ := ih hp
      refine ⟨C c+X*lo,hi,Rep.cons hc hlo,hhi,?_⟩
      rw [he,pow_succ]
      ring

/--
Defines `truncate` of type `Option (List Bounds)` by `if bs.length≤n then some bs else do let
tail ← range s ⟨0,s⟩ (bs.drop n) let rest ← mulB s ⟨0,s⟩ tail return add [rest] (bs.take n)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalOp_sound` uses this definition
to establish `At s out x (op.value v)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def truncate (s n : Nat) (bs : List Bounds) : Option (List Bounds) :=
  if bs.length≤n then some bs else do
    let tail ← range s ⟨0,s⟩ (bs.drop n)
    let rest ← mulB s ⟨0,s⟩ tail
    return add [rest] (bs.take n)

/--
The precise assertion is `At s out x v`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalOp_sound` uses this assertion
to establish `At s out x (op.value v)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Separate `bs.length≤n` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem truncate_sound {s n : Nat} (hs : 0<s) {bs out : List Bounds} {x v : ℝ}
    (hx : x∈Icc (0:ℝ) 1) (h : At s bs x v)
    (he : truncate s n bs=some out) : At s out x v := by
  -- Separate `bs.length≤n` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  obtain ⟨p,hp,hv⟩ := h
  by_cases hlen : bs.length≤n
  · have heq : bs=out := by simpa [truncate,hlen] using he
    subst out
    exact ⟨p,hp,hv⟩
  · obtain ⟨tail,htail,rest,hrest,hout⟩ :
        ∃ tail, range s ⟨0,s⟩ (bs.drop n)=some tail ∧
        ∃ rest, mulB s ⟨0,s⟩ tail=some rest ∧ add [rest] (bs.take n)=out := by
      simpa only [truncate,hlen,↓reduceIte,Option.bind_eq_bind,Option.bind_eq_some_iff,
        Option.pure_def,Option.some.injEq] using he
    obtain ⟨lo,hi,hlo,hhi,hpoly⟩ := split_sound hp n
    have hmem (y : ℝ) (hy : y∈Icc (0:ℝ) 1) : (⟨0,s⟩:Bounds).Mem s y := by
      constructor <;> dsimp [Bounds.Mem]
      · simpa using mul_nonneg (Nat.cast_nonneg s) hy.1
      · simpa using mul_le_mul_of_nonneg_left hy.2 (Nat.cast_nonneg s)
    have hpow : x^n∈Icc (0:ℝ) 1 := ⟨pow_nonneg hx.1 _,pow_le_one₀ hx.1 hx.2⟩
    have htail' := range_sound hs hhi (hmem x hx) htail
    have hrest' := mulB_sound hs (hmem (x^n) hpow) htail' hrest
    have hc : Rep s [rest] (C (x^n*hi.eval x)) := by
      simpa using Rep.cons hrest' (Rep.nil (s := s))
    subst out
    refine ⟨C (x^n*hi.eval x)+lo,add_sound hc hlo,?_⟩
    rw [← hv,hpoly]
    simp only [eval_add,eval_C,eval_mul,eval_pow,eval_X]
    ring

namespace Taylor
/--
Defines `box` of type `Bounds` by `⟨lo,lo+width⟩`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceTrajectory.covers` uses this definition to
establish constructs witnesses with the exact properties `∃ r∈rows, t∈Icc (r.left scale)
(r.right scale)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def box (lo width : Int) : Bounds := ⟨lo,lo+width⟩

/--
A checkpoint cuts repeated reduction of a shared expression. Its entire model is recomputed and
compared before the supplied value enters the stack.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.checkpoint_sound` rewrites with
this definition to establish `At s out x v`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def checkpoint (computed : List Bounds) : Option (List Bounds) → Option (List Bounds)
  | none => some computed
  | some proposed => if computed=proposed then some proposed else none

/--
The precise assertion is `At s out x v`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalProgram_sound` uses this
assertion to establish `Encloses s out x (codeValue v ops)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Separate `computed=proposed` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem checkpoint_sound {s : Nat} {computed out : List Bounds} {cp : Option (List Bounds)}
    {x v : ℝ} (hc : At s computed x v) (he : checkpoint computed cp=some out) : At s out x v := by
  -- Separate `computed=proposed` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  cases cp with
  | none =>
    have h : computed=out := by simpa [checkpoint] using he
    simpa [h] using hc
  | some proposed =>
    by_cases h : computed=proposed
    · have hh : proposed=out := by simpa [checkpoint,h] using he
      simpa [h,hh] using hc
    · simp [checkpoint,h] at he

/--
Defines `evalOp` by pattern matching with result type `Op → Option (List Bounds)`. The
displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalOp_sound` rewrites with this
definition to establish `At s out x (op.value v)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def evalOp (s n : Nat) (stack : List (List Bounds)) : Op → Option (List Bounds)
  | .mul i j => do truncate s n (trim (convolution s (← stack[i]?) (← stack[j]?)))
  | op => Poly.evalOp s stack op

/--
Defines `evalProgram` by pattern matching with result type `List (List Bounds) → List (Option
(List Bounds)) → List Op → Option (List (List Bounds))`. The displayed branches determine the
recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalProgram_sound` rewrites with
this definition to establish `Encloses s out x (codeValue v ops)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def evalProgram (s n : Nat) : List (List Bounds) → List (Option (List Bounds)) →
    List Op → Option (List (List Bounds))
  | stack, [], [] => some stack
  | stack, cp::cps, op::ops => do
    let computed ← evalOp s n stack op
    let out ← checkpoint computed cp
    evalProgram s n (out::stack) cps ops
  | _, _, _ => none

/--
Defines `Encloses` of type `Prop` by `∀ i I, stack[i]?=some I → At s I x (v i)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.source_enclosed` uses this
definition to prove the bound `result.Mem s (source.value (fun j => (v
j).eval x))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Encloses (s : Nat) (stack : List (List Bounds)) (x : ℝ) (v : Nat → ℝ) : Prop :=
  ∀ i I, stack[i]?=some I → At s I x (v i)

/--
The precise assertion is `At s out x (op.value v)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalProgram_sound` uses this
assertion to establish `Encloses s out x (codeValue v ops)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.Poly.Rep.at`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.constant_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.add_sound` with the arguments shown in the
proof.
-/
theorem evalOp_sound {s n : Nat} (hs : 0<s) {stack : List (List Bounds)}
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) {v : Nat → ℝ} (hv : Encloses s stack x v)
    {op : Op} {out : List Bounds} (he : evalOp s n stack op=some out) :
    At s out x (op.value v) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.Poly.Rep.at`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.constant_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.add_sound` with the arguments shown in
  -- the proof.
  cases op with
  | literal a b => simpa [Op.value] using (constant_sound hs he).at x
  | copy i => exact hv i out he
  | add i j =>
    obtain ⟨a,ha,b,hb,hout⟩ : ∃ a, stack[i]?=some a ∧
        ∃ b, stack[j]?=some b ∧ add a b=out := by
      simpa only [evalOp,Poly.evalOp,Option.bind_eq_bind,Option.bind_eq_some_iff,
        Option.pure_def,Option.some.injEq] using he
    obtain ⟨p,hp,hpval⟩ := hv i a ha
    obtain ⟨q,hq,hqval⟩ := hv j b hb
    subst out
    exact ⟨p+q,add_sound hp hq,by simp [Op.value,hpval,hqval]⟩
  | neg i =>
    obtain ⟨a,ha,hout⟩ : ∃ a, stack[i]?=some a ∧ neg a=out := by
      simpa only [evalOp,Poly.evalOp,Option.bind_eq_bind,Option.bind_eq_some_iff,
        Option.pure_def,Option.some.injEq] using he
    obtain ⟨p,hp,hpval⟩ := hv i a ha
    subst out
    exact ⟨-p,neg_sound hp,by simp [Op.value,hpval]⟩
  | mul i j =>
    obtain ⟨a,ha,b,hb,hout⟩ : ∃ a, stack[i]?=some a ∧
        ∃ b, stack[j]?=some b ∧ truncate s n (trim (convolution s a b))=some out := by
      simpa only [evalOp,Option.bind_eq_bind,Option.bind_eq_some_iff] using he
    obtain ⟨p,hp,hpval⟩ := hv i a ha
    obtain ⟨q,hq,hqval⟩ := hv j b hb
    apply truncate_sound hs hx ?_ hout
    exact ⟨p*q,trim_sound hs (convolution_sound hs hp hq),by simp [Op.value,hpval,hqval]⟩
  | inv i => simp [evalOp,Poly.evalOp] at he
  | cubic i j => simp [evalOp,Poly.evalOp] at he

/--
The precise assertion is `Encloses s out x (codeValue v ops)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.source_enclosed` uses this
assertion to prove the bound `result.Mem s (source.value (fun j => (v
j).eval x))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `ops` while keeping `stack v cps` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem evalProgram_sound {s n : Nat} (hs : 0<s) {x : ℝ} (hx : x∈Icc (0:ℝ) 1)
    (ops : List Op) {stack out : List (List Bounds)} {cps : List (Option (List Bounds))}
    {v : Nat → ℝ} (hv : Encloses s stack x v) (he : evalProgram s n stack cps ops=some out) :
    Encloses s out x (codeValue v ops) := by
  -- Induct on `ops` while keeping `stack v cps` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ops generalizing stack v cps with
  | nil =>
    cases cps with
    | nil =>
      have h : stack=out := by simpa [evalProgram] using he
      subst out
      exact hv
    | cons cp cps => simp [evalProgram] at he
  | cons op ops ih =>
    cases cps with
    | nil => simp [evalProgram] at he
    | cons cp cps =>
      obtain ⟨a,ha,b,hb,hrest⟩ : ∃ a, evalOp s n stack op=some a ∧
          ∃ b, checkpoint a cp=some b ∧ evalProgram s n (b::stack) cps ops=some out := by
        simpa only [evalProgram,Option.bind_eq_bind,Option.bind_eq_some_iff] using he
      apply ih ?_ hrest
      intro i I hi
      cases i with
      | zero =>
        have h : b=I := by simpa using hi
        subst I
        exact checkpoint_sound (evalOp_sound hs hx hv ha) hb
      | succ i => exact hv i I (by simpa using hi)

/--
The stated quantitative bound `result.Mem s (source.value (fun j => (v j).eval x))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.sourceRange_sound` uses this
identity to prove the bound `result.Mem s (source.value (fun j =>
(values s r j).eval x))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.Poly.Rep.at`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalProgram_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound` with the arguments shown in the
proof.
-/
theorem source_enclosed {s n : Nat} (hs : 0<s) {x : ℝ} (hx : x∈Icc (0:ℝ) 1)
    (ops : List Op) {stack out : List (List Bounds)} {v : Nat → ℝ[X]}
    {cps : List (Option (List Bounds))}
    (hv : Poly.Encloses s stack v) (he : evalProgram s n stack cps ops=some out)
    {i : Nat} {source : Expr} (hsource : codeExpressionCheck ops i source=true)
    {pB : List Bounds} (hi : out[i]?=some pB) {result : Bounds}
    (hrange : range s ⟨0,s⟩ pB=some result) :
    result.Mem s (source.value (fun j => (v j).eval x)) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.Poly.Rep.at`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalProgram_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound` with the arguments shown in
  -- the proof.
  have hv' : Encloses s stack x (fun i => (v i).eval x) :=
    fun i I hi => (hv i I hi).at x
  obtain ⟨p,hp,hpval⟩ := evalProgram_sound hs hx ops hv' he i pB hi
  have hx' : (⟨0,s⟩:Bounds).Mem s x := by
    constructor <;> dsimp [Bounds.Mem]
    · simpa using mul_nonneg (Nat.cast_nonneg s) hx.1
    · simpa using mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg s)
  have h := range_sound hs hp hx' hrange
  rw [hpval] at h
  have hshape : codeExpression Expr.input ops i=source := of_decide_eq_true hsource
  have hvalue := codeExpression_value ops Expr.input (fun j => (v j).eval x) i
  simp only [Expr.value,hshape] at hvalue
  rwa [← hvalue] at h

end Taylor
end «2610.05164v2».Numerics.IntegerCertificate.Poly
