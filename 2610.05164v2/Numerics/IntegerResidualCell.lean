import «2610.05164v2».Numerics.IntegerReferenceResidual
import «2610.05164v2».Numerics.IntegerTaylorModel

/-!
Article: 2610.05164v2, Section 4.1.
A complete local certificate for a reference filter.
Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` feeds
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.error` (error).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate
open Set Polynomial «2610.05164v2».DualCertificate «2610.05164v2».Calibration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `Bounds.lower` of type `ℚ` by `(B.lo:ℚ)/s`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Bounds.real_abs` uses this definition to
establish the stated quantitative bound `|x|≤(B.magnitude s:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Bounds.lower (B : Bounds) (s : Nat) : ℚ := (B.lo:ℚ)/s
/--
Defines `Bounds.upper` of type `ℚ` by `(B.hi:ℚ)/s`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Bounds.real_abs` uses this definition to
establish the stated quantitative bound `|x|≤(B.magnitude s:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Bounds.upper (B : Bounds) (s : Nat) : ℚ := (B.hi:ℚ)/s
/--
Defines `Bounds.magnitude` of type `ℚ` by `((max (-B.lo) B.hi : Int):ℚ)/s`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Bounds.real_abs` uses this definition to
establish the stated quantitative bound `|x|≤(B.magnitude s:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Bounds.magnitude (B : Bounds) (s : Nat) : ℚ := ((max (-B.lo) B.hi : Int):ℚ)/s

/--
Membership in the specified domain/enclosure: `x∈Icc (B.lower s:ℝ) (B.upper s:ℝ)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Summary.sound` uses this
assertion to prove the bound `0≤p ∧ |R.normalizedVelocity
t*(R.k*(t*R.normalizedRoot t)^2-2*p-σ*p^2)-pd|≤(η:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Bounds.real_mem {s : Nat} (hs : 0<s) {B : Bounds} {x : ℝ}
    (hx : B.Mem s x) : x∈Icc (B.lower s:ℝ) (B.upper s:ℝ) := by
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  simp only [lower,upper,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  exact ⟨(div_le_iff₀ hs').mpr (by nlinarith [hx.1]),
    (le_div_iff₀ hs').mpr (by nlinarith [hx.2])⟩

/--
The stated quantitative bound `|x|≤(B.magnitude s:ℝ)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Summary.sound` uses this bound to
establish the stated quantitative bound `0≤p ∧ |R.normalizedVelocity t*(R.k*(t*R.normalizedRoot
t)^2-2*p-σ*p^2)-pd|≤(η:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Bounds.real_mem` with the arguments shown in the
proof.
-/
theorem Bounds.real_abs {s : Nat} (hs : 0<s) {B : Bounds} {x : ℝ}
    (hx : B.Mem s x) : |x|≤(B.magnitude s:ℝ) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.Bounds.real_mem`
  -- with the arguments shown in the proof.
  have hh := B.real_mem hs hx
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  rw [abs_le]
  simp only [lower,upper,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] at hh
  simp only [magnitude,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  simp only [Int.cast_max,Int.cast_neg]
  constructor
  · have hm : -(B.lo:ℝ)/s≤max (-(B.lo:ℝ)) (B.hi:ℝ)/s :=
      div_le_div_of_nonneg_right (le_max_left _ _) hs'.le
    rw [neg_div] at hm
    linarith [hh.1]
  · exact hh.2.trans (div_le_div_of_nonneg_right (le_max_right _ _) hs'.le)

namespace ResidualCell
/--
Scaled reference-cell data or computed residual summaries. Polynomial coefficients and interval
bounds are candidate data; the row checker and its actual-ODE bridge supply acceptance.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check` uses this record of data
and proof obligations in the displayed construction of `check`. Its inputs and component
formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure Row where
  /-- Left endpoint in common scaled integer time coordinates. -/
  start : Int
  /-- Nonnegative cell width in the same time scale. -/
  width : Nat
  /-- Scaled chart step parameter used by the row model. -/
  step : Nat
  /-- Whether this row uses the reflected/right chart. -/
  reflected : Bool
  /-- Scaled polynomial coefficients for the reference filter approximation, or its interval enclosure in a range result. -/
  p : List Int
  /-- Scaled polynomial coefficients for the cubic-root approximation, or its interval enclosure in a range result. -/
  z : List Int
  /-- Root-approximation uncertainty budget. -/
  delta : ℚ
  /-- Retained polynomial degree in residual evaluation. -/
  degree : Nat
  /-- Optional node enclosures that the checker verifies rather than assumes. -/
  checkpoints : List (Option (List Bounds))
  deriving Repr, DecidableEq

/--
Defines `coordinate` of type `List Int` by `if r.reflected then [2*s-r.start,-(r.width:Int)]
else [r.start,r.width]`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.inputs` uses this definition in
the displayed construction of `inputs`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def coordinate (s : Nat) (r : Row) : List Int :=
  if r.reflected then [2*s-r.start,-(r.width:Int)] else [r.start,r.width]
/--
Defines `inputs` of type `List (List Bounds)` by `[Poly.exactBounds (coordinate s
r),[piB],Poly.exactBounds r.z, Poly.exactBounds r.p,Poly.scaleNat r.step (Poly.derivative
(Poly.exactBounds r.p))]`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` uses this definition
to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def inputs (s : Nat) (piB : Bounds) (r : Row) : List (List Bounds) :=
  [Poly.exactBounds (coordinate s r),[piB],Poly.exactBounds r.z,
    Poly.exactBounds r.p,Poly.scaleNat r.step (Poly.derivative (Poly.exactBounds r.p))]
/--
Defines `values` by pattern matching with result type `Nat → ℝ[X]`. The displayed branches
determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` uses this definition
to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def values (s : Nat) (r : Row) : Nat → ℝ[X]
  | 0 => Poly.exactPolynomial s (coordinate s r)
  | 1 => C Real.pi
  | 2 => Poly.exactPolynomial s r.z
  | 3 => Poly.exactPolynomial s r.p
  | 4 => C (r.step:ℝ)*(Poly.exactPolynomial s r.p).derivative
  | _ => 0

/--
The precise assertion is `Poly.Encloses s (inputs s piB r) (values s r)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.sourceRange_sound` uses this
assertion to prove the bound `result.Mem s (source.value (fun j =>
(values s r j).eval x))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Poly.exactBounds_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.scaleNat_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.derivative_sound` with the arguments shown in
the proof.
-/
theorem inputs_sound {s : Nat} (hs : 0<s) {piB : Bounds}
    (hpi : piB.Mem s Real.pi) (r : Row) : Poly.Encloses s (inputs s piB r) (values s r) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.exactBounds_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.scaleNat_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.derivative_sound` with the arguments
  -- shown in the proof.
  intro i I hi
  cases i with
  | zero =>
    have h : I=Poly.exactBounds (coordinate s r) := by simpa [inputs] using hi.symm
    subst I
    exact Poly.exactBounds_sound hs _
  | succ i =>
    cases i with
    | zero =>
      have h : I=[piB] := by simpa [inputs] using hi.symm
      subst I
      simpa [values] using Poly.Rep.cons hpi (Poly.Rep.nil (s := s))
    | succ i =>
      cases i with
      | zero =>
        have h : I=Poly.exactBounds r.z := by simpa [inputs] using hi.symm
        subst I
        exact Poly.exactBounds_sound hs _
      | succ i =>
        cases i with
        | zero =>
          have h : I=Poly.exactBounds r.p := by simpa [inputs] using hi.symm
          subst I
          exact Poly.exactBounds_sound hs _
        | succ i =>
          cases i with
          | zero =>
            have h : I=Poly.scaleNat r.step (Poly.derivative (Poly.exactBounds r.p)) := by
              simpa [inputs] using hi.symm
            subst I
            exact Poly.scaleNat_sound (Poly.derivative_sound (Poly.exactBounds_sound hs _))
          | succ i => simp [inputs] at hi

/--
Scaled reference-cell data or computed residual summaries. Polynomial coefficients and interval
bounds are candidate data; the row checker and its actual-ODE bridge supply acceptance.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check` uses this record of data
and proof obligations in the displayed construction of `check`. Its inputs and component
formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure Summary where
  /-- Enclosure of the positive ground parameter. -/
  k : Bounds
  /-- Enclosure of the residual denominator; acceptance requires its needed sign. -/
  den : Bounds
  /-- Enclosure of the positive cubic root. -/
  root : Bounds
  /-- Enclosure of the residual scaling factor. -/
  factor : Bounds
  /-- Enclosure of the polynomial ODE residual. -/
  ode : Bounds
  /-- Scaled polynomial coefficients for the cubic-root approximation, or its interval enclosure in a range result. -/
  z : Bounds
  /-- Scaled polynomial coefficients for the reference filter approximation, or its interval enclosure in a range result. -/
  p : Bounds
  deriving Repr, DecidableEq

/--
Defines `outputRange` of type `Option Bounds` by `do Poly.range s ⟨0,s⟩ (← out[i]?)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` uses this definition
to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def outputRange (s : Nat) (out : List (List Bounds)) (i : Nat) : Option Bounds := do
  Poly.range s ⟨0,s⟩ (← out[i]?)

/--
Defines `summarize` of type `Option Summary` by `do let out ← Poly.Taylor.evalProgram s
r.degree (inputs s piB r) r.checkpoints ops return ⟨← outputRange s out 72, ← outputRange s out
30, ← outputRange s out 16, ← outputRange s out 12, ← outputRange s out 0, ← Poly.range s ⟨0,s⟩
(Poly.exactBounds r.z), ← Poly.range s ⟨0,s⟩ (Poly.exactBounds r.p)⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check` uses this definition in
the displayed construction of `check`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def summarize (s : Nat) (ops : List Op) (piB : Bounds) (r : Row) : Option Summary := do
  let out ← Poly.Taylor.evalProgram s r.degree (inputs s piB r) r.checkpoints ops
  return ⟨← outputRange s out 72, ← outputRange s out 30,
    ← outputRange s out 16, ← outputRange s out 12, ← outputRange s out 0,
    ← Poly.range s ⟨0,s⟩ (Poly.exactBounds r.z),
    ← Poly.range s ⟨0,s⟩ (Poly.exactBounds r.p)⟩

/--
Defines `Summary.check` of type `Bool` by `decide ( 0<s ∧ 0<b.den.lower s ∧ 0<b.k.lower s ∧
0<b.z.lower s ∧ 0≤δ ∧ δ≤b.z.lower s/2 ∧ 0≤b.p.lower s ∧ 0≤η ∧ 0≤b.factor.magnitude s ∧
b.root.magnitude s≤δ*(b.den.lower s*b.k.lower s*(b.z.lower s)^2) ∧ b.ode.magnitude
s+b.factor.magnitude s*δ*(2*b.z.upper s+δ)≤ η*(b.k.lower s*(b.z.lower s)^2/6))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check` uses this definition in
the displayed construction of `check`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Summary.check (s : Nat) (δ η : ℚ) (b : Summary) : Bool := decide (
  0<s ∧ 0<b.den.lower s ∧ 0<b.k.lower s ∧ 0<b.z.lower s ∧
  0≤δ ∧ δ≤b.z.lower s/2 ∧ 0≤b.p.lower s ∧ 0≤η ∧ 0≤b.factor.magnitude s ∧
  b.root.magnitude s≤δ*(b.den.lower s*b.k.lower s*(b.z.lower s)^2) ∧
  b.ode.magnitude s+b.factor.magnitude s*δ*(2*b.z.upper s+δ)≤
    η*(b.k.lower s*(b.z.lower s)^2/6))

/--
Defines `check` of type `Bool` by `decide (0<r.width ∧ r.width*r.step=s) && ((summarize s ops
piB r).any (Summary.check s r.delta η))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` uses this definition
to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def check (s : Nat) (ops : List Op) (piB : Bounds) (η : ℚ) (r : Row) : Bool :=
  decide (0<r.width ∧ r.width*r.step=s) &&
    ((summarize s ops piB r).any (Summary.check s r.delta η))

/--
The precise assertion is `result.Mem s ((v i).eval x)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound` with the arguments shown in the
proof.
-/
theorem outputRange_sound {s : Nat} (hs : 0<s) {out : List (List Bounds)}
    {v : Nat → ℝ[X]} (hv : Poly.Encloses s out v) {i : Nat} {result : Bounds}
    (he : outputRange s out i=some result) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    result.Mem s ((v i).eval x) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound`
  -- with the arguments shown in the proof.
  obtain ⟨p,hp,hr⟩ : ∃ p, out[i]?=some p ∧ Poly.range s ⟨0,s⟩ p=some result := by
    simpa only [outputRange,Option.bind_eq_bind,Option.bind_eq_some_iff] using he
  apply Poly.range_sound hs (hv i p hp) ?_ hr
  constructor <;> dsimp [Bounds.Mem]
  · simpa using mul_nonneg (Nat.cast_nonneg s) hx.1
  · simpa using mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg s)

/--
The stated quantitative bound `result.Mem s (source.value (fun j => (values s r j).eval x))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` uses this identity
to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.source_enclosed`,
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.inputs_sound` with the arguments shown
in the proof.
-/
theorem sourceRange_sound {s : Nat} (hs : 0<s) {out : List (List Bounds)}
    {ops : List Op} {piB : Bounds} {r : Row} (hpi : piB.Mem s Real.pi)
    (he : Poly.Taylor.evalProgram s r.degree (inputs s piB r) r.checkpoints ops=some out)
    {i : Nat} {source : Expr} (hsource : codeExpressionCheck ops i source=true)
    {result : Bounds} (hr : outputRange s out i=some result)
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    result.Mem s (source.value (fun j => (values s r j).eval x)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.source_enclosed`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.inputs_sound` with the arguments
  -- shown in the proof.
  obtain ⟨p,hp,hrange⟩ : ∃ p, out[i]?=some p ∧ Poly.range s ⟨0,s⟩ p=some result := by
    simpa only [outputRange,Option.bind_eq_bind,Option.bind_eq_some_iff] using hr
  exact Poly.Taylor.source_enclosed hs hx ops (inputs_sound hs hpi r) he hsource hp hrange

/--
Exact identity `(fun j => (values s r j).eval x)=ResidualExpr.values ((values s r 0).eval x)
((values s r 2).eval x) ((values s r 3).eval x) ((values s r 4).eval x)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` rewrites with this
identity to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem values_eval (s : Nat) (r : Row) (x : ℝ) :
    (fun j => (values s r j).eval x)=ResidualExpr.values
      ((values s r 0).eval x) ((values s r 2).eval x)
      ((values s r 3).eval x) ((values s r 4).eval x) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  funext i
  rcases i with _|i
  · rfl
  rcases i with _|i
  · simp [values,ResidualExpr.values]
  rcases i with _|i
  · rfl
  rcases i with _|i
  · rfl
  rcases i with _|i
  · rfl
  · simp [values,ResidualExpr.values]

/--
The stated quantitative bound `0≤p ∧ |R.normalizedVelocity t*(R.k*(t*R.normalizedRoot
t)^2-2*p-σ*p^2)-pd|≤(η:ℝ)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` uses this bound to
establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Bounds.real_mem`,
`«2610.05164v2».Numerics.ReferenceResidual.polynomial_residual_bound`,
`«2610.05164v2».Numerics.IntegerCertificate.Bounds.real_abs` with the arguments shown in the
proof.
-/
theorem Summary.sound {s : Nat} {b : Summary} {δ η : ℚ}
    (hc : b.check s δ η=true) (R : ReferenceData) {σ t z p pd d : ℝ}
    (ht : t∈Icc (0:ℝ) 1)
    (hk : b.k.Mem s R.k) (hd : b.den.Mem s d) (hz : b.z.Mem s z)
    (hp : b.p.Mem s p)
    (hr : b.root.Mem s (d*(R.k*z^3-3*t*(2-t^3)*z-2*R.b (t^3*(2-t^3))*(2-t^3))))
    (ho : b.ode.Mem s (R.k*(3*t^2-pd)*z^2+pd*t*(2-t^3)-6*p-3*σ*p^2))
    (hf : b.factor.Mem s (R.k*(3*t^2-pd))) :
    0≤p ∧ |R.normalizedVelocity t*(R.k*(t*R.normalizedRoot t)^2-2*p-σ*p^2)-pd|≤(η:ℝ) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.Bounds.real_mem`,
  -- `«2610.05164v2».Numerics.ReferenceResidual.polynomial_residual_bound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Bounds.real_abs` with the arguments shown in
  -- the proof.
  obtain ⟨hs,hD,hK,hL,hδ,hδl,hp0,hη,hf0,hroot,hbudget⟩ := of_decide_eq_true hc
  have hDr : (0:ℝ)<(b.den.lower s:ℝ) := by exact_mod_cast hD
  have hKr : (0:ℝ)<(b.k.lower s:ℝ) := by exact_mod_cast hK
  have hLr : (0:ℝ)<(b.z.lower s:ℝ) := by exact_mod_cast hL
  have hδr : (0:ℝ)≤(δ:ℝ) := by exact_mod_cast hδ
  have hδlr : (δ:ℝ)≤(b.z.lower s:ℝ)/2 := by exact_mod_cast hδl
  have hp0r : (0:ℝ)≤(b.p.lower s:ℝ) := by exact_mod_cast hp0
  have hηr : (0:ℝ)≤(η:ℝ) := by exact_mod_cast hη
  have hf0r : (0:ℝ)≤(b.factor.magnitude s:ℝ) := by exact_mod_cast hf0
  have hrootr : (b.root.magnitude s:ℝ)≤
      (δ:ℝ)*((b.den.lower s:ℝ)*(b.k.lower s:ℝ)*(b.z.lower s:ℝ)^2) := by
    exact_mod_cast hroot
  have hbudgetr : (b.ode.magnitude s:ℝ)+(b.factor.magnitude s:ℝ)*(δ:ℝ)*
      (2*(b.z.upper s:ℝ)+(δ:ℝ))≤(η:ℝ)*((b.k.lower s:ℝ)*(b.z.lower s:ℝ)^2/6) := by
    exact_mod_cast hbudget
  have hd' := Bounds.real_mem hs hd
  refine ⟨hp0r.trans (Bounds.real_mem hs hp).1,?_⟩
  apply ReferenceResidual.polynomial_residual_bound R ht (hDr.trans_le hd'.1)
    hKr (Bounds.real_mem hs hk).1 hLr (Bounds.real_mem hs hz) hδr hδlr
    (Bounds.real_abs hs hr) ?_ (Bounds.real_abs hs ho) (Bounds.real_abs hs hf)
    hf0r hηr hbudgetr
  exact hrootr.trans (by gcongr; exact hd'.1)

/--
The complete local acceptance theorem: all numerical premises are discharged by the executable
certificate predicate.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.error` uses this bound to
establish the stated quantitative bound `|y t-r.approx s t|≤e+(η:ℝ)*(t-r.left s)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.sourceRange_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.values_basic`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound` with the arguments shown in the
proof.
-/
theorem check_sound {s : Nat} (hs : 0<s) {ops : List Op} {piB : Bounds}
    (hpi : piB.Mem s Real.pi) (R : RationalReference) (σ η : ℚ)
    (shapeK : codeExpressionCheck ops 72 ResidualExpr.k=true)
    (shapeD : codeExpressionCheck ops 30 (ResidualExpr.profileParts R).1=true)
    (shapeRoot : codeExpressionCheck ops 16 (ResidualExpr.rootResidual R)=true)
    (shapeFactor : codeExpressionCheck ops 12 ResidualExpr.factor=true)
    (shapeODE : codeExpressionCheck ops 0 (ResidualExpr.odeResidual σ)=true)
    {r : Row} (hc : check s ops piB η r=true) {x : ℝ} (hx : x∈Icc (0:ℝ) 1)
    (ht : (values s r 0).eval x∈Icc (0:ℝ) 1) :
    0≤(values s r 3).eval x ∧
    |(ReferenceJetSource.referenceData R).normalizedVelocity ((values s r 0).eval x)*
      ((Real.pi^2/4)*(((values s r 0).eval x)*
        (ReferenceJetSource.referenceData R).normalizedRoot ((values s r 0).eval x))^2-
        2*(values s r 3).eval x-(σ:ℝ)*((values s r 3).eval x)^2)-
      (values s r 4).eval x|≤(η:ℝ) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.sourceRange_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.values_basic`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound` with the arguments shown in
  -- the proof.
  have hboth : decide (0<r.width ∧ r.width*r.step=s)=true ∧
      (summarize s ops piB r).any (Summary.check s r.delta η)=true := by
    simpa only [check,Bool.and_eq_true] using hc
  have hcheck := hboth.2
  cases he : summarize s ops piB r with
  | none => simp [he] at hcheck
  | some b =>
    have hb : b.check s r.delta η=true := by simpa [he] using hcheck
    obtain ⟨out,hout,K,hK,D,hD,N,hN,F,hF,E,hE,Z,hZ,P,hP,heq⟩ :
        ∃ out, Poly.Taylor.evalProgram s r.degree (inputs s piB r) r.checkpoints ops=some out ∧
        ∃ K, outputRange s out 72=some K ∧
        ∃ D, outputRange s out 30=some D ∧
        ∃ N, outputRange s out 16=some N ∧
        ∃ F, outputRange s out 12=some F ∧
        ∃ E, outputRange s out 0=some E ∧
        ∃ Z, Poly.range s ⟨0,s⟩ (Poly.exactBounds r.z)=some Z ∧
        ∃ P, Poly.range s ⟨0,s⟩ (Poly.exactBounds r.p)=some P ∧
        Summary.mk K D N F E Z P=b := by
      simpa only [summarize,Option.bind_eq_bind,Option.bind_eq_some_iff,
        Option.pure_def,Option.some.injEq] using he
    subst b
    have hK' := sourceRange_sound hs hpi hout shapeK hK hx
    have hD' := sourceRange_sound hs hpi hout shapeD hD hx
    have hN' := sourceRange_sound hs hpi hout shapeRoot hN hx
    have hF' := sourceRange_sound hs hpi hout shapeFactor hF hx
    have hE' := sourceRange_sound hs hpi hout shapeODE hE hx
    rw [values_eval] at hK' hD' hN' hF' hE'
    have hbasic := ResidualExpr.values_basic ((values s r 0).eval x)
      ((values s r 2).eval x) ((values s r 3).eval x) ((values s r 4).eval x)
    rw [hbasic.2.2.2.2.1] at hK'
    rw [ResidualExpr.rootResidual_value R ht] at hN'
    rw [ResidualExpr.factor_value] at hF'
    rw [ResidualExpr.odeResidual_value] at hE'
    have hxi : (⟨0,s⟩:Bounds).Mem s x := by
      constructor <;> dsimp [Bounds.Mem]
      · simpa using mul_nonneg (Nat.cast_nonneg s) hx.1
      · simpa using mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg s)
    have hZ' := Poly.range_sound hs (Poly.exactBounds_sound hs r.z) hxi hZ
    have hP' := Poly.range_sound hs (Poly.exactBounds_sound hs r.p) hxi hP
    exact Summary.sound hb (ReferenceJetSource.referenceData R) ht hK' hD' hZ' hP' hN' hE' hF'

end ResidualCell
end «2610.05164v2».Numerics.IntegerCertificate
