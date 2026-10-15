import «2610.05164v2».Numerics.ContactCheck
import «2610.05164v2».Numerics.ReferenceValueBounds

/-!
Article: 2610.05164v2, Section 4.1.
Contact Models.
Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.time_mem` feeds
`«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.Panel.actual_of_inputs` (actual of
inputs).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate
open Set Polynomial «2610.05164v2».Calibration «2610.05164v2».DualCertificate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `symmetricBox` of type `Bounds` by `⟨-radius,radius⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.symmetricBox_mem` uses this definition to
establish the precise assertion is `(symmetricBox radius).Mem s x`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def symmetricBox (radius : Int) : Bounds := ⟨-radius,radius⟩

/--
The precise assertion is `(symmetricBox radius).Mem s x`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.valueModel_sound` uses this assertion to
establish the precise assertion is `Poly.At s (valueModel s cs u radius) x y`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem symmetricBox_mem {s : Nat} (hs : 0<s) {radius : Int} {x : ℝ}
    (h : |x|≤(radius:ℝ)/s) : (symmetricBox radius).Mem s x := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hh := abs_le.mp h
  constructor
  · dsimp [symmetricBox,Bounds.Mem]
    push_cast
    have hl : -(radius:ℝ)/s≤x := by simpa only [neg_div] using hh.1
    have hle := (div_le_iff₀ hs').mp hl
    nlinarith
  · dsimp [symmetricBox,Bounds.Mem]
    have hle := (le_div_iff₀ hs').mp hh.2
    nlinarith

/--
Defines `valueModel` of type `List Bounds` by `Poly.add [symmetricBox radius] (Poly.compose s
(Poly.exactBounds u) (Poly.exactBounds cs))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.models` uses this
definition in the displayed construction of `Panel.models`. Its inputs and component formulas
are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def valueModel (s : Nat) (cs u : List Int) (radius : Int) : List Bounds :=
  Poly.add [symmetricBox radius]
    (Poly.compose s (Poly.exactBounds u) (Poly.exactBounds cs))

/--
The precise assertion is `Poly.At s (valueModel s cs u radius) x y`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.inputs_sound` uses
this assertion to establish the assertion stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Poly.compose_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.exactBounds_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.widen_sound` with the arguments shown in the
proof.
-/
theorem valueModel_sound {s : Nat} (hs : 0<s) (cs u : List Int)
    {radius : Int} {x y : ℝ}
    (he : |y-(Poly.exactPolynomial s cs).eval ((Poly.exactPolynomial s u).eval x)|≤
      (radius:ℝ)/s) : Poly.At s (valueModel s cs u radius) x y := by
  have hp := Poly.compose_sound hs (Poly.exactBounds_sound hs cs) (Poly.exactBounds_sound hs u)
  apply Poly.widen_sound hp
  apply symmetricBox_mem hs
  simpa only [eval_comp] using he

namespace ContactPolynomial
/--
A contact panel linking one left-chart row and one reflected-chart row to a proposed quadrature
primitive and its residual witnesses. Shared endpoints and source rows prevent an unrelated
model from being substituted.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.leftCoordinate` uses
this record of data and proof obligations in the displayed construction of
`Panel.leftCoordinate`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure Panel where
  /-- Scaled left endpoint of this contact quadrature panel. -/
  start : Int
  /-- Scaled panel width. -/
  width : Nat
  /-- Checked left-chart reference row covering this panel. -/
  left : ResidualCell.Row
  /-- Checked reflected-chart reference row covering this panel. -/
  right : ResidualCell.Row
  /-- Scaled uncertainty radius for the cubic reference root. -/
  rootRadius : Int
  /-- Scaled polynomial coefficients of the proposed contact-integral primitive. -/
  g : List Int
  /-- Polynomial/checkpoint witnesses for the contact residual program. -/
  row : Row
  deriving Repr, DecidableEq

/--
Defines `Panel.leftCoordinate` of type `List Int` by
`[(p.start-p.left.start)*p.left.step,(p.width:Int)*p.left.step]`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.leftCoordinate_eval`
uses this definition to establish `(Poly.exactPolynomial s
p.leftCoordinate).eval x= p.left.localCoordinate s (p.time s x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Panel.leftCoordinate (p : Panel) : List Int :=
  [(p.start-p.left.start)*p.left.step,(p.width:Int)*p.left.step]
/--
Defines `Panel.rightCoordinate` of type `List Int` by
`[(2*s-p.start-p.right.start)*p.right.step,-(p.width:Int)*p.right.step]`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.models` uses this
definition in the displayed construction of `Panel.models`. Its inputs and component formulas
are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Panel.rightCoordinate (s : Nat) (p : Panel) : List Int :=
  [(2*s-p.start-p.right.start)*p.right.step,-(p.width:Int)*p.right.step]
/--
Defines `Panel.time` of type `ℝ` by `(p.start:ℝ)/s+(p.width:ℝ)/s*x`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.leftCoordinate_eval`
uses this definition to establish `(Poly.exactPolynomial s
p.leftCoordinate).eval x= p.left.localCoordinate s (p.time s x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def Panel.time (s : Nat) (p : Panel) (x : ℝ) : ℝ :=
  (p.start:ℝ)/s+(p.width:ℝ)/s*x
/--
Defines `Panel.models` of type `List (List Bounds)` by `[Poly.exactBounds [p.start,p.width],
[piB], valueModel s p.left.z p.leftCoordinate p.rootRadius, valueModel s p.left.p
p.leftCoordinate eL, valueModel s p.right.p (p.rightCoordinate s) eR,Poly.exactBounds p.g]`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.modelCheck` uses this
definition in the displayed construction of `Panel.modelCheck`. Its inputs and component
formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Panel.models (s : Nat) (piB : Bounds) (eL eR : Int) (p : Panel) : List (List Bounds) :=
  [Poly.exactBounds [p.start,p.width], [piB],
    valueModel s p.left.z p.leftCoordinate p.rootRadius,
    valueModel s p.left.p p.leftCoordinate eL,
    valueModel s p.right.p (p.rightCoordinate s) eR,Poly.exactBounds p.g]

/--
Defines `Panel.modelCheck` of type `Bool` by `decide ( 0<p.width ∧ 0≤p.start ∧
p.start+p.width≤s ∧ p.left.start≤p.start ∧ p.start+p.width≤p.left.start+p.left.width ∧
p.right.start≤2*s-p.start-p.width ∧ 2*s-p.start≤p.right.start+p.right.width ∧
p.left.delta≤(p.rootRadius:ℚ)/s ∧ p.row.inputs=p.models s piB eL eR)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.time_mem` uses this
definition to establish membership in the specified domain/enclosure: `p.time s x∈Icc (0:ℝ) 1 ∧
p.time s x∈Icc (p.left.left s) (p.left.right s) ∧ 2-p.time s x∈Icc (p.right.left s)
(p.right.right s)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Panel.modelCheck (s : Nat) (piB : Bounds) (eL eR : Int) (p : Panel) : Bool := decide (
  0<p.width ∧ 0≤p.start ∧ p.start+p.width≤s ∧
  p.left.start≤p.start ∧ p.start+p.width≤p.left.start+p.left.width ∧
  p.right.start≤2*s-p.start-p.width ∧ 2*s-p.start≤p.right.start+p.right.width ∧
  p.left.delta≤(p.rootRadius:ℚ)/s ∧ p.row.inputs=p.models s piB eL eR)

/--
Exact identity `(Poly.exactPolynomial s [p.start,p.width]).eval x=p.time s x`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.inputs_sound` uses
this identity to establish the assertion stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Panel.time_eval (s : Nat) (p : Panel) (x : ℝ) :
    (Poly.exactPolynomial s [p.start,p.width]).eval x=p.time s x := by
  simp only [Poly.exactPolynomial,time,eval_add,eval_C,eval_mul,eval_X,mul_zero,add_zero]
  push_cast
  ring

/--
The precise assertion is `(Poly.exactPolynomial s p.leftCoordinate).eval x=
p.left.localCoordinate s (p.time s x)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.inputs_sound` uses
this identity to establish the assertion stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Panel.leftCoordinate_eval (s : Nat) (p : Panel) (x : ℝ) :
    (Poly.exactPolynomial s p.leftCoordinate).eval x=
      p.left.localCoordinate s (p.time s x) := by
  simp only [leftCoordinate,Poly.exactPolynomial,eval_add,eval_C,eval_mul,eval_X,
    mul_zero,add_zero,ResidualCell.Row.localCoordinate,ResidualCell.Row.left,time]
  push_cast
  ring

/--
The precise assertion is `(Poly.exactPolynomial s (p.rightCoordinate s)).eval x=
p.right.localCoordinate s (2-p.time s x)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.inputs_sound` uses
this identity to establish the assertion stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem Panel.rightCoordinate_eval {s : Nat} (hs : 0<s) (p : Panel) (x : ℝ) :
    (Poly.exactPolynomial s (p.rightCoordinate s)).eval x=
      p.right.localCoordinate s (2-p.time s x) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  simp only [rightCoordinate,Poly.exactPolynomial,eval_add,eval_C,eval_mul,eval_X,
    mul_zero,add_zero,ResidualCell.Row.localCoordinate,ResidualCell.Row.left,time]
  push_cast
  have hs' : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  field_simp [hs']
  ring

/--
Membership in the specified domain/enclosure: `p.time s x∈Icc (0:ℝ) 1 ∧ p.time s x∈Icc
(p.left.left s) (p.left.right s) ∧ 2-p.time s x∈Icc (p.right.left s) (p.right.right s)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.Panel.actual_of_inputs`
uses this assertion to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Panel.time_mem {s : Nat} (hs : 0<s) (p : Panel) {piB : Bounds} {eL eR : Int}
    (hc : p.modelCheck s piB eL eR=true) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    p.time s x∈Icc (0:ℝ) 1 ∧
    p.time s x∈Icc (p.left.left s) (p.left.right s) ∧
    2-p.time s x∈Icc (p.right.left s) (p.right.right s) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  obtain ⟨_,ha,hb,hla,hlb,hra,hrb,_,_⟩ := of_decide_eq_true hc
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hw : (0:ℝ)≤p.width := Nat.cast_nonneg _
  have hbox : (p.start:ℝ)/s≤p.time s x ∧ p.time s x≤((p.start:ℝ)+p.width)/s := by
    dsimp [time]
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hw hs'.le) hx.1)
    · rw [add_div]
      nlinarith [mul_nonneg (div_nonneg hw hs'.le) (sub_nonneg.mpr hx.2)]
  have hla' : (p.left.start:ℝ)/s≤(p.start:ℝ)/s :=
    div_le_div_of_nonneg_right (by exact_mod_cast hla) hs'.le
  have hlb' : ((p.start:ℝ)+p.width)/s≤((p.left.start:ℝ)+p.left.width)/s :=
    div_le_div_of_nonneg_right (by exact_mod_cast hlb) hs'.le
  have hra' : (p.right.start:ℝ)/s≤2-((p.start:ℝ)+p.width)/s := by
    rw [le_sub_iff_add_le,← add_div,div_le_iff₀ hs']
    have hh : (p.right.start:ℝ)≤2*s-p.start-p.width := by exact_mod_cast hra
    linarith
  have hrb' : 2-(p.start:ℝ)/s≤((p.right.start:ℝ)+p.right.width)/s := by
    rw [sub_le_iff_le_add,← add_div,le_div_iff₀ hs']
    have hh : 2*(s:ℝ)-p.start≤(p.right.start:ℝ)+p.right.width := by exact_mod_cast hrb
    linarith
  refine ⟨⟨?_,?_⟩,⟨hla'.trans hbox.1,hbox.2.trans hlb'⟩,⟨?_,?_⟩⟩
  · exact (div_nonneg (by exact_mod_cast ha) hs'.le).trans hbox.1
  · refine hbox.2.trans ?_
    rw [div_le_iff₀ hs',one_mul]
    exact_mod_cast hb
  · change (p.right.start:ℝ)/s≤2-p.time s x
    linarith [hbox.2]
  · change 2-p.time s x≤((p.right.start:ℝ)+p.right.width)/s
    linarith [hbox.1]

end ContactPolynomial
end «2610.05164v2».Numerics.IntegerCertificate
