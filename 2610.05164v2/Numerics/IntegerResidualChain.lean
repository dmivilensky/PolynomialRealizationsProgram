import «2610.05164v2».Numerics.IntegerResidualCell

/-!
Article: 2610.05164v2, Section 4.1.
Local coordinates and propagation for polynomial residual certificates.
Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.chain_sound` feeds
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.complete_reference_chain` (complete
reference chain).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate.ResidualCell
open Set Polynomial «2610.05164v2».Calibration «2610.05164v2».DualCertificate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `Row.left` of type `ℝ` by `(r.start:ℝ)/s`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.chain_sound` rewrites with this
definition to prove the bound `|y ((stop:ℝ)/s)-(lastValue s center
rs:ℝ)|≤(bound:ℝ) ∧ ∀ r∈rs, ∀ t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤(bound:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Row.left (s : Nat) (r : Row) : ℝ := (r.start:ℝ)/s
/--
Defines `Row.right` of type `ℝ` by `((r.start:ℝ)+r.width)/s`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.chain_sound` rewrites with this
definition to prove the bound `|y ((stop:ℝ)/s)-(lastValue s center
rs:ℝ)|≤(bound:ℝ) ∧ ∀ r∈rs, ∀ t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤(bound:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Row.right (s : Nat) (r : Row) : ℝ := ((r.start:ℝ)+r.width)/s
/--
Defines `Row.localCoordinate` of type `ℝ` by `(t-r.left s)*r.step`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.approx` uses this definition
in the displayed construction of `Row.approx`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Row.localCoordinate (s : Nat) (r : Row) (t : ℝ) : ℝ := (t-r.left s)*r.step
/--
Defines `Row.approx` of type `ℝ` by `(Poly.exactPolynomial s r.p).eval (r.localCoordinate s
t)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.approx_hasDerivAt` uses this
definition to establish the actual derivative at the stated point: `HasDerivAt (r.approx s)
(r.approxDeriv s t) t`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Row.approx (s : Nat) (r : Row) (t : ℝ) : ℝ :=
  (Poly.exactPolynomial s r.p).eval (r.localCoordinate s t)
/--
Defines `Row.approxDeriv` of type `ℝ` by `(r.step:ℝ)*(Poly.exactPolynomial s
r.p).derivative.eval (r.localCoordinate s t)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.approx_hasDerivAt` uses this
definition to establish the actual derivative at the stated point: `HasDerivAt (r.approx s)
(r.approxDeriv s t) t`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Row.approxDeriv (s : Nat) (r : Row) (t : ℝ) : ℝ :=
  (r.step:ℝ)*(Poly.exactPolynomial s r.p).derivative.eval (r.localCoordinate s t)
/--
Defines `Row.chart` of type `ℝ` by `if r.reflected then 2-t else t`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.coordinate_eval` rewrites
with this definition to establish the identity `(values s r 0).eval (r.localCoordinate s
t)=r.chart t`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Row.chart (r : Row) (t : ℝ) : ℝ := if r.reflected then 2-t else t
/--
Defines `Row.beginValue` of type `ℚ` by `(r.p.headD 0:ℚ)/s`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.approx_left` uses this
definition to establish the identity `r.approx s (r.left s)=(r.beginValue s:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Row.beginValue (s : Nat) (r : Row) : ℚ := (r.p.headD 0:ℚ)/s
/--
Defines `Row.endValue` of type `ℚ` by `(r.p.sum:ℚ)/s`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.approx_right` uses this
definition to establish the identity `r.approx s (r.right s)=(r.endValue s:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Row.endValue (s : Nat) (r : Row) : ℚ := (r.p.sum:ℚ)/s

/--
Membership in the specified domain/enclosure: `r.localCoordinate s t∈Icc (0:ℝ) 1`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.error` uses this assertion to
establish the stated quantitative bound `|y t-r.approx s t|≤e+(η:ℝ)*(t-r.left s)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem Row.local_mem {s : Nat} (hs : 0<s) (r : Row)
    (hwidth : 0<r.width) (hstep : r.width*r.step=s) {t : ℝ}
    (ht : t∈Icc (r.left s) (r.right s)) : r.localCoordinate s t∈Icc (0:ℝ) 1 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hstep' : (r.width:ℝ)*(r.step:ℝ)=(s:ℝ) := by exact_mod_cast hstep
  have hpos : (0:ℝ)<r.width := by exact_mod_cast hwidth
  have hsp : 0<(r.step:ℝ) := by nlinarith
  constructor
  · exact mul_nonneg (sub_nonneg.mpr ht.1) hsp.le
  · dsimp [localCoordinate,left,right] at *
    have hh : t-(r.start:ℝ)/s≤(r.width:ℝ)/s := by
      rw [add_div] at ht
      linarith [ht.2]
    calc
      (t-(r.start:ℝ)/s)*r.step≤((r.width:ℝ)/s)*r.step := by gcongr
      _ = 1 := by field_simp; nlinarith [hstep']

/--
Exact identity `(values s r 0).eval (r.localCoordinate s t)=r.chart t`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.error` uses this identity to
establish the stated quantitative bound `|y t-r.approx s t|≤e+(η:ℝ)*(t-r.left s)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem Row.coordinate_eval {s : Nat} (hs : 0<s) (r : Row)
    (hstep : r.width*r.step=s) (t : ℝ) :
    (values s r 0).eval (r.localCoordinate s t)=r.chart t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs' : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  have hstep' : (r.width:ℝ)*(r.step:ℝ)=(s:ℝ) := by exact_mod_cast hstep
  cases hr : r.reflected <;>
    simp only [values,coordinate,hr,Row.chart,Bool.false_eq_true,↓reduceIte,
      Poly.exactPolynomial,eval_add,eval_C,eval_mul,eval_X,mul_zero,add_zero]
  · dsimp [localCoordinate,left]
    push_cast
    field_simp
    have he := congrArg (fun v : ℝ => ((s:ℝ)*t-r.start)*v) hstep'
    nlinarith [he]
  · dsimp [localCoordinate,left]
    push_cast
    field_simp
    have he := congrArg (fun v : ℝ => ((s:ℝ)*t-r.start)*v) hstep'
    nlinarith [he]

/--
The actual derivative at the stated point: `HasDerivAt (r.approx s) (r.approxDeriv s t) t`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.error` uses this derivative
formula to prove the bound `|y t-r.approx s t|≤e+(η:ℝ)*(t-r.left s)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Row.approx_hasDerivAt (s : Nat) (r : Row) (t : ℝ) :
    HasDerivAt (r.approx s) (r.approxDeriv s t) t := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have h := (Poly.exactPolynomial s r.p).hasDerivAt (r.localCoordinate s t)
  have hl : HasDerivAt (r.localCoordinate s) (r.step:ℝ) t := by
    convert! ((hasDerivAt_id t).sub_const (r.left s)).mul_const (r.step:ℝ) using 1
    simp
  convert! h.comp t hl using 1
  dsimp [approxDeriv]
  ring

/--
Exact identity `r.approx s (r.left s)=(r.beginValue s:ℝ)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.chain_sound` rewrites with this
identity to prove the bound `|y ((stop:ℝ)/s)-(lastValue s center
rs:ℝ)|≤(bound:ℝ) ∧ ∀ r∈rs, ∀ t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤(bound:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Row.approx_left (s : Nat) (r : Row) :
    r.approx s (r.left s)=(r.beginValue s:ℝ) := by cases hp : r.p <;> simp [approx,localCoordinate,Poly.exactPolynomial,beginValue,hp]

/--
Exact identity `(Poly.exactPolynomial s as).eval 1=(as.sum:ℝ)/s`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.approx_right` rewrites with
this identity to establish the identity `r.approx s (r.right s)=(r.endValue s:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `as`; the recursive step uses the previous-stage assertion.
-/
theorem exactPolynomial_eval_one (s : Nat) (as : List Int) :
    (Poly.exactPolynomial s as).eval 1=(as.sum:ℝ)/s := by
  induction as with
  | nil => simp [Poly.exactPolynomial]
  | cons a as ih => simp [Poly.exactPolynomial,ih,add_div]

/--
Exact identity `r.approx s (r.right s)=(r.endValue s:ℝ)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.chain_sound` uses this identity
to prove the bound `|y ((stop:ℝ)/s)-(lastValue s center
rs:ℝ)|≤(bound:ℝ) ∧ ∀ r∈rs, ∀ t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤(bound:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.exactPolynomial_eval_one` with the
arguments shown in the proof.
-/
theorem Row.approx_right {s : Nat} (hs : 0<s) (r : Row)
    (hstep : r.width*r.step=s) : r.approx s (r.right s)=(r.endValue s:ℝ) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.exactPolynomial_eval_one` with
  -- the arguments shown in the proof.
  have hs' : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  have hstep' : (r.width:ℝ)*(r.step:ℝ)=(s:ℝ) := by exact_mod_cast hstep
  have hx : r.localCoordinate s (r.right s)=1 := by
    dsimp [localCoordinate,left,right]
    rw [add_div,add_sub_cancel_left,div_mul_eq_mul_div,hstep',div_self hs']
  rw [approx,hx,exactPolynomial_eval_one]
  simp only [endValue,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]

/--
The stated quantitative bound `|y t-r.approx s t|≤e+(η:ℝ)*(t-r.left s)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.left_stable` uses this bound to
establish the precise assertion is `Stable s (η:ℝ) ((ReferenceJetSource.referenceData
R).normalizedFilter (σ := (σ:ℝ)) (by exact_mod_cast hσ)) r`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedSpeed_positive`,
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.local_mem` with the arguments
shown in the proof.
-/
theorem Row.error {s : Nat} (hs : 0<s) {ops : List Op} {piB : Bounds}
    (hpi : piB.Mem s Real.pi) (R : RationalReference) (σ η : ℚ)
    (shapeK : codeExpressionCheck ops 72 ResidualExpr.k=true)
    (shapeD : codeExpressionCheck ops 30 (ResidualExpr.profileParts R).1=true)
    (shapeRoot : codeExpressionCheck ops 16 (ResidualExpr.rootResidual R)=true)
    (shapeFactor : codeExpressionCheck ops 12 ResidualExpr.factor=true)
    (shapeODE : codeExpressionCheck ops 0 (ResidualExpr.odeResidual σ)=true)
    (hσ : 0≤(σ:ℝ)) (hη : 0≤(η:ℝ)) (r : Row) (hc : check s ops piB η r=true)
    (hchart : ∀ t∈Icc (r.left s) (r.right s), r.chart t∈Icc (0:ℝ) 1)
    {y : ℝ → ℝ} (hy : ContinuousOn y (Icc (r.left s) (r.right s)))
    (hy0 : ∀ t∈Ico (r.left s) (r.right s), 0≤y t)
    (hyd : ∀ t∈Ico (r.left s) (r.right s), HasDerivWithinAt y
      ((ReferenceJetSource.referenceData R).normalizedVelocity (r.chart t)*
        ((Real.pi^2/4)*(r.chart t*(ReferenceJetSource.referenceData R).normalizedRoot (r.chart t))^2-
          2*y t-(σ:ℝ)*(y t)^2)) (Ici t) t)
    {e : ℝ} (he : 0≤e) (h0 : |y (r.left s)-r.approx s (r.left s)|≤e)
    {t : ℝ} (ht : t∈Icc (r.left s) (r.right s)) :
    |y t-r.approx s t|≤e+(η:ℝ)*(t-r.left s) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedSpeed_positive`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.local_mem` with the arguments
  -- shown in the proof.
  have hwidthstep : 0<r.width ∧ r.width*r.step=s := by
    have hh : decide (0<r.width ∧ r.width*r.step=s)=true ∧
        (summarize s ops piB r).any (Summary.check s r.delta η)=true := by
      simpa only [check,Bool.and_eq_true] using hc
    exact of_decide_eq_true hh.1
  let D := ReferenceJetSource.referenceData R
  let v := fun x => D.normalizedVelocity (r.chart x)
  let C := fun x => v x*(Real.pi^2/4)*(r.chart x*D.normalizedRoot (r.chart x))^2
  let A := fun x => -2*v x
  let B := fun x => -(σ:ℝ)*v x
  have hv (x : ℝ) (hx : x∈Icc (r.left s) (r.right s)) : 0≤v x := by
    exact (div_pos (by norm_num) (D.normalizedSpeed_positive (hchart x hx))).le
  have hcert (x : ℝ) (hx : x∈Icc (r.left s) (r.right s)) :=
    check_sound hs hpi R σ η shapeK shapeD shapeRoot shapeFactor shapeODE hc
      (r.local_mem hs hwidthstep.1 hwidthstep.2 hx)
      (by rw [r.coordinate_eval hs hwidthstep.2]; exact hchart x hx)
  apply riccati_residual_bound_nonnegative (C := C) (A := A) (B := B)
    (p' := r.approxDeriv s) hy
    (fun x hx => (r.approx_hasDerivAt s x).continuousAt.continuousWithinAt)
    ?_ (fun x _ => (r.approx_hasDerivAt s x).hasDerivWithinAt) ?_ ?_ hy0
    ?_ he hη h0 ?_ ht
  · intro x hx
    convert hyd x hx using 1
    dsimp [C,A,B,v]
    ring
  · intro x hx
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hv x ⟨hx.1,hx.2.le⟩)
  · intro x hx
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ) (hv x ⟨hx.1,hx.2.le⟩)
  · intro x hx
    exact (hcert x ⟨hx.1,hx.2.le⟩).1
  · intro x hx
    have h := (hcert x ⟨hx.1,hx.2.le⟩).2
    rw [r.coordinate_eval hs hwidthstep.2] at h
    convert h using 1
    dsimp [C,A,B,v,D,values,approx,approxDeriv]
    simp only [eval_mul,eval_C]
    congr 1
    ring

/--
Defines `nextError` of type `ℚ` by `error+|center-r.beginValue s|+η*((r.width:ℚ)/s)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.chain_sound` rewrites with this
definition to prove the bound `|y ((stop:ℝ)/s)-(lastValue s center
rs:ℝ)|≤(bound:ℝ) ∧ ∀ r∈rs, ∀ t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤(bound:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def nextError (s : Nat) (η center error : ℚ) (r : Row) : ℚ :=
  error+|center-r.beginValue s|+η*((r.width:ℚ)/s)

/--
Defines `chainCheck` by pattern matching with result type `Int → ℚ → ℚ → List Row → Bool`. The
displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.chain_sound` uses this definition
to prove the bound `|y ((stop:ℝ)/s)-(lastValue s center
rs:ℝ)|≤(bound:ℝ) ∧ ∀ r∈rs, ∀ t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤(bound:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def chainCheck (s : Nat) (η bound : ℚ) (stop : Int) :
    Int → ℚ → ℚ → List Row → Bool
  | start, _, error, [] => decide (start=stop ∧ error≤bound)
  | start, center, error, r::rs =>
    decide (start=r.start ∧ 0<r.width ∧ r.width*r.step=s ∧ 0≤error ∧
      nextError s η center error r≤bound) &&
    chainCheck s η bound stop (r.start+r.width) (r.endValue s)
      (nextError s η center error r) rs

/--
An abstract local stability property, used only with `Row.error` below.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.chain_sound` uses this definition
to prove the bound `|y ((stop:ℝ)/s)-(lastValue s center
rs:ℝ)|≤(bound:ℝ) ∧ ∀ r∈rs, ∀ t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤(bound:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Stable (s : Nat) (η : ℝ) (y : ℝ → ℝ) (r : Row) : Prop :=
  ∀ e : ℝ, 0≤e → |y (r.left s)-r.approx s (r.left s)|≤e →
    ∀ t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤e+η*(t-r.left s)

/--
Defines `lastValue` by pattern matching with result type `ℚ → List Row → ℚ`. The displayed
branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.chain_sound` uses this definition
to prove the bound `|y ((stop:ℝ)/s)-(lastValue s center
rs:ℝ)|≤(bound:ℝ) ∧ ∀ r∈rs, ∀ t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤(bound:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def lastValue (s : Nat) : ℚ → List Row → ℚ
  | c, [] => c
  | _, r::rs => lastValue s (r.endValue s) rs

/--
The stated quantitative bound `|y ((stop:ℝ)/s)-(lastValue s center rs:ℝ)|≤(bound:ℝ) ∧ ∀ r∈rs, ∀
t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤(bound:ℝ)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.complete_reference_chain` uses
this bound to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `rs` while keeping `start center error` arbitrary; the recursive step
uses the previous-stage assertion.
-/
theorem chain_sound {s : Nat} (hs : 0<s) {η bound center error : ℚ}
    (hη : 0≤η) {start stop : Int} (rs : List Row)
    (hc : chainCheck s η bound stop start center error rs=true)
    {y : ℝ → ℝ} (hy : ∀ r∈rs, Stable s (η:ℝ) y r)
    (h0 : |y ((start:ℝ)/s)-(center:ℝ)|≤(error:ℝ)) :
    |y ((stop:ℝ)/s)-(lastValue s center rs:ℝ)|≤(bound:ℝ) ∧
    ∀ r∈rs, ∀ t∈Icc (r.left s) (r.right s), |y t-r.approx s t|≤(bound:ℝ) := by
  -- Induct on `rs` while keeping `start center error` arbitrary; the recursive step uses
  -- the previous-stage assertion.
  induction rs generalizing start center error with
  | nil =>
    have hh : start=stop ∧ error≤bound := of_decide_eq_true hc
    rw [hh.1] at h0
    refine ⟨h0.trans ?_,by simp⟩
    exact_mod_cast hh.2
  | cons r rs ih =>
    have hh : (start=r.start ∧ 0<r.width ∧ r.width*r.step=s ∧ 0≤error ∧
        nextError s η center error r≤bound) ∧
        chainCheck s η bound stop (r.start+r.width) (r.endValue s)
          (nextError s η center error r) rs=true := by
      simpa only [chainCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
    have hηr : (0:ℝ)≤(η:ℝ) := by exact_mod_cast hη
    have he : (0:ℝ)≤(error:ℝ) := by exact_mod_cast hh.1.2.2.2.1
    have hbound : (nextError s η center error r:ℝ)≤(bound:ℝ) := by
      exact_mod_cast hh.1.2.2.2.2
    have hinit : |y (r.left s)-r.approx s (r.left s)|≤
        (error:ℝ)+|(center:ℝ)-(r.beginValue s:ℝ)| := by
      rw [Row.approx_left]
      have h0r : |y (r.left s)-(center:ℝ)|≤(error:ℝ) := by
        simpa only [hh.1.1,Row.left] using h0
      exact (abs_sub_le _ _ _).trans (add_le_add h0r le_rfl)
    have hr := hy r (by simp) _ (add_nonneg he (abs_nonneg _)) hinit
    have hlen : r.left s≤r.right s := by
      dsimp [Row.left,Row.right]
      exact div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg r.width : (0:ℝ)≤r.width)])
        (Nat.cast_nonneg s)
    have hend := hr (r.right s) ⟨hlen,le_rfl⟩
    rw [r.approx_right hs hh.1.2.2.1] at hend
    have hright : r.right s=((r.start+r.width: Int):ℝ)/s := by simp [Row.right]
    have hnexteq : (nextError s η center error r:ℝ)=
        (error:ℝ)+|(center:ℝ)-(r.beginValue s:ℝ)|+(η:ℝ)*(r.right s-r.left s) := by
      simp [nextError,Row.right,Row.left,add_div]
    have hnext : |y (((r.start+r.width:Int):ℝ)/s)-(r.endValue s:ℝ)|≤
        (nextError s η center error r:ℝ) := by simpa [hnexteq,hright] using hend
    have hi := ih hh.2 (fun v hv => hy v (by simp [hv])) hnext
    refine ⟨hi.1,?_⟩
    intro v hv t ht
    rcases List.mem_cons.mp hv with hvr|hvr
    · subst v
      refine (hr t ht).trans (le_trans ?_ hbound)
      rw [hnexteq]
      gcongr
      exact ht.2
    · exact hi.2 v hvr t ht

end
end «2610.05164v2».Numerics.IntegerCertificate.ResidualCell
