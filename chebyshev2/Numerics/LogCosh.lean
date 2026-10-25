import chebyshev2.Numerics.BinaryPowerHigh

/-!
Article: chebyshev2, Section 4.1.
Stable interval evaluation of the exact spectral target log(cosh(sqrt s)).
Use: `chebyshev2.Numerics.logCoshCheck_sound` feeds
`chebyshev2.Certificates.DualInputs.TargetObservations.Hsupport_mem` (Hsupport mem).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
open LeanCert.Core
set_option autoImplicit false

/--
Defines `sqrtBracketCheck` of type `Bool` by `decide (0≤S.lo ∧ 0≤J.lo ∧ J.lo^2≤S.lo ∧
S.hi≤J.hi^2)`.

Use: `chebyshev2.Numerics.sqrtBracketCheck_sound` uses this definition to establish
membership in the specified domain/enclosure: `Real.sqrt s∈J`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def sqrtBracketCheck (S J : IntervalRat) : Bool :=
  decide (0≤S.lo ∧ 0≤J.lo ∧ J.lo^2≤S.lo ∧ S.hi≤J.hi^2)

/--
Membership in the specified domain/enclosure: `Real.sqrt s∈J`.

Use: `chebyshev2.Certificates.DualInputs.TargetObservations.Hsupport_mem` uses this
assertion to establish membership in the specified domain/enclosure: `Real.log (Real.cosh
(Real.sqrt ((sigma:ℝ)*(Real.pi^2/4))))∈Hsupportbounds`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem sqrtBracketCheck_sound {S J : IntervalRat} (hc : sqrtBracketCheck S J=true)
    {s : ℝ} (hs : s∈S) : Real.sqrt s∈J := by
  -- The tactic block explicitly constructs the required witness or reduces the goal to the
  -- local facts stated below.
  have h := of_decide_eq_true hc
  change 0≤S.lo ∧ 0≤J.lo ∧ J.lo^2≤S.lo ∧ S.hi≤J.hi^2 at h
  have hS : (0:ℝ)≤S.lo := by exact_mod_cast h.1
  have hL : (0:ℝ)≤J.lo := by exact_mod_cast h.2.1
  have hU : (0:ℝ)≤J.hi := hL.trans (by exact_mod_cast J.le)
  have hl : (J.lo:ℝ)^2≤S.lo := by exact_mod_cast h.2.2.1
  have hu : (S.hi:ℝ)≤(J.hi:ℝ)^2 := by exact_mod_cast h.2.2.2
  have hsq := Real.sq_sqrt (hS.trans hs.1)
  have hn := Real.sqrt_nonneg s
  constructor <;> nlinarith [hs.1,hs.2]

/--
Exact identity `Real.log (Real.cosh x)=x+Real.log (1+Real.exp (-2*x))-Real.log 2`.

Use: `chebyshev2.Numerics.logCoshCheck_sound` rewrites with this identity to establish
membership in the specified domain/enclosure: `Real.log (Real.cosh x)∈output`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem log_cosh_stable (x : ℝ) :
    Real.log (Real.cosh x)=x+Real.log (1+Real.exp (-2*x))-Real.log 2 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have he : Real.cosh x=Real.exp x*(1+Real.exp (-2*x))/2 := by
    have hr : Real.exp x*Real.exp (-2*x)=Real.exp (-x) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [Real.cosh_eq,mul_add,mul_one,hr]
  rw [he,Real.log_div (mul_pos (Real.exp_pos x) (by positivity)).ne' (by norm_num),
    Real.log_mul (Real.exp_ne_zero x) (by positivity),Real.log_exp]

/--
Defines `logCoshInterval` of type `IntervalRat` by `let E := expBinaryHigh (IntervalRat.mul
(IntervalRat.singleton (-2)) J) roundHigh (IntervalRat.sub (IntervalRat.add J
(IntervalRat.logComputable (IntervalRat.add (IntervalRat.singleton 1) E) 6))
(IntervalRat.ln2Computable 64))`.

Use: `chebyshev2.Numerics.logCoshCheck` uses this definition in the displayed construction
of `logCoshCheck`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def logCoshInterval (J : IntervalRat) : IntervalRat :=
  let E := expBinaryHigh (IntervalRat.mul (IntervalRat.singleton (-2)) J)
  roundHigh (IntervalRat.sub
    (IntervalRat.add J (IntervalRat.logComputable (IntervalRat.add (IntervalRat.singleton 1) E) 6))
    (IntervalRat.ln2Computable 64))

/--
Defines `logCoshCheck` of type `Bool` by `let E := expBinaryHigh (IntervalRat.mul
(IntervalRat.singleton (-2)) J) decide (0<(IntervalRat.add (IntervalRat.singleton 1) E).lo) &&
intervalSubsetCheck (logCoshInterval J) output`.

Use: `chebyshev2.Numerics.logCoshCheck_sound` rewrites with this definition to establish
membership in the specified domain/enclosure: `Real.log (Real.cosh x)∈output`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def logCoshCheck (J output : IntervalRat) : Bool :=
  let E := expBinaryHigh (IntervalRat.mul (IntervalRat.singleton (-2)) J)
  decide (0<(IntervalRat.add (IntervalRat.singleton 1) E).lo) &&
    intervalSubsetCheck (logCoshInterval J) output

/--
Membership in the specified domain/enclosure: `Real.log (Real.cosh x)∈output`.

Use: `chebyshev2.Certificates.DualInputs.TargetObservations.Hsupport_mem` uses this
assertion to establish membership in the specified domain/enclosure: `Real.log (Real.cosh
(Real.sqrt ((sigma:ℝ)*(Real.pi^2/4))))∈Hsupportbounds`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Numerics.intervalSubsetCheck_sound`,
`chebyshev2.Numerics.log_cosh_stable`, `chebyshev2.Numerics.mem_roundHigh` with the
arguments shown in the proof.
-/
theorem logCoshCheck_sound {J output : IntervalRat} (hc : logCoshCheck J output=true)
    {x : ℝ} (hx : x∈J) : Real.log (Real.cosh x)∈output := by
  -- Use the identities/estimates `chebyshev2.Numerics.intervalSubsetCheck_sound`,
  -- `chebyshev2.Numerics.log_cosh_stable`, `chebyshev2.Numerics.mem_roundHigh` with
  -- the arguments shown in the proof.
  simp only [logCoshCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  apply intervalSubsetCheck_sound hc.2
  rw [log_cosh_stable]
  apply mem_roundHigh
  apply IntervalRat.mem_sub
  · apply IntervalRat.mem_add hx
    apply IntervalRat.mem_logComputable _ hc.1 6
    apply IntervalRat.mem_add (show (1:ℝ)∈IntervalRat.singleton 1 by
      simpa only [Rat.cast_one] using IntervalRat.mem_singleton 1)
    apply mem_expBinaryHigh
    simpa only [Rat.cast_neg,Rat.cast_ofNat] using
      IntervalRat.mem_mul (IntervalRat.mem_singleton (-2)) hx
  · exact IntervalRat.mem_ln2Computable 64

end chebyshev2.Numerics
