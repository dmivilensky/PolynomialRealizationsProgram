import chebyshev2.Numerics.IntegerCertificate
import chebyshev2.Numerics.CubicRoot

/-!
Article: chebyshev2, Section 4.1.
Integer Cubic.
Use: `chebyshev2.Numerics.IntegerCertificate.cubicCheck_sound` feeds
`chebyshev2.Numerics.IntegerCertificate.Op.check_sound` (check sound).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate
open LeanCert.Core
set_option autoImplicit false

/--
Defines `Bounds.toInterval` of type `IntervalRat` by `⟨(I.lo : ℚ) / s, (I.hi : ℚ) / s,
div_le_div_of_nonneg_right (by exact_mod_cast hI) (by positivity)⟩`.

Use: `chebyshev2.Numerics.IntegerCertificate.Bounds.mem_toInterval` uses this definition to
establish equivalence of the displayed criteria: `x ∈ I.toInterval s hs hI ↔ I.Mem s x`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Bounds.toInterval (I : Bounds) (s : Nat) (hs : 0 < s) (hI : I.lo ≤ I.hi) : IntervalRat :=
  ⟨(I.lo : ℚ) / s, (I.hi : ℚ) / s,
    div_le_div_of_nonneg_right (by exact_mod_cast hI) (by positivity)⟩

/--
Equivalence of the displayed criteria: `x ∈ I.toInterval s hs hI ↔ I.Mem s x`.

Use: `chebyshev2.Numerics.IntegerCertificate.cubicCheck_sound` uses this assertion to
establish the precise assertion is `R.Mem s (chebyshev2.Numerics.positiveCubic a b)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Bounds.mem_toInterval {I : Bounds} {s : Nat} (hs : 0 < s) (hI : I.lo ≤ I.hi)
    {x : ℝ} : x ∈ I.toInterval s hs hI ↔ I.Mem s x := by
  have hp : (0 : ℝ) < s := by exact_mod_cast hs
  simp only [toInterval, IntervalRat.mem_def, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    div_le_iff₀ hp, le_div_iff₀ hp, Bounds.Mem]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith

/--
Defines `cubicCheck` of type `Bool` by `decide (0 ≤ A.lo ∧ 0 < B.lo ∧ 0 ≤ R.lo ∧ R.lo ≤ R.hi ∧
R.lo^3 - A.lo * R.lo * (s : Int) - B.lo * (s : Int)^2 ≤ 0 ∧ 0 ≤ R.hi^3 - A.hi * R.hi * (s :
Int) - B.hi * (s : Int)^2)`.

Use: `chebyshev2.Numerics.IntegerCertificate.cubicCheck_sound` uses this definition to
establish the precise assertion is `R.Mem s (chebyshev2.Numerics.positiveCubic a b)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def cubicCheck (s : Nat) (A B R : Bounds) : Bool :=
  decide (0 ≤ A.lo ∧ 0 < B.lo ∧ 0 ≤ R.lo ∧ R.lo ≤ R.hi ∧
    R.lo^3 - A.lo * R.lo * (s : Int) - B.lo * (s : Int)^2 ≤ 0 ∧
    0 ≤ R.hi^3 - A.hi * R.hi * (s : Int) - B.hi * (s : Int)^2)

/--
The precise assertion is `R.Mem s (chebyshev2.Numerics.positiveCubic a b)`.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` uses this assertion to
establish the precise assertion is `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem cubicCheck_sound {A B R : Bounds} {s : Nat} (hs : 0 < s) {a b : ℝ}
    (hc : cubicCheck s A B R = true) (ha : A.Mem s a) (hb : B.Mem s b) :
    R.Mem s (chebyshev2.Numerics.positiveCubic a b) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hh : 0 ≤ A.lo ∧ 0 < B.lo ∧ 0 ≤ R.lo ∧ R.lo ≤ R.hi ∧
      R.lo^3 - A.lo * R.lo * (s : Int) - B.lo * (s : Int)^2 ≤ 0 ∧
      0 ≤ R.hi^3 - A.hi * R.hi * (s : Int) - B.hi * (s : Int)^2 := of_decide_eq_true hc
  have hA : A.lo ≤ A.hi := by exact_mod_cast ha.1.trans ha.2
  have hB : B.lo ≤ B.hi := by exact_mod_cast hb.1.trans hb.2
  have hR := hh.2.2.2.1
  have hp : (0 : ℚ) < s := by exact_mod_cast hs
  have hn : (s : ℚ) ≠ 0 := hp.ne'
  have hlow : (R.lo : ℚ)^3 - (A.lo : ℚ) * R.lo * s - (B.lo : ℚ) * (s : ℚ)^2 ≤ 0 := by
    exact_mod_cast hh.2.2.2.2.1
  have hupp : (0 : ℚ) ≤ (R.hi : ℚ)^3 - (A.hi : ℚ) * R.hi * s - (B.hi : ℚ) * (s : ℚ)^2 := by
    exact_mod_cast hh.2.2.2.2.2
  have he (r α β : ℚ) :
      ((r / s)^3 - (α / s) * (r / s) - β / s) * (s : ℚ)^3 =
        r^3 - α * r * s - β * (s : ℚ)^2 := by
    field_simp
  have hcheck : cubicBracketCheck (A.toInterval s hs hA) (B.toInterval s hs hB)
      (R.toInterval s hs hR) = true := by
    apply decide_eq_true
    change 0 ≤ (A.lo : ℚ) / s ∧ 0 < (B.lo : ℚ) / s ∧ 0 ≤ (R.lo : ℚ) / s ∧
      ((R.lo : ℚ) / s)^3 - ((A.lo : ℚ) / s) * ((R.lo : ℚ) / s) - (B.lo : ℚ) / s ≤ 0 ∧
      0 ≤ ((R.hi : ℚ) / s)^3 - ((A.hi : ℚ) / s) * ((R.hi : ℚ) / s) - (B.hi : ℚ) / s
    refine ⟨div_nonneg (by exact_mod_cast hh.1) hp.le,
      div_pos (by exact_mod_cast hh.2.1) hp,
      div_nonneg (by exact_mod_cast hh.2.2.1) hp.le, ?_, ?_⟩
    · apply (mul_le_mul_iff_right₀ (pow_pos hp 3)).mp
      simpa only [mul_comm ((s : ℚ)^3), he, zero_mul, mul_zero] using hlow
    · apply (mul_le_mul_iff_right₀ (pow_pos hp 3)).mp
      simpa only [mul_comm ((s : ℚ)^3), he, zero_mul, mul_zero] using hupp
  exact (R.mem_toInterval hs hR).mp
    (cubicBracketCheck_sound hcheck ((A.mem_toInterval hs hA).mpr ha) ((B.mem_toInterval hs hB).mpr hb))

end chebyshev2.Numerics.IntegerCertificate
