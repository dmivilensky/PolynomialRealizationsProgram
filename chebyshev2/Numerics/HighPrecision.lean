import chebyshev2.Numerics.PiBounds
import LeanCert.Core.IntervalRat.Taylor
import LeanCert.Core.IntervalDyadic

/-!
Article: chebyshev2, Section 4.1.
The two occurrences denote the same real number.
Use: `chebyshev2.Numerics.mem_squareHigh` feeds `chebyshev2.Numerics.mem_riccatiJetStep`
(mem riccati Jet Step).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
open LeanCert.Core

/--
Outward dyadic rounding for the printed sine-energy certificate.

Use: `chebyshev2.Numerics.inverseHigh` uses this definition in the displayed construction
of `inverseHigh`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def roundHigh (I : IntervalRat) : IntervalRat :=
  (IntervalDyadic.ofIntervalRat I (-192)).toIntervalRat

/--
Membership in the specified domain/enclosure: `x ∈ roundHigh I`.

Use: `chebyshev2.Numerics.mem_inverseHigh` uses this assertion to establish membership in
the specified domain/enclosure: `x⁻¹ ∈ inverseHigh I`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem mem_roundHigh {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : x ∈ roundHigh I :=
  IntervalDyadic.mem_toIntervalRat.mp (IntervalDyadic.mem_ofIntervalRat hx (-192))

/--
Defines `piHigh` of type `IntervalRat` by
`⟨314159265358979323846264338327950288419716939937510/10^50,
314159265358979323846264338327950288419716939937511/10^50, by norm_num⟩`.

Use: `chebyshev2.Numerics.mem_piHigh` uses this definition to establish membership in the
specified domain/enclosure: `Real.pi ∈ piHigh`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def piHigh : IntervalRat :=
  ⟨314159265358979323846264338327950288419716939937510/10^50,
   314159265358979323846264338327950288419716939937511/10^50, by norm_num⟩

/--
Membership in the specified domain/enclosure: `Real.pi ∈ piHigh`.

Use: `chebyshev2.Certificates.DualInputs.TargetObservations.k_mem` uses this assertion to
establish membership in the specified domain/enclosure: `Real.pi^2/4∈kBox`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Numerics.pi_fifty_lower`,
`chebyshev2.Numerics.pi_fifty_upper` with the arguments shown in the proof.
-/
theorem mem_piHigh : Real.pi ∈ piHigh := by
  constructor
  · convert pi_fifty_lower.le using 1; norm_num [piHigh]
  · convert pi_fifty_upper.le using 1; norm_num [piHigh]

/--
Reciprocal enclosure; callers must prove positivity of the lower endpoint.

Use: `chebyshev2.Numerics.mem_inverseHigh` uses this definition to establish membership in
the specified domain/enclosure: `x⁻¹ ∈ inverseHigh I`.

Article: chebyshev2, Section 4.1.
-/
def inverseHigh (I : IntervalRat) : IntervalRat :=
  roundHigh ⟨min I.lo⁻¹ I.hi⁻¹,max I.lo⁻¹ I.hi⁻¹,min_le_max⟩

/--
Membership in the specified domain/enclosure: `x⁻¹ ∈ inverseHigh I`.

Use: `chebyshev2.Numerics.mem_cubicJetStep` uses this assertion to establish the assertion
stated in that declaration.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates `chebyshev2.Numerics.mem_roundHigh` with the arguments
shown in the proof.
-/
theorem mem_inverseHigh {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hp : 0 < I.lo) :
    x⁻¹ ∈ inverseHigh I := by
  apply mem_roundHigh
  have h₀ : (0:ℝ) < I.lo := by exact_mod_cast hp
  have h₁ := h₀.trans_le hx.1
  simp only [IntervalRat.mem_def,Rat.cast_min,Rat.cast_max,Rat.cast_inv]
  exact ⟨(min_le_right _ _).trans (inv_anti₀ h₁ hx.2),
    (inv_anti₀ h₀ hx.1).trans (le_max_left _ _)⟩

/--
Rounding after each multiplication prevents denominator growth.

Use: `chebyshev2.Numerics.mem_powerHigh` uses this definition to establish membership in
the specified domain/enclosure: `x^j ∈ powerHigh I j`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def powerHigh (I : IntervalRat) : ℕ → IntervalRat
  | 0 => IntervalRat.singleton 1
  | j+1 => roundHigh (IntervalRat.mul I (powerHigh I j))

/--
Membership in the specified domain/enclosure: `x^j ∈ powerHigh I j`.

Use: `chebyshev2.Numerics.FlowStep.check_range_sound` uses this assertion to establish
membership in the specified domain/enclosure: `y (a+v)∈W.rangeEnclosure V`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `j`; the recursive step uses the previous-stage assertion.
-/
theorem mem_powerHigh {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (j : ℕ) :
    x^j ∈ powerHigh I j := by
  induction j with
  | zero => simpa only [pow_zero,powerHigh,Rat.cast_one] using IntervalRat.mem_singleton 1
  | succ j ih =>
    simpa only [powerHigh,pow_succ'] using mem_roundHigh (IntervalRat.mem_mul hx ih)

/--
The two occurrences denote the same real number. A square stays nonnegative even when its input
interval straddles zero.

Use: `chebyshev2.Numerics.mem_squareHigh` uses this definition to establish membership in
the specified domain/enclosure: `x^2∈squareHigh I`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def squareHigh (I : IntervalRat) : IntervalRat :=
  roundHigh (if h : 0≤I.lo then ⟨I.lo^2,I.hi^2,by nlinarith [I.le]⟩
    else if h' : I.hi≤0 then ⟨I.hi^2,I.lo^2,by nlinarith [I.le]⟩
    else ⟨0,max (I.lo^2) (I.hi^2),le_max_of_le_left (sq_nonneg _)⟩)

/--
Membership in the specified domain/enclosure: `x^2∈squareHigh I`.

Use: `chebyshev2.Certificates.DualInputs.TargetObservations.k_mem` uses this assertion to
establish membership in the specified domain/enclosure: `Real.pi^2/4∈kBox`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Separate `0≤I.lo` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem mem_squareHigh {x : ℝ} {I : IntervalRat} (hx : x∈I) : x^2∈squareHigh I := by
  -- Separate `0≤I.lo` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply mem_roundHigh
  by_cases h : 0≤I.lo
  · simp only [dite_eq_left h,IntervalRat.mem_def,Rat.cast_pow]
    have hl : (0:ℝ)≤I.lo := by exact_mod_cast h
    constructor <;> nlinarith [hx.1,hx.2]
  · by_cases h' : I.hi≤0
    · simp only [dite_eq_right h,dite_eq_left h',IntervalRat.mem_def,Rat.cast_pow]
      have hu : (I.hi:ℝ)≤0 := by exact_mod_cast h'
      constructor <;> nlinarith [hx.1,hx.2]
    · simp only [dite_eq_right h,dite_eq_right h',IntervalRat.mem_def,Rat.cast_zero,Rat.cast_max,Rat.cast_pow]
      refine ⟨sq_nonneg _,?_⟩
      rcases le_total 0 x with hp | hn
      · exact (by nlinarith [hx.2] : x^2≤(I.hi:ℝ)^2).trans (le_max_right _ _)
      · exact (by nlinarith [hx.1] : x^2≤(I.lo:ℝ)^2).trans (le_max_left _ _)

end chebyshev2.Numerics
