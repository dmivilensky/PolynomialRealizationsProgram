import «2610.05164v2».Numerics.IntervalExpr

/-!
Article: 2610.05164v2, Section 4.1.
The finite tube premise (51) and one-sided slope enclosure for Lemma 21.
Use: `«2610.05164v2».Numerics.intervalSubsetCheck_sound` feeds
`«2610.05164v2».Numerics.ReferenceCoreSource.calibration_constant_enclosed` (calibration constant
enclosed).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics
open LeanCert.Core Set
set_option autoImplicit false

/--
Defines `riccatiImage` of type `IntervalRat` by `IntervalRat.add C (IntervalRat.add
(IntervalRat.mul A Y) (IntervalRat.mul B (IntervalRat.mul Y Y)))`.

Use: `«2610.05164v2».Numerics.flowTubeCheck` uses this definition in the displayed construction
of `flowTubeCheck`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def riccatiImage (C A B Y : IntervalRat) : IntervalRat :=
  IntervalRat.add C (IntervalRat.add (IntervalRat.mul A Y)
    (IntervalRat.mul B (IntervalRat.mul Y Y)))

 /--
Membership in the specified domain/enclosure: `c+a*y+b*y^2∈riccatiImage C A B Y`.

Use: `«2610.05164v2».Numerics.flowTubeCheck_sound` uses this assertion to establish membership
in the specified domain/enclosure: `y0+θ*(c+a*y+b*y^2)∈Y`.

Article: 2610.05164v2, Section 4.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem mem_riccatiImage {C A B Y : IntervalRat} {c a b y : ℝ}
    (hc : c∈C) (ha : a∈A) (hb : b∈B) (hy : y∈Y) : c+a*y+b*y^2∈riccatiImage C A B Y := by
  simpa only [riccatiImage,pow_two,add_assoc,mul_assoc] using
    IntervalRat.mem_add hc (IntervalRat.mem_add (IntervalRat.mem_mul ha hy)
      (IntervalRat.mem_mul hb (IntervalRat.mem_mul hy hy)))

/--
Defines `intervalSubsetCheck` of type `Bool` by `decide (J.lo≤I.lo ∧ I.hi≤J.hi)`.

Use: `«2610.05164v2».Numerics.flowTubeCheck` uses this definition in the displayed construction
of `flowTubeCheck`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def intervalSubsetCheck (I J : IntervalRat) : Bool := decide (J.lo≤I.lo ∧ I.hi≤J.hi)

 /--
Membership in the specified domain/enclosure: `x∈J`.

Use: `«2610.05164v2».Numerics.flowTubeCheck_sound` uses this assertion to establish membership
in the specified domain/enclosure: `y0+θ*(c+a*y+b*y^2)∈Y`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem intervalSubsetCheck_sound {I J : IntervalRat} (h : intervalSubsetCheck I J=true)
    {x : ℝ} (hx : x∈I) : x∈J := by
  have he : J.lo≤I.lo ∧ I.hi≤J.hi := of_decide_eq_true h
  have hlo : (J.lo:ℝ)≤I.lo := by exact_mod_cast he.1
  have hhi : (I.hi:ℝ)≤J.hi := by exact_mod_cast he.2
  exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩

/--
Defines `hullPoint` of type `IntervalRat` by `⟨min Y0.lo m,max Y0.hi m,(min_le_left _ _).trans
(Y0.le.trans (le_max_left _ _))⟩`.

Use: `«2610.05164v2».Numerics.flowTubeCheck` uses this definition in the displayed construction
of `flowTubeCheck`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def hullPoint (Y0 : IntervalRat) (m : ℚ) : IntervalRat :=
  ⟨min Y0.lo m,max Y0.hi m,(min_le_left _ _).trans (Y0.le.trans (le_max_left _ _))⟩

 /--
Membership in the specified domain/enclosure: `y∈hullPoint Y0 m`.

Use: `«2610.05164v2».Numerics.FlowStep.check_range_sound` uses this assertion to establish
membership in the specified domain/enclosure: `y (a+v)∈W.rangeEnclosure V`.

Article: 2610.05164v2, Section 4.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem mem_hullPoint {Y0 : IntervalRat} {y : ℝ} (hy : y∈Y0) (m : ℚ) : y∈hullPoint Y0 m := by
  have hlo : (min Y0.lo m:ℝ)≤Y0.lo := by exact_mod_cast min_le_left Y0.lo m
  have hhi : (Y0.hi:ℝ)≤max Y0.hi m := by exact_mod_cast le_max_left Y0.hi m
  constructor
  · simpa only [hullPoint,Rat.cast_min] using hlo.trans hy.1
  · simpa only [hullPoint,Rat.cast_max] using hy.2.trans hhi

 /--
Membership in the specified domain/enclosure: `(m:ℝ)∈hullPoint Y0 m`.

Use: `«2610.05164v2».Numerics.FlowStep.check_range_sound` uses this assertion to establish
membership in the specified domain/enclosure: `y (a+v)∈W.rangeEnclosure V`.

Article: 2610.05164v2, Section 4.1.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem center_mem_hullPoint (Y0 : IntervalRat) (m : ℚ) : (m:ℝ)∈hullPoint Y0 m := by
  constructor
  · exact_mod_cast min_le_right Y0.lo m
  · exact_mod_cast le_max_right Y0.hi m

/--
Defines `flowTubeCheck` of type `Bool` by `if hh : 0≤h then intervalSubsetCheck
(IntervalRat.add (hullPoint Y0 m) (IntervalRat.mul ⟨0,h,hh⟩ (riccatiImage C A B Y))) Y else
false`.

Use: `«2610.05164v2».Numerics.flowTubeCheck_nonneg` rewrites with this definition to establish
the stated quantitative bound `0≤h`.

Article: 2610.05164v2, Section 4.1.
-/
def flowTubeCheck (Y0 Y C A B : IntervalRat) (m h : ℚ) : Bool :=
  if hh : 0≤h then
    intervalSubsetCheck (IntervalRat.add (hullPoint Y0 m)
      (IntervalRat.mul ⟨0,h,hh⟩ (riccatiImage C A B Y))) Y
  else false

 /--
The stated quantitative bound `0≤h`.

Use: `«2610.05164v2».Numerics.flowTubeCheck_sound` uses this bound to establish membership in
the specified domain/enclosure: `y0+θ*(c+a*y+b*y^2)∈Y`.

Article: 2610.05164v2, Section 4.1.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem flowTubeCheck_nonneg {Y0 Y C A B : IntervalRat} {m h : ℚ}
    (hcheck : flowTubeCheck Y0 Y C A B m h=true) : 0≤h := by
  by_contra hh
  simp [flowTubeCheck,hh] at hcheck

 /--
Membership in the specified domain/enclosure: `y0+θ*(c+a*y+b*y^2)∈Y`.

Use: `«2610.05164v2».Numerics.flowTubeCheck_exists` uses this assertion to establish constructs
witnesses with the exact properties `∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Y) ∧ ∀ t∈Icc a
(a+h),HasDerivWithinAt y (C t+A t*y t+B t*y t^2) (Icc a (a+h)) t`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.flowTubeCheck_nonneg`,
`«2610.05164v2».Numerics.intervalSubsetCheck_sound`, `«2610.05164v2».Numerics.mem_riccatiImage`
with the arguments shown in the proof.
-/
theorem flowTubeCheck_sound {Y0 Y C A B : IntervalRat} {m h : ℚ}
    (hcheck : flowTubeCheck Y0 Y C A B m h=true) {c a b y y0 θ : ℝ}
    (hc : c∈C) (ha : a∈A) (hb : b∈B) (hy : y∈Y)
    (h0 : y0∈hullPoint Y0 m) (hθ : θ∈Icc (0:ℝ) h) :
    y0+θ*(c+a*y+b*y^2)∈Y := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.flowTubeCheck_nonneg`,
  -- `«2610.05164v2».Numerics.intervalSubsetCheck_sound`,
  -- `«2610.05164v2».Numerics.mem_riccatiImage` with the arguments shown in the proof.
  have hh := flowTubeCheck_nonneg hcheck
  have hsub : intervalSubsetCheck (IntervalRat.add (hullPoint Y0 m)
      (IntervalRat.mul ⟨0,h,hh⟩ (riccatiImage C A B Y))) Y=true := by
    simpa [flowTubeCheck,hh] using hcheck
  exact intervalSubsetCheck_sound hsub (IntervalRat.mem_add h0
    (IntervalRat.mem_mul (by simpa [IntervalRat.mem_def] using hθ : θ∈(⟨0,h,hh⟩:IntervalRat))
      (mem_riccatiImage hc ha hb hy)))

/--
Defines `riccatiSlope` of type `IntervalRat` by `IntervalRat.add A (IntervalRat.mul
(IntervalRat.singleton 2) (IntervalRat.mul B Y))`.

Use: `«2610.05164v2».Numerics.riccatiSlope_upper` uses this definition to establish the stated
quantitative bound `a+2*b*y≤(riccatiSlope A B Y).hi`.

Article: 2610.05164v2, Section 4.1.
-/
def riccatiSlope (A B Y : IntervalRat) : IntervalRat :=
  IntervalRat.add A (IntervalRat.mul (IntervalRat.singleton 2) (IntervalRat.mul B Y))

 /--
The stated quantitative bound `a+2*b*y≤(riccatiSlope A B Y).hi`.

Use: `«2610.05164v2».Numerics.FlowStep.check_range_sound` uses this bound to establish
membership in the specified domain/enclosure: `y (a+v)∈W.rangeEnclosure V`.

Article: 2610.05164v2, Section 4.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem riccatiSlope_upper {A B Y : IntervalRat} {a b y : ℝ}
    (ha : a∈A) (hb : b∈B) (hy : y∈Y) : a+2*b*y≤(riccatiSlope A B Y).hi := by
  have he := IntervalRat.mem_add ha (IntervalRat.mem_mul (IntervalRat.mem_singleton 2)
    (IntervalRat.mem_mul hb hy))
  simpa only [riccatiSlope,Rat.cast_ofNat,mul_assoc] using he.2

end «2610.05164v2».Numerics
