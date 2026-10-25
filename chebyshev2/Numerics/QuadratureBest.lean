import chebyshev2.Numerics.QuadratureJet

/-!
Article: chebyshev2, Lemma 20.
`chebyshev2.Numerics.quadratureBestEnclosure_sound` selects the narrowest sound Taylor enclosure
without assuming higher order improves it.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.quadrature_taylor_even`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set MeasureTheory LeanCert.Core
set_option autoImplicit false

/--
Defines `quadratureRangeEnclosure` of type `IntervalRat` by `let lo := 2*h*(jetAt whole 0).lo
let hi := 2*h*(jetAt whole 0).hi ⟨min lo hi,max lo hi,min_le_max⟩`.

Use: `chebyshev2.Numerics.quadratureRangeEnclosure_sound` uses this definition to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈quadratureRangeEnclosure
whole h`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def quadratureRangeEnclosure (whole : IntervalJet) (h : ℚ) : IntervalRat :=
  let lo := 2*h*(jetAt whole 0).lo
  let hi := 2*h*(jetAt whole 0).hi
  ⟨min lo hi,max lo hi,min_le_max⟩

/--
Membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈quadratureRangeEnclosure
whole h`.

Use: `chebyshev2.Numerics.quadratureBestEnclosure_sound` uses this assertion to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈quadratureBestEnclosure
point whole h n`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.normalizedWithin_zero` with the
arguments shown in the proof.
-/
theorem quadratureRangeEnclosure_sound {whole : IntervalJet} {h : ℚ} (hh : 0≤h)
    {n : ℕ} {f : ℝ → ℝ} {c : ℝ}
    (hf : ContDiffOn ℝ (n+1) f (Icc (c-h) (c+h)))
    (hwhole : ∀ t∈Icc (c-h) (c+h),JetEncloses whole f (Icc (c-h) (c+h)) t (n+1)) :
    (∫ t in c-h..c+h,f t)∈quadratureRangeEnclosure whole h := by
  -- Use the identities/estimates `chebyshev2.Numerics.normalizedWithin_zero` with the
  -- arguments shown in the proof.
  have hhr : (0:ℝ)≤h := by exact_mod_cast hh
  have hab : c-h≤c+h := by linarith
  have hInt : IntervalIntegrable f volume (c-h) (c+h) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hf.continuousOn
  have hv : ∀ t∈Icc (c-h) (c+h),f t∈jetAt whole 0 := by
    intro t ht
    simpa only [normalizedWithin_zero] using hwhole t ht 0 (by omega)
  have hlo := intervalIntegral.integral_mono_on hab (intervalIntegrable_const) hInt
    (fun t ht => (hv t ht).1)
  have hhi := intervalIntegral.integral_mono_on hab hInt (intervalIntegrable_const)
    (fun t ht => (hv t ht).2)
  have he : c+(h:ℝ)-(c-h)=2*h := by ring
  simp only [intervalIntegral.integral_const,smul_eq_mul,he] at hlo hhi
  have horder : 2*h*(jetAt whole 0).lo≤2*h*(jetAt whole 0).hi :=
    mul_le_mul_of_nonneg_left (jetAt whole 0).le (by linarith)
  simpa only [IntervalRat.mem_def,quadratureRangeEnclosure,min_eq_left horder,max_eq_right horder,
    Rat.cast_mul,Rat.cast_ofNat] using And.intro hlo hhi

/--
Defines `quadratureBestEnclosure` by pattern matching with result type `ℕ → IntervalRat`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.quadratureBestEnclosure_sound` uses this definition to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈quadratureBestEnclosure
point whole h n`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def quadratureBestEnclosure (point whole : IntervalJet) (h : ℚ) : ℕ → IntervalRat
  | 0 =>
    let taylor := quadratureJetEnclosure point whole h 0
    let range := quadratureRangeEnclosure whole h
    if range.hi-range.lo≤taylor.hi-taylor.lo then range else taylor
  | n+1 =>
    let previous := quadratureBestEnclosure point whole h n
    let next := quadratureJetEnclosure point whole h (n+1)
    if next.hi-next.lo≤previous.hi-previous.lo then next else previous

/--
Membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈quadratureBestEnclosure
point whole h n`.

Use: `chebyshev2.Numerics.ActualJetCell.integral_enclosed` uses this assertion to establish
membership in the specified domain/enclosure: `(∫ t in (c.domain.lo:ℝ)..c.domain.hi,f
t)∈c.integralBox`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem quadratureBestEnclosure_sound {point whole : IntervalJet} {h : ℚ} (hh : 0≤h)
    {n : ℕ} {f : ℝ → ℝ} {c : ℝ}
    (hf : ContDiffOn ℝ (n+1) f (Icc (c-h) (c+h)))
    (hpoint : JetEncloses point f (Icc (c-h) (c+h)) c (n+1))
    (hwhole : ∀ t∈Icc (c-h) (c+h),JetEncloses whole f (Icc (c-h) (c+h)) t (n+1)) :
    (∫ t in c-h..c+h,f t)∈quadratureBestEnclosure point whole h n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero =>
    have hrange := quadratureRangeEnclosure_sound hh hf hwhole
    have htaylor := quadratureJetEnclosure_sound hh hf hpoint hwhole
    dsimp only [quadratureBestEnclosure]
    split_ifs
    · exact hrange
    · exact htaylor
  | succ n ih =>
    have previous := ih (hf.of_le (by exact_mod_cast Nat.le_succ (n+1)))
      (fun j hj => hpoint j (by omega)) (fun t ht j hj => hwhole t ht j (by omega))
    have next := quadratureJetEnclosure_sound hh hf hpoint hwhole
    dsimp only [quadratureBestEnclosure]
    split_ifs
    · exact next
    · exact previous

end chebyshev2.Numerics
