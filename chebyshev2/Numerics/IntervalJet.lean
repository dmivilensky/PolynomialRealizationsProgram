import chebyshev2.Numerics.JetRules
import chebyshev2.Numerics.RiccatiBounds

/-!
Article: chebyshev2, Section 4.1.
Finite rational jet witnesses.
Use: `chebyshev2.Numerics.mem_sumIntervals` feeds `chebyshev2.Numerics.mem_cubicJetStep`
(mem cubic Jet Step).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
open Set LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Defines `IntervalJet` of type `` by `List IntervalRat`.

Use: `chebyshev2.Numerics.convolution` uses this definition in the displayed construction
of `convolution`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Section 4.1.
-/
abbrev IntervalJet := List IntervalRat

/--
Defines `jetAt` of type `IntervalRat` by `J[j]?.getD (IntervalRat.singleton 0)`.

Use: `chebyshev2.Numerics.convolution` uses this definition in the displayed construction
of `convolution`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Section 4.1.
-/
def jetAt (J : IntervalJet) (j : ℕ) : IntervalRat := J[j]?.getD (IntervalRat.singleton 0)

/--
Defines `sumIntervals` by pattern matching with result type `ℕ → IntervalRat`. The displayed
branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.convolution` uses this definition in the displayed construction
of `convolution`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def sumIntervals (J : ℕ → IntervalRat) : ℕ → IntervalRat
  | 0 => IntervalRat.singleton 0
  | n+1 => roundHigh (IntervalRat.add (sumIntervals J n) (J n))

/--
Membership in the specified domain/enclosure: `(∑ j∈Finset.range n,f j)∈sumIntervals J n`.

Use: `chebyshev2.Numerics.mem_convolution` uses this assertion to establish membership in
the specified domain/enclosure: `(∑ i∈Finset.range (j+1),f i*g (j-i))∈convolution J K j`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem mem_sumIntervals {J : ℕ → IntervalRat} {f : ℕ → ℝ} (n : ℕ)
    (h : ∀ j<n,f j∈J j) : (∑ j∈Finset.range n,f j)∈sumIntervals J n := by
  induction n with
  | zero => simpa only [Finset.sum_range_zero,sumIntervals,Rat.cast_zero] using IntervalRat.mem_singleton 0
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact mem_roundHigh (IntervalRat.mem_add (ih (fun j hj => h j (by omega))) (h n (by omega)))

/--
Defines `convolution` of type `IntervalRat` by `sumIntervals (fun i => roundHigh
(IntervalRat.mul (jetAt J i) (jetAt K (j-i)))) (j+1)`.

Use: `chebyshev2.Numerics.mem_convolution` uses this definition to establish membership in
the specified domain/enclosure: `(∑ i∈Finset.range (j+1),f i*g (j-i))∈convolution J K j`.

Article: chebyshev2, Section 4.1.
-/
def convolution (J K : IntervalJet) (j : ℕ) : IntervalRat :=
  sumIntervals (fun i => roundHigh (IntervalRat.mul (jetAt J i) (jetAt K (j-i)))) (j+1)

/--
Membership in the specified domain/enclosure: `(∑ i∈Finset.range (j+1),f i*g (j-i))∈convolution
J K j`.

Use: `chebyshev2.Numerics.mulJet_encloses` uses this assertion to establish the stated
quantitative bound `JetEncloses (mulJet J K N) (fun t => f t*g t) s x N`.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates `chebyshev2.Numerics.mem_sumIntervals`,
`chebyshev2.Numerics.mem_roundHigh` with the arguments shown in the proof.
-/
theorem mem_convolution {J K : IntervalJet} {f g : ℕ → ℝ} (j : ℕ)
    (hf : ∀ i≤j,f i∈jetAt J i) (hg : ∀ i≤j,g i∈jetAt K i) :
    (∑ i∈Finset.range (j+1),f i*g (j-i))∈convolution J K j := by
  apply mem_sumIntervals
  intro i hi
  exact mem_roundHigh (IntervalRat.mem_mul (hf i (by omega)) (hg (j-i) (Nat.sub_le _ _)))

/--
Defines `squareConvolution` of type `IntervalRat` by `sumIntervals (fun i => if i=j-i then
squareHigh (jetAt J i) else roundHigh (IntervalRat.mul (jetAt J i) (jetAt J (j-i)))) (j+1)`.

Use: `chebyshev2.Numerics.riccatiJetRhs` uses this definition in the displayed construction
of `riccatiJetRhs`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Section 4.1.
-/
def squareConvolution (J : IntervalJet) (j : ℕ) : IntervalRat :=
  sumIntervals (fun i => if i=j-i then squareHigh (jetAt J i)
    else roundHigh (IntervalRat.mul (jetAt J i) (jetAt J (j-i)))) (j+1)

/--
Membership in the specified domain/enclosure: `(∑ i∈Finset.range (j+1),f i*f
(j-i))∈squareConvolution J j`.

Use: `chebyshev2.Numerics.mem_riccatiJetStep` uses this assertion to establish membership
in the specified domain/enclosure: `((c j+a j*y+b j*y^2)+ (∑ i∈Finset.range (j+1),(a i+2*b
i*y)*ρ (j-i))+ ∑ i∈Finset.range (j+1),b i*∑ k∈Finset.range (j-i+1),ρ k*ρ (j-i-k))/(j+1)
∈riccatiJetStep C A B R Y j`.

Article: chebyshev2, Section 4.1.

Proof: Separate `i=j-i` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem mem_squareConvolution {J : IntervalJet} {f : ℕ → ℝ} (j : ℕ)
    (hf : ∀ i≤j,f i∈jetAt J i) :
    (∑ i∈Finset.range (j+1),f i*f (j-i))∈squareConvolution J j := by
  -- Separate `i=j-i` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply mem_sumIntervals
  intro i hi
  by_cases h : i=j-i
  · rw [ite_eq_left h,← h,← pow_two]
    exact mem_squareHigh (hf i (by omega))
  · rw [ite_eq_right h]
    exact mem_roundHigh (IntervalRat.mem_mul (hf i (by omega)) (hf (j-i) (Nat.sub_le _ _)))

/--
Defines `shiftedConstant` of type `IntervalRat` by `roundHigh (IntervalRat.add (IntervalRat.add
(jetAt C j) (IntervalRat.mul (jetAt A j) Y)) (IntervalRat.mul (jetAt B j) (squareHigh Y)))`.

Use: `chebyshev2.Numerics.mem_riccatiJetStep` uses this definition to establish membership
in the specified domain/enclosure: `((c j+a j*y+b j*y^2)+ (∑ i∈Finset.range (j+1),(a i+2*b
i*y)*ρ (j-i))+ ∑ i∈Finset.range (j+1),b i*∑ k∈Finset.range (j-i+1),ρ k*ρ (j-i-k))/(j+1)
∈riccatiJetStep C A B R Y j`.

Article: chebyshev2, Section 4.1.
-/
def shiftedConstant (C A B : IntervalJet) (Y : IntervalRat) (j : ℕ) : IntervalRat :=
  roundHigh (IntervalRat.add (IntervalRat.add (jetAt C j) (IntervalRat.mul (jetAt A j) Y))
    (IntervalRat.mul (jetAt B j) (squareHigh Y)))

/--
Defines `shiftedLinear` of type `IntervalRat` by `roundHigh (IntervalRat.add (jetAt A j)
(IntervalRat.mul (IntervalRat.singleton 2) (IntervalRat.mul (jetAt B j) Y)))`.

Use: `chebyshev2.Numerics.mem_riccatiJetStep` uses this definition to establish membership
in the specified domain/enclosure: `((c j+a j*y+b j*y^2)+ (∑ i∈Finset.range (j+1),(a i+2*b
i*y)*ρ (j-i))+ ∑ i∈Finset.range (j+1),b i*∑ k∈Finset.range (j-i+1),ρ k*ρ (j-i-k))/(j+1)
∈riccatiJetStep C A B R Y j`.

Article: chebyshev2, Section 4.1.
-/
def shiftedLinear (A B : IntervalJet) (Y : IntervalRat) (j : ℕ) : IntervalRat :=
  roundHigh (IntervalRat.add (jetAt A j)
    (IntervalRat.mul (IntervalRat.singleton 2) (IntervalRat.mul (jetAt B j) Y)))

/--
Defines `riccatiJetRhs` of type `IntervalRat` by `roundHigh (IntervalRat.add (shiftedConstant C
A B Y j) (IntervalRat.add (sumIntervals (fun i => roundHigh (IntervalRat.mul (shiftedLinear A B
Y i) (jetAt R (j-i)))) (j+1)) (sumIntervals (fun i => roundHigh (IntervalRat.mul (jetAt B i)
(squareConvolution R (j-i)))) (j+1))))`.

Use: `chebyshev2.Numerics.riccatiJetStep` uses this definition in the displayed
construction of `riccatiJetStep`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Section 4.1.
-/
def riccatiJetRhs (C A B R : IntervalJet) (Y : IntervalRat) (j : ℕ) : IntervalRat :=
  roundHigh (IntervalRat.add (shiftedConstant C A B Y j)
    (IntervalRat.add
      (sumIntervals (fun i => roundHigh (IntervalRat.mul (shiftedLinear A B Y i) (jetAt R (j-i)))) (j+1))
      (sumIntervals (fun i => roundHigh (IntervalRat.mul (jetAt B i) (squareConvolution R (j-i)))) (j+1))))

/--
Defines `riccatiJetStep` of type `IntervalRat` by `roundHigh (IntervalRat.mul
(IntervalRat.singleton ((j+1:ℚ)⁻¹)) (riccatiJetRhs C A B R Y j))`.

Use: `chebyshev2.Numerics.mem_riccatiJetStep` uses this definition to establish membership
in the specified domain/enclosure: `((c j+a j*y+b j*y^2)+ (∑ i∈Finset.range (j+1),(a i+2*b
i*y)*ρ (j-i))+ ∑ i∈Finset.range (j+1),b i*∑ k∈Finset.range (j-i+1),ρ k*ρ (j-i-k))/(j+1)
∈riccatiJetStep C A B R Y j`.

Article: chebyshev2, Section 4.1.
-/
def riccatiJetStep (C A B R : IntervalJet) (Y : IntervalRat) (j : ℕ) : IntervalRat :=
  roundHigh (IntervalRat.mul (IntervalRat.singleton ((j+1:ℚ)⁻¹)) (riccatiJetRhs C A B R Y j))

/--
Membership in the specified domain/enclosure: `((c j+a j*y+b j*y^2)+ (∑ i∈Finset.range (j+1),(a
i+2*b i*y)*ρ (j-i))+ ∑ i∈Finset.range (j+1),b i*∑ k∈Finset.range (j-i+1),ρ k*ρ (j-i-k))/(j+1)
∈riccatiJetStep C A B R Y j`.

Use: `chebyshev2.Numerics.riccatiJetCheck_sound` uses this assertion to establish
establishes the uniform, quantified assertion `∀ j≤N,normalizedWithin (fun t => y t-y x) s j
x∈jetAt R j`.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates `chebyshev2.Numerics.mem_roundHigh`,
`chebyshev2.Numerics.mem_squareHigh`, `chebyshev2.Numerics.mem_sumIntervals` with the
arguments shown in the proof.
-/
theorem mem_riccatiJetStep {C A B R : IntervalJet} {Y : IntervalRat}
    {c a b ρ : ℕ → ℝ} {y : ℝ} (j : ℕ)
    (hc : ∀ i≤j,c i∈jetAt C i) (ha : ∀ i≤j,a i∈jetAt A i)
    (hb : ∀ i≤j,b i∈jetAt B i) (hρ : ∀ i≤j,ρ i∈jetAt R i) (hy : y∈Y) :
    ((c j+a j*y+b j*y^2)+
      (∑ i∈Finset.range (j+1),(a i+2*b i*y)*ρ (j-i))+
      ∑ i∈Finset.range (j+1),b i*∑ k∈Finset.range (j-i+1),ρ k*ρ (j-i-k))/(j+1)
      ∈riccatiJetStep C A B R Y j := by
  -- Use the identities/estimates `chebyshev2.Numerics.mem_roundHigh`,
  -- `chebyshev2.Numerics.mem_squareHigh`, `chebyshev2.Numerics.mem_sumIntervals` with
  -- the arguments shown in the proof.
  have hC : c j+a j*y+b j*y^2∈shiftedConstant C A B Y j :=
    mem_roundHigh (IntervalRat.mem_add (IntervalRat.mem_add (hc j le_rfl)
      (IntervalRat.mem_mul (ha j le_rfl) hy)) (IntervalRat.mem_mul (hb j le_rfl) (mem_squareHigh hy)))
  have hA : ∀ i≤j,a i+2*b i*y∈shiftedLinear A B Y i := by
    intro i hi
    apply mem_roundHigh
    simpa only [mul_assoc,Rat.cast_ofNat] using IntervalRat.mem_add (ha i hi)
      (IntervalRat.mem_mul (IntervalRat.mem_singleton 2) (IntervalRat.mem_mul (hb i hi) hy))
  have hsumA := mem_sumIntervals (j+1) (fun i hi => mem_roundHigh
    (IntervalRat.mem_mul (hA i (by omega)) (hρ (j-i) (Nat.sub_le _ _))))
  have hsumB := mem_sumIntervals (j+1) (fun i hi => mem_roundHigh
    (IntervalRat.mem_mul (hb i (by omega)) (mem_squareConvolution (j-i)
      (fun k hk => hρ k (hk.trans (Nat.sub_le _ _))))))
  have hrhs := mem_roundHigh (IntervalRat.mem_add hC (IntervalRat.mem_add hsumA hsumB))
  have hm := mem_roundHigh (IntervalRat.mem_mul (IntervalRat.mem_singleton ((j+1:ℚ)⁻¹)) hrhs)
  simpa only [riccatiJetStep,riccatiJetRhs,Rat.cast_inv,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,
    mul_add,div_eq_mul_inv,mul_comm,add_assoc] using hm

/--
Defines `riccatiJetCheck` of type `Bool` by `decide ((jetAt R 0).lo≤0 ∧ 0≤(jetAt R 0).hi) &&
(List.range N).all (fun j => intervalSubsetCheck (riccatiJetStep C A B R Y j) (jetAt R
(j+1)))`.

Use: `chebyshev2.Numerics.riccatiJetCheck_sound` uses this definition to establish
establishes the uniform, quantified assertion `∀ j≤N,normalizedWithin (fun t => y t-y x) s j
x∈jetAt R j`.

Article: chebyshev2, Section 4.1.
-/
def riccatiJetCheck (C A B R : IntervalJet) (Y : IntervalRat) (N : ℕ) : Bool :=
  decide ((jetAt R 0).lo≤0 ∧ 0≤(jetAt R 0).hi) &&
    (List.range N).all (fun j => intervalSubsetCheck (riccatiJetStep C A B R Y j) (jetAt R (j+1)))

/--
Establishes the uniform, quantified assertion `∀ j≤N,normalizedWithin (fun t => y t-y x) s j
x∈jetAt R j`.

Use: `chebyshev2.Numerics.FlowStep.check_range_sound` uses this identity to establish
membership in the specified domain/enclosure: `y (a+v)∈W.rangeEnclosure V`.

Article: chebyshev2, Section 4.1.

Proof: Induct on `j`; the recursive step uses the previous-stage assertion.
-/
theorem riccatiJetCheck_sound {C A B R : IntervalJet} {Y : IntervalRat} {N : ℕ}
    (hcheck : riccatiJetCheck C A B R Y N=true)
    {c a b y : ℝ → ℝ} {s : Set ℝ} {x : ℝ} (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (hC : ContDiffWithinAt ℝ N c s x) (hA : ContDiffWithinAt ℝ N a s x)
    (hB : ContDiffWithinAt ℝ N b s x) (hy : ContDiffWithinAt ℝ N y s x)
    (hd : ∀ t∈s,HasDerivWithinAt y (c t+a t*y t+b t*y t^2) s t)
    (hCI : ∀ j<N,normalizedWithin c s j x∈jetAt C j)
    (hAI : ∀ j<N,normalizedWithin a s j x∈jetAt A j)
    (hBI : ∀ j<N,normalizedWithin b s j x∈jetAt B j) (hyY : y x∈Y) :
    ∀ j≤N,normalizedWithin (fun t => y t-y x) s j x∈jetAt R j := by
  -- Induct on `j`; the recursive step uses the previous-stage assertion.
  have hparts : decide ((jetAt R 0).lo≤0 ∧ 0≤(jetAt R 0).hi)=true ∧
      (List.range N).all (fun j => intervalSubsetCheck (riccatiJetStep C A B R Y j) (jetAt R (j+1)))=true := by
    simpa only [riccatiJetCheck,Bool.and_eq_true] using hcheck
  have hchecks : (jetAt R 0).lo≤0 ∧ 0≤(jetAt R 0).hi := by
    exact of_decide_eq_true hparts.1
  have hsteps : ∀ j<N,intervalSubsetCheck (riccatiJetStep C A B R Y j) (jetAt R (j+1))=true := by
    simpa only [List.all_eq_true,List.mem_range] using hparts.2
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
   cases j with
   | zero =>
    intro _
    simp only [normalizedWithin_zero,sub_self]
    constructor
    · exact_mod_cast hchecks.1
    · exact_mod_cast hchecks.2
   | succ j =>
    intro hj
    have hjN : j<N := by omega
    have hr : ∀ i≤j,normalizedWithin (fun t => y t-y x) s i x∈jetAt R i := by
      intro i hi
      exact ih i (by omega) (by omega)
    have hm := mem_riccatiJetStep j
      (fun i hi => hCI i (by omega)) (fun i hi => hAI i (by omega)) (fun i hi => hBI i (by omega)) hr hyY
    have he := normalizedWithin_shifted_riccati hs hx
      (hC.of_le (by exact_mod_cast (Nat.le_of_lt hjN)))
      (hA.of_le (by exact_mod_cast (Nat.le_of_lt hjN)))
      (hB.of_le (by exact_mod_cast (Nat.le_of_lt hjN)))
      (hy.of_le (by exact_mod_cast (Nat.le_of_lt hjN))) hd (y x)
    have hj0 : (j:ℝ)+1≠0 := by positivity
    rw [← he,mul_div_cancel_left₀ _ hj0] at hm
    rw [normalizedWithin_sub_const (by omega)]
    exact intervalSubsetCheck_sound (hsteps j hjN) hm

end chebyshev2.Numerics
