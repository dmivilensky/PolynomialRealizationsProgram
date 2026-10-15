import «2610.05164v2».Finite.NormalizedEnergy
import Mathlib.Topology.Order.LiminfLimsup

/-!
Article: 2610.05164v2, Theorem 1.1.
The sine upper bound implied by Theorem 2.5.
Result: `«2610.05164v2».Optimal.gainConstant_le_sine` supplies the stated article conclusion.
-/
namespace «2610.05164v2».Optimal
noncomputable section
open «2606.16671v2» Real Filter Topology
set_option backward.isDefEq.respectTransparency false

/--
Horizon n+1 avoids an irrelevant zero-horizon convention in the liminf.

Use: `«2610.05164v2».Optimal.finiteEnergy` uses this definition in the displayed construction
of `finiteEnergy`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_ge_one`.
-/
def energyValues (n : ℕ) := Set.range (fun J : Fiber (n+1) => J.val.normalizedEnergy)
/--
Defines `finiteEnergy` of type `ℝ` by `sInf (energyValues n)`.

Use: `«2610.05164v2».Optimal.finiteGain_ge_two` uses this definition to establish the stated
quantitative bound `2 ≤ finiteGain I n`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_ge_one`.
-/
def finiteEnergy (n : ℕ) : ℝ := sInf (energyValues n)
/--
Defines `gainValues` of type `(I : SpectralInterval) (n : ℕ)` by `Set.range (fun R :
ExactRecurrence I (n+1) => R.val.normalizedGain I)`.

Use: `«2610.05164v2».Optimal.finiteGain` uses this definition in the displayed construction of
`finiteGain`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_lower`.
-/
def gainValues (I : SpectralInterval) (n : ℕ) := Set.range
  (fun R : ExactRecurrence I (n+1) => R.val.normalizedGain I)
/--
Defines `finiteGain` of type `ℝ` by `sInf (gainValues I n)`.

Use: `«2610.05164v2».Optimal.finiteGain_interval_independent` uses this definition to establish
exact identity `finiteGain I n = finiteGain K n`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_lower`.
-/
def finiteGain (I : SpectralInterval) (n : ℕ) : ℝ := sInf (gainValues I n)
/--
Defines `greenConstant` of type `ℝ` by `liminf finiteEnergy atTop`.

Use: `«2610.05164v2».Optimal.gainConstant_lower` rewrites with this definition to establish the
stated quantitative bound `2*sqrt greenConstant ≤ gainConstant I`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_ge_one`.
-/
def greenConstant : ℝ := liminf finiteEnergy atTop
/--
Defines `gainConstant` of type `ℝ` by `liminf (finiteGain I) atTop`.

Use: `«2610.05164v2».Optimal.gainConstant_interval_independent` uses this definition to
establish exact identity `gainConstant I = gainConstant K`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_lower`.
-/
def gainConstant (I : SpectralInterval) : ℝ := liminf (finiteGain I) atTop

/--
The precise assertion is `(energyValues n).Nonempty`.

Use: `«2610.05164v2».Optimal.finiteEnergy_ge_one` uses this assertion to establish the stated
quantitative bound `1 ≤ finiteEnergy n`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_ge_one`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem energyValues_nonempty (n : ℕ) : (energyValues n).Nonempty :=
  ⟨_,⟨SineJacobi.fiber (n+1) (by omega),rfl⟩⟩

/--
The precise assertion is `BddBelow (energyValues n)`.

Use: `«2610.05164v2».Optimal.finiteEnergy_le` uses this assertion to establish the stated
quantitative bound `finiteEnergy n ≤ J.val.normalizedEnergy`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_le_sine`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.normalizedEnergy_ge_one` with the
arguments shown in the proof.
-/
theorem energyValues_bddBelow (n : ℕ) : BddBelow (energyValues n) := by
  refine ⟨1, ?_⟩
  rintro x ⟨J,rfl⟩
  exact J.val.normalizedEnergy_ge_one (by omega) J.property

/--
The stated quantitative bound `1 ≤ finiteEnergy n`.

Use: `«2610.05164v2».Optimal.energy_bounded_below` uses this bound to establish the stated
quantitative bound `IsBoundedUnder (· ≥ ·) atTop finiteEnergy`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_ge_one`.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.energyValues_nonempty`,
`«2610.05164v2».Jacobi.normalizedEnergy_ge_one` with the arguments shown in the proof.
-/
theorem finiteEnergy_ge_one (n : ℕ) : 1 ≤ finiteEnergy n := by
  apply le_csInf (energyValues_nonempty n)
  rintro x ⟨J,rfl⟩
  exact J.val.normalizedEnergy_ge_one (by omega) J.property

/--
The stated quantitative bound `finiteEnergy n ≤ J.val.normalizedEnergy`.

Use: `«2610.05164v2».Optimal.energy_bounded_above` uses this bound to establish the stated
quantitative bound `IsBoundedUnder (· ≤ ·) atTop finiteEnergy`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_le_sine`.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.energyValues_bddBelow` with the
arguments shown in the proof.
-/
theorem finiteEnergy_le (n : ℕ) (J : Fiber (n+1)) : finiteEnergy n ≤ J.val.normalizedEnergy :=
  csInf_le (energyValues_bddBelow n) ⟨J,rfl⟩

/--
Exact identity `gainValues I n = Set.range (fun J : Fiber (n+1) => ((recurrenceEquiv I (n+1)
(by omega)) J).val.normalizedGain I)`.

Use: `«2610.05164v2».Optimal.finiteGain_interval_independent` rewrites with this identity to
establish exact identity `finiteGain I n = finiteGain K n`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_lower`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem gainValues_eq_jacobi (I : SpectralInterval) (n : ℕ) : gainValues I n = Set.range
    (fun J : Fiber (n+1) => ((recurrenceEquiv I (n+1) (by omega)) J).val.normalizedGain I) := by
  ext x
  constructor
  · rintro ⟨R,rfl⟩
    exact ⟨(recurrenceEquiv I (n+1) (by omega)).symm R, by simp⟩
  · rintro ⟨J,rfl⟩; exact ⟨(recurrenceEquiv I (n+1) (by omega)) J,rfl⟩

/--
Exact identity `finiteGain I n = finiteGain K n`.

Use: `«2610.05164v2».Optimal.gainConstant_interval_independent` uses this identity to establish
exact identity `gainConstant I = gainConstant K`.

Article: 2610.05164v2, Theorem 1.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem finiteGain_interval_independent (I K : SpectralInterval) (n : ℕ) :
    finiteGain I n = finiteGain K n := by
  unfold finiteGain
  rw [gainValues_eq_jacobi I n, gainValues_eq_jacobi K n]
  apply congrArg sInf
  apply congrArg Set.range
  funext J
  exact J.val.normalized_gain_interval_independent I K (by omega) J.property

/--
The precise assertion is `(gainValues I n).Nonempty`.

Use: `«2610.05164v2».Optimal.finiteGain_lower` uses this assertion to establish the stated
quantitative bound `2*sqrt (finiteEnergy n) ≤ finiteGain I n`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_lower`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem gainValues_nonempty (I : SpectralInterval) (n : ℕ) : (gainValues I n).Nonempty :=
  ⟨_,⟨(recurrenceEquiv I (n+1) (by omega)) (SineJacobi.fiber (n+1) (by omega)),rfl⟩⟩

/--
The stated quantitative bound `2*sqrt (finiteEnergy n) ≤ finiteGain I n`.

Use: `«2610.05164v2».Optimal.finiteGain_ge_two` uses this bound to establish the stated
quantitative bound `2 ≤ finiteGain I n`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_lower`.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.gainValues_nonempty`,
`«2610.05164v2».Optimal.gainValues_eq_jacobi`, `«2610.05164v2».Optimal.finiteEnergy_le` with
the arguments shown in the proof.
-/
theorem finiteGain_lower (I : SpectralInterval) (n : ℕ) :
    2*sqrt (finiteEnergy n) ≤ finiteGain I n := by
  apply le_csInf (gainValues_nonempty I n)
  rw [gainValues_eq_jacobi I n]
  rintro x ⟨J,rfl⟩
  exact (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (finiteEnergy_le n J)) (by norm_num)).trans
    (J.val.normalizedGain_lower I (by omega) J.property)

/--
The stated quantitative bound `2 ≤ finiteGain I n`.

Use: `«2610.05164v2».Optimal.gain_bounded_below` uses this bound to establish the stated
quantitative bound `IsBoundedUnder (· ≥ ·) atTop (finiteGain I)`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_le_sine`.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.finiteEnergy_ge_one`,
`«2610.05164v2».Optimal.finiteGain_lower` with the arguments shown in the proof.
-/
theorem finiteGain_ge_two (I : SpectralInterval) (n : ℕ) : 2 ≤ finiteGain I n := by
  have he : 1 ≤ sqrt (finiteEnergy n) := by
    simpa only [sqrt_one] using sqrt_le_sqrt (finiteEnergy_ge_one n)
  linarith [finiteGain_lower I n]

/--
The precise assertion is `BddBelow (gainValues I n)`.

Use: `«2610.05164v2».Optimal.finiteGain_le_sine` uses this assertion to establish the stated
quantitative bound `finiteGain I n ≤ 2*sqrt (SineJacobi.chain (n+1)).normalizedEnergy`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_le_sine`.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.gainValues_eq_jacobi`,
`«2610.05164v2».Jacobi.normalizedGain_lower` with the arguments shown in the proof.
-/
theorem gainValues_bddBelow (I : SpectralInterval) (n : ℕ) : BddBelow (gainValues I n) := by
  refine ⟨0, ?_⟩
  rw [gainValues_eq_jacobi I n]
  rintro x ⟨J,rfl⟩
  exact (mul_nonneg (by norm_num) (sqrt_nonneg _)).trans
    (J.val.normalizedGain_lower I (by omega) J.property)

/--
The stated quantitative bound `finiteGain I n ≤ 2*sqrt (SineJacobi.chain
(n+1)).normalizedEnergy`.

Use: `«2610.05164v2».Optimal.gainConstant_le_sine` uses this bound to establish the stated
quantitative bound `gainConstant I ≤ 2*sqrt SineJacobi.energy`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_le_sine`.

Proof: Use the identities/estimates `«2610.05164v2».SineJacobi.normalized_gain_exact`,
`«2610.05164v2».Optimal.gainValues_bddBelow` with the arguments shown in the proof.
-/
theorem finiteGain_le_sine (I : SpectralInterval) (n : ℕ) :
    finiteGain I n ≤ 2*sqrt (SineJacobi.chain (n+1)).normalizedEnergy := by
  rw [← SineJacobi.normalized_gain_exact I (n+1) (by omega)]
  exact csInf_le (gainValues_bddBelow I n)
    ⟨(recurrenceEquiv I (n+1) (by omega)) (SineJacobi.fiber (n+1) (by omega)),rfl⟩

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n : ℕ =>
(SineJacobi.chain (n+1)).normalizedEnergy) atTop (𝓝 SineJacobi.energy)`.

Use: `«2610.05164v2».Optimal.energy_bounded_above` uses this limit to establish the stated
quantitative bound `IsBoundedUnder (· ≤ ·) atTop finiteEnergy`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_le_sine`.

Proof: Use the identities/estimates `«2610.05164v2».SineJacobi.energy_limit` with the arguments
shown in the proof.
-/
theorem sineEnergy_limit : Tendsto (fun n : ℕ => (SineJacobi.chain (n+1)).normalizedEnergy)
    atTop (𝓝 SineJacobi.energy) :=
  SineJacobi.energy_limit.comp (tendsto_add_atTop_nat 1)

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n : ℕ =>
2*sqrt (SineJacobi.chain (n+1)).normalizedEnergy) atTop (𝓝 (2*sqrt SineJacobi.energy))`.

Use: `«2610.05164v2».Optimal.gainConstant_le_sine` rewrites with this limit to establish the
stated quantitative bound `gainConstant I ≤ 2*sqrt SineJacobi.energy`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_le_sine`.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.sineEnergy_limit` with the
arguments shown in the proof.
-/
theorem sineGain_limit : Tendsto (fun n : ℕ => 2*sqrt (SineJacobi.chain (n+1)).normalizedEnergy)
    atTop (𝓝 (2*sqrt SineJacobi.energy)) :=
  (continuous_const.mul continuous_sqrt).continuousAt.tendsto.comp sineEnergy_limit

/--
The stated quantitative bound `IsBoundedUnder (· ≥ ·) atTop finiteEnergy`.

Use: `«2610.05164v2».Optimal.gainConstant_lower` uses this bound to establish the stated
quantitative bound `2*sqrt greenConstant ≤ gainConstant I`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_le_sine`.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.finiteEnergy_ge_one` with the
arguments shown in the proof.
-/
theorem energy_bounded_below : IsBoundedUnder (· ≥ ·) atTop finiteEnergy :=
  isBoundedUnder_of_eventually_ge (Eventually.of_forall finiteEnergy_ge_one)
/--
The stated quantitative bound `IsBoundedUnder (· ≤ ·) atTop finiteEnergy`.

Use: `«2610.05164v2».Optimal.gainConstant_lower` uses this bound to establish the stated
quantitative bound `2*sqrt greenConstant ≤ gainConstant I`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_ge_one`.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.sineEnergy_limit`,
`«2610.05164v2».Optimal.finiteEnergy_le` with the arguments shown in the proof.
-/
theorem energy_bounded_above : IsBoundedUnder (· ≤ ·) atTop finiteEnergy :=
  sineEnergy_limit.isBoundedUnder_le.mono_le
    (Eventually.of_forall (fun n => finiteEnergy_le n (SineJacobi.fiber (n+1) (by omega))))
/--
The stated quantitative bound `IsBoundedUnder (· ≥ ·) atTop (finiteGain I)`.

Use: `«2610.05164v2».Optimal.gainConstant_le_sine` uses this bound to establish the stated
quantitative bound `gainConstant I ≤ 2*sqrt SineJacobi.energy`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_le_sine`.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.finiteGain_ge_two` with the
arguments shown in the proof.
-/
theorem gain_bounded_below (I : SpectralInterval) : IsBoundedUnder (· ≥ ·) atTop (finiteGain I) :=
  isBoundedUnder_of_eventually_ge (Eventually.of_forall (finiteGain_ge_two I))
/--
The stated quantitative bound `IsBoundedUnder (· ≤ ·) atTop (finiteGain I)`.

Use: `«2610.05164v2».Optimal.gainConstant_lower` uses this bound to establish the stated
quantitative bound `2*sqrt greenConstant ≤ gainConstant I`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.gainConstant_lower`.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.sineGain_limit`,
`«2610.05164v2».Optimal.finiteGain_le_sine` with the arguments shown in the proof.
-/
theorem gain_bounded_above (I : SpectralInterval) : IsBoundedUnder (· ≤ ·) atTop (finiteGain I) :=
  sineGain_limit.isBoundedUnder_le.mono_le (Eventually.of_forall (finiteGain_le_sine I))

/--
The stated quantitative bound `1 ≤ greenConstant`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 1.2.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.energy_bounded_above`,
`«2610.05164v2».Optimal.finiteEnergy_ge_one` with the arguments shown in the proof.
-/
theorem greenConstant_ge_one : 1 ≤ greenConstant :=
  le_liminf_of_le energy_bounded_above.isCoboundedUnder_ge (Eventually.of_forall finiteEnergy_ge_one)

/--
The stated quantitative bound `greenConstant ≤ SineJacobi.energy`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 1.2.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.finiteEnergy_le`,
`«2610.05164v2».Optimal.energy_bounded_below`, `«2610.05164v2».Optimal.sineEnergy_limit` with
the arguments shown in the proof.
-/
theorem greenConstant_le_sine : greenConstant ≤ SineJacobi.energy := by
  have he := liminf_le_liminf
    (Eventually.of_forall (fun n => finiteEnergy_le n (SineJacobi.fiber (n+1) (by omega))))
    energy_bounded_below sineEnergy_limit.isBoundedUnder_le.isCoboundedUnder_ge
  change liminf finiteEnergy atTop ≤ liminf (fun n => (SineJacobi.chain (n+1)).normalizedEnergy) atTop at he
  rw [sineEnergy_limit.liminf_eq] at he
  exact he

/--
The liminf conclusion of Theorem 2.2.

The stated quantitative bound `2*sqrt greenConstant ≤ gainConstant I`.

Use: `«2610.05164v2».DualCertificate.gainConstant_ge_of_uniform` uses this bound to establish
the stated quantitative bound `2*sqrt L≤«2610.05164v2».Optimal.gainConstant I`.

Article: 2610.05164v2, Theorem 1.2.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.energy_bounded_above`,
`«2610.05164v2».Optimal.energy_bounded_below`, `«2610.05164v2».Optimal.finiteGain_lower` with
the arguments shown in the proof.
-/
theorem gainConstant_lower (I : SpectralInterval) : 2*sqrt greenConstant ≤ gainConstant I := by
  -- Use the identities/estimates `«2610.05164v2».Optimal.energy_bounded_above`,
  -- `«2610.05164v2».Optimal.energy_bounded_below`, `«2610.05164v2».Optimal.finiteGain_lower`
  -- with the arguments shown in the proof.
  have hmono : Monotone (fun x : ℝ => 2*sqrt x) := fun _ _ h =>
    mul_le_mul_of_nonneg_left (sqrt_le_sqrt h) (by norm_num)
  have he := hmono.map_liminf_of_continuousAt finiteEnergy
    (continuous_const.mul continuous_sqrt).continuousAt
    energy_bounded_above.isCoboundedUnder_ge energy_bounded_below
  rw [greenConstant, he]
  apply liminf_le_liminf (Eventually.of_forall (finiteGain_lower I))
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => by positivity)))
    (gain_bounded_above I).isCoboundedUnder_ge

/--
The sine upper bound implied by Theorem 2.5.

The stated quantitative bound `gainConstant I ≤ 2*sqrt SineJacobi.energy`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 1.2.

Proof: Use the identities/estimates `«2610.05164v2».Optimal.finiteGain_le_sine`,
`«2610.05164v2».Optimal.gain_bounded_below`, `«2610.05164v2».Optimal.sineGain_limit` with the
arguments shown in the proof.
-/
theorem gainConstant_le_sine (I : SpectralInterval) : gainConstant I ≤ 2*sqrt SineJacobi.energy := by
  have he := liminf_le_liminf (Eventually.of_forall (finiteGain_le_sine I))
    (gain_bounded_below I) sineGain_limit.isBoundedUnder_le.isCoboundedUnder_ge
  rw [sineGain_limit.liminf_eq] at he
  exact he

/--
Exact identity `gainConstant I = gainConstant K`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 1.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem gainConstant_interval_independent (I K : SpectralInterval) : gainConstant I = gainConstant K := by
  unfold gainConstant
  congr 1
  funext n
  exact finiteGain_interval_independent I K n

end
end «2610.05164v2».Optimal
