import chebyshev2.Finite.Optimal

/-!
Article: chebyshev2, Theorem 1.1.
The normalized finite sine gain tends to the stated leading coefficient.
Result: `chebyshev2.SineJacobi.normalized_gain_limit` supplies the stated article conclusion.
-/
namespace chebyshev2.Optimal
noncomputable section
open chebyshev1 Real Filter Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `symmetricValues` of type `(I : SpectralInterval) (n : ℕ)` by `Set.range (fun R :
ExactRecurrence I (n+1) => R.val.normalizedSymmetricGain I)`.

Use: `chebyshev2.Optimal.finiteSymmetricGain` uses this definition in the displayed
construction of `finiteSymmetricGain`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.
-/
def symmetricValues (I : SpectralInterval) (n : ℕ) := Set.range
  (fun R : ExactRecurrence I (n+1) => R.val.normalizedSymmetricGain I)
/--
Defines `finiteSymmetricGain` of type `ℝ` by `sInf (symmetricValues I n)`.

Use: `chebyshev2.Optimal.symmetricGainConstant` uses this definition in the displayed
construction of `symmetricGainConstant`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.
-/
def finiteSymmetricGain (I : SpectralInterval) (n : ℕ) : ℝ := sInf (symmetricValues I n)
/--
Defines `symmetricGainConstant` of type `ℝ` by `liminf (finiteSymmetricGain I) atTop`.

Use: `chebyshev2.Optimal.symmetricGainConstant_bounds` uses this definition to establish
the stated quantitative bound `2*sqrt greenConstant ≤ symmetricGainConstant I ∧
symmetricGainConstant I ≤ gainConstant I`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.
-/
def symmetricGainConstant (I : SpectralInterval) : ℝ := liminf (finiteSymmetricGain I) atTop

/--
The precise assertion is `(symmetricValues I n).Nonempty`.

Use: `chebyshev2.Optimal.finiteSymmetricGain_lower` uses this assertion to establish the
stated quantitative bound `2*sqrt (finiteEnergy n) ≤ finiteSymmetricGain I n`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem symmetricValues_nonempty (I : SpectralInterval) (n : ℕ) : (symmetricValues I n).Nonempty :=
  ⟨_,⟨(recurrenceEquiv I (n+1) (by omega)) (SineJacobi.fiber (n+1) (by omega)),rfl⟩⟩

/--
The precise assertion is `BddBelow (symmetricValues I n)`.

Use: `chebyshev2.Optimal.finiteSymmetricGain_le` uses this assertion to establish the
stated quantitative bound `finiteSymmetricGain I n ≤ finiteGain I n`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.normalizedSymmetricGain_lower` with
the arguments shown in the proof.
-/
theorem symmetricValues_bddBelow (I : SpectralInterval) (n : ℕ) : BddBelow (symmetricValues I n) := by
  refine ⟨0, ?_⟩
  rintro x ⟨R,rfl⟩
  obtain ⟨J,rfl⟩ := (recurrenceEquiv I (n+1) (by omega)).surjective R
  exact (mul_nonneg (by norm_num) (sqrt_nonneg _)).trans
    (J.val.normalizedSymmetricGain_lower I (by omega) J.property)

/--
The stated quantitative bound `2*sqrt (finiteEnergy n) ≤ finiteSymmetricGain I n`.

Use: `chebyshev2.Optimal.symmetricGainConstant_bounds` uses this bound to establish the
stated quantitative bound `2*sqrt greenConstant ≤ symmetricGainConstant I ∧
symmetricGainConstant I ≤ gainConstant I`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.

Proof: Use the identities/estimates `chebyshev2.Optimal.symmetricValues_nonempty`,
`chebyshev2.Optimal.finiteEnergy_le`, `chebyshev2.Jacobi.normalizedSymmetricGain_lower`
with the arguments shown in the proof.
-/
theorem finiteSymmetricGain_lower (I : SpectralInterval) (n : ℕ) :
    2*sqrt (finiteEnergy n) ≤ finiteSymmetricGain I n := by
  apply le_csInf (symmetricValues_nonempty I n)
  rintro x ⟨R,rfl⟩
  obtain ⟨J,rfl⟩ := (recurrenceEquiv I (n+1) (by omega)).surjective R
  exact (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (finiteEnergy_le n J)) (by norm_num)).trans
    (J.val.normalizedSymmetricGain_lower I (by omega) J.property)

/--
The stated quantitative bound `finiteSymmetricGain I n ≤ finiteGain I n`.

Use: `chebyshev2.Optimal.symmetricGainConstant_bounds` uses this bound to establish the
stated quantitative bound `2*sqrt greenConstant ≤ symmetricGainConstant I ∧
symmetricGainConstant I ≤ gainConstant I`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.

Proof: Use the identities/estimates `chebyshev2.Optimal.gainValues_nonempty`,
`chebyshev2.Optimal.symmetricValues_bddBelow`,
`chebyshev2.Jacobi.normalizedSymmetricGain_le` with the arguments shown in the proof.
-/
theorem finiteSymmetricGain_le (I : SpectralInterval) (n : ℕ) :
    finiteSymmetricGain I n ≤ finiteGain I n := by
  apply le_csInf (gainValues_nonempty I n)
  rintro x ⟨R,rfl⟩
  apply (csInf_le (symmetricValues_bddBelow I n) ⟨R,rfl⟩).trans
  obtain ⟨J,rfl⟩ := (recurrenceEquiv I (n+1) (by omega)).surjective R
  exact J.val.normalizedSymmetricGain_le I (by omega) J.property

/--
The stated quantitative bound `IsBoundedUnder (· ≥ ·) atTop (finiteSymmetricGain I)`.

Use: `chebyshev2.Optimal.symmetricGainConstant_bounds` uses this bound to establish the
stated quantitative bound `2*sqrt greenConstant ≤ symmetricGainConstant I ∧
symmetricGainConstant I ≤ gainConstant I`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.

Proof: Use the identities/estimates `chebyshev2.Optimal.finiteSymmetricGain_lower` with the
arguments shown in the proof.
-/
theorem symmetricGain_bounded_below (I : SpectralInterval) :
    IsBoundedUnder (· ≥ ·) atTop (finiteSymmetricGain I) := by
  apply isBoundedUnder_of_eventually_ge (a := 0)
  exact Eventually.of_forall (fun n =>
    (mul_nonneg (by norm_num) (sqrt_nonneg _)).trans (finiteSymmetricGain_lower I n))

/--
The stated quantitative bound `IsBoundedUnder (· ≤ ·) atTop (finiteSymmetricGain I)`.

Use: `chebyshev2.Optimal.symmetricGainConstant_bounds` uses this bound to establish the
stated quantitative bound `2*sqrt greenConstant ≤ symmetricGainConstant I ∧
symmetricGainConstant I ≤ gainConstant I`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.

Proof: Use the identities/estimates `chebyshev2.Optimal.gain_bounded_above`,
`chebyshev2.Optimal.finiteSymmetricGain_le` with the arguments shown in the proof.
-/
theorem symmetricGain_bounded_above (I : SpectralInterval) :
    IsBoundedUnder (· ≤ ·) atTop (finiteSymmetricGain I) :=
  (gain_bounded_above I).mono_le (Eventually.of_forall (finiteSymmetricGain_le I))

/--
The asymptotic sandwich underlying Corollary 1.

The stated quantitative bound `2*sqrt greenConstant ≤ symmetricGainConstant I ∧
symmetricGainConstant I ≤ gainConstant I`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Corollary 1.

Proof: Use the identities/estimates `chebyshev2.Optimal.energy_bounded_above`,
`chebyshev2.Optimal.energy_bounded_below`,
`chebyshev2.Optimal.finiteSymmetricGain_lower` with the arguments shown in the proof.
-/
theorem symmetricGainConstant_bounds (I : SpectralInterval) :
    2*sqrt greenConstant ≤ symmetricGainConstant I ∧ symmetricGainConstant I ≤ gainConstant I := by
  -- Use the identities/estimates `chebyshev2.Optimal.energy_bounded_above`,
  -- `chebyshev2.Optimal.energy_bounded_below`,
  -- `chebyshev2.Optimal.finiteSymmetricGain_lower` with the arguments shown in the proof.
  constructor
  · have hmono : Monotone (fun x : ℝ => 2*sqrt x) := fun _ _ h =>
      mul_le_mul_of_nonneg_left (sqrt_le_sqrt h) (by norm_num)
    have he := hmono.map_liminf_of_continuousAt finiteEnergy
      (continuous_const.mul continuous_sqrt).continuousAt
      energy_bounded_above.isCoboundedUnder_ge energy_bounded_below
    rw [greenConstant,he]
    apply liminf_le_liminf (Eventually.of_forall (finiteSymmetricGain_lower I))
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => by positivity)))
      (symmetricGain_bounded_above I).isCoboundedUnder_ge
  · exact liminf_le_liminf (Eventually.of_forall (finiteSymmetricGain_le I))
      (symmetricGain_bounded_below I) (gain_bounded_above I).isCoboundedUnder_ge

end
end chebyshev2.Optimal

namespace chebyshev2.SineJacobi
noncomputable section
open chebyshev1 Real Filter Topology

/--
The normalized finite sine gain tends to the stated leading coefficient.

Convergence along the specified source filter to the specified limit: `Tendsto (fun n : ℕ =>
((recurrenceEquiv I (n+1) (by omega)) (fiber (n+1) (by omega))).val.normalizedGain I) atTop (𝓝
(2*sqrt energy))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.5.

Proof: Use the identities/estimates `chebyshev2.Optimal.sineGain_limit`,
`chebyshev2.SineJacobi.normalized_gain_exact` with the arguments shown in the proof.
-/
theorem normalized_gain_limit (I : SpectralInterval) :
    Tendsto (fun n : ℕ => ((recurrenceEquiv I (n+1) (by omega)) (fiber (n+1) (by omega))).val.normalizedGain I)
      atTop (𝓝 (2*sqrt energy)) := by
  have he := Optimal.sineGain_limit
  apply he.congr
  intro n
  exact (normalized_gain_exact I (n+1) (by omega)).symm

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n : ℕ =>
((recurrenceEquiv I (n+1) (by omega)) (fiber (n+1) (by omega))).val.normalizedSymmetricGain I)
atTop (𝓝 (2*sqrt energy))`.

Use: a standalone supporting limit for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 1.1.

Proof: Use the identities/estimates `chebyshev2.Optimal.sineGain_limit`,
`chebyshev2.SineJacobi.normalized_symmetric_gain_exact` with the arguments shown in the
proof.
-/
theorem normalized_symmetric_gain_limit (I : SpectralInterval) :
    Tendsto (fun n : ℕ => ((recurrenceEquiv I (n+1) (by omega)) (fiber (n+1) (by omega))).val.normalizedSymmetricGain I)
      atTop (𝓝 (2*sqrt energy)) := by
  apply Optimal.sineGain_limit.congr
  intro n
  exact (normalized_symmetric_gain_exact I (n+1) (by omega)).symm

end
end chebyshev2.SineJacobi
