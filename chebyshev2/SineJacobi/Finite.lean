import chebyshev2.SineJacobi.Chain
import chebyshev2.SineJacobi.Density
import chebyshev2.Finite.Subclasses
import chebyshev1.SineJacobi.Algorithm
import chebyshev1.SineJacobi.Resolvent
import chebyshev1.SineJacobi.GainAsymptotics
import chebyshev1.SineJacobi.EnergyDecimal

/-!
Article: chebyshev2, Section 4.1.
The actual finite Green energy E_N, with no surrogate diagonal.
Use: `chebyshev2.SineJacobi.energy_decimal` feeds
`chebyshev2.DualCertificate.coarse_sine_upper` (coarse sine upper).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2
noncomputable section
open chebyshev1 Polynomial Polynomial.Chebyshev

namespace SineJacobi

/--
The precise assertion is `(chain N).Centered`.

Use: `chebyshev2.SineJacobi.six_classes_nonempty` uses this assertion to establish
constructs witnesses with the exact properties `∃ J : Fiber N, J.val.Centered ∧
((recurrenceEquiv I N hN) J).val.Centered I`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.SineJacobi.six_classes_nonempty`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.data_aSq`,
`chebyshev1.SineJacobi.couplingSq_pos` with the arguments shown in the proof.
-/
theorem centered (N : ℕ) : (chain N).Centered := by
  refine ⟨?_, fun _ _ => rfl⟩
  intro i hi hn
  change 0 < (chebyshev1.SineJacobi.data N).aSq i
  rw [chebyshev1.SineJacobi.data_aSq N i hi hn]
  exact chebyshev1.SineJacobi.couplingSq_pos N i hi hn

/--
Defines `fiber` of type `Fiber N` by `⟨chain N, terminal N hN⟩`.

Use: `chebyshev2.SineJacobi.six_classes_nonempty` uses this definition to establish
constructs witnesses with the exact properties `∃ J : Fiber N, J.val.Centered ∧
((recurrenceEquiv I N hN) J).val.Centered I`.

Article: chebyshev2, Theorem 1.2 via `chebyshev2.Optimal.greenConstant_le_sine`.
-/
def fiber (N : ℕ) (hN : 0 < N) : Fiber N := ⟨chain N, terminal N hN⟩

/--
Constructs witnesses with the exact properties `∃ J : Fiber N, J.val.Centered ∧
((recurrenceEquiv I N hN) J).val.Centered I`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.1.

Proof: Use the identities/estimates `chebyshev2.SineJacobi.centered`,
`chebyshev2.Jacobi.admissible`, `chebyshev2.SineJacobi.terminal` with the arguments
shown in the proof.
-/
theorem six_classes_nonempty (I : SpectralInterval) (N : ℕ) (hN : 0 < N) :
    ∃ J : Fiber N, J.val.Centered ∧
      ((recurrenceEquiv I N hN) J).val.Centered I := by
  refine ⟨fiber N hN, centered N, ?_⟩
  exact ((chain N).recurrence_centered_iff I ((chain N).admissible I hN (terminal N hN))).mpr
    (centered N)

/--
Defines `diagonalProfile` of type `` by `chebyshev1.SineJacobi.diagonalProfile`.

Use: `chebyshev2.SineJacobi.diagonal_l2_limit` uses this definition to establish the stated
quantitative bound `Filter.Tendsto (fun N : ℕ => MeasureTheory.eLpNorm (fun t =>
diagonalProfile N t-phi t) 2 (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))) Filter.atTop
(nhds 0)`.

Article: chebyshev2, Theorem 2.5 via `chebyshev2.SineJacobi.diagonal_l2_limit`.
-/
abbrev diagonalProfile := chebyshev1.SineJacobi.diagonalProfile

/--
The actual finite Green energy E_N, with no surrogate diagonal.

Exact identity `(chain N).energy = ∑ s ∈ Finset.range N, chebyshev1.SineJacobi.greenWeight
N s^2`.

Use: `chebyshev2.SineJacobi.energy_limit` rewrites with this identity to establish the
stated quantitative bound `Filter.Tendsto (fun N : ℕ => (chain N).energy/(N:ℝ)^3) Filter.atTop
(nhds energy)`.

Article: chebyshev2, Theorem 2.5 via `chebyshev2.SineJacobi.gain_exact`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.resolvent_diagonal` with the
arguments shown in the proof.
-/
theorem energy_eq (N : ℕ) : (chain N).energy =
    ∑ s ∈ Finset.range N, chebyshev1.SineJacobi.greenWeight N s^2 := by
  simp only [Jacobi.energy, Jacobi.green, Jacobi.matrix, chain,
    chebyshev1.SineJacobi.resolvent_diagonal]
  exact Fin.sum_univ_eq_sum_range (fun s : ℕ => chebyshev1.SineJacobi.greenWeight N s^2) N

/--
Exact identity `((recurrenceEquiv I N hN) (fiber N hN)).val.method.realization.gain I N =
2*I.epsilon N/I.delta * Real.sqrt (chain N).energy`.

Use: `chebyshev2.SineJacobi.normalized_gain_exact` rewrites with this identity to establish
exact identity `((recurrenceEquiv I N hN) (fiber N hN)).val.normalizedGain I = 2*sqrt (chain
N).normalizedEnergy`.

Article: chebyshev2, Theorem 2.5.

Proof: Use the identities/estimates `chebyshev2.Jacobi.admissible`,
`chebyshev2.SineJacobi.terminal`, `chebyshev2.Horizon.gain_eq` with the arguments shown
in the proof.
-/
theorem gain_exact (I : SpectralInterval) (N : ℕ) (hN : 0 < N) :
    ((recurrenceEquiv I N hN) (fiber N hN)).val.method.realization.gain I N =
      2*I.epsilon N/I.delta * Real.sqrt (chain N).energy := by
  -- Use the identities/estimates `chebyshev2.Jacobi.admissible`,
  -- `chebyshev2.SineJacobi.terminal`, `chebyshev2.Horizon.gain_eq` with the arguments
  -- shown in the proof.
  change ((chain N).recurrence I ((chain N).admissible I hN (terminal N hN))).method.realization.gain
    I N = _
  rw [Horizon.gain_eq ((chain N).recurrence_agree I
    ((chain N).admissible I hN (terminal N hN))) I]
  change ((chebyshev1.SineJacobi.data N).realization I).gain I N = _
  rw [energy_eq]
  exact chebyshev1.SineJacobi.gain_exact I N hN

/--
The stated quantitative bound `Filter.Tendsto (fun N : ℕ => MeasureTheory.eLpNorm (fun t =>
diagonalProfile N t-phi t) 2 (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))) Filter.atTop
(nhds 0)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.5.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`
with the arguments shown in the proof.
-/
theorem diagonal_l2_limit :
    Filter.Tendsto (fun N : ℕ => MeasureTheory.eLpNorm
      (fun t => diagonalProfile N t-phi t) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1)))
      Filter.atTop (nhds 0) :=
  chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit (by norm_num) (by norm_num)

/--
The stated quantitative bound `Filter.Tendsto (fun N : ℕ => (chain N).energy/(N:ℝ)^3)
Filter.atTop (nhds energy)`.

Use: `chebyshev2.Optimal.sineEnergy_limit` uses this identity to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun n : ℕ =>
(SineJacobi.chain (n+1)).normalizedEnergy) atTop (𝓝 SineJacobi.energy)`.

Article: chebyshev2, Theorem 2.5.

Proof: Use the identities/estimates `chebyshev2.SineJacobi.energy_eq`,
`chebyshev1.SineJacobi.greenWeight_energy_limit` with the arguments shown in the proof.
-/
theorem energy_limit : Filter.Tendsto
    (fun N : ℕ => (chain N).energy/(N:ℝ)^3) Filter.atTop (nhds energy) := by
  simp only [energy_eq]
  exact chebyshev1.SineJacobi.greenWeight_energy_limit

/--
The stated quantitative bound `1.14269215 < energy ∧ energy < 1.14269221`.

Use: `chebyshev2.DualCertificate.coarse_sine_upper` uses this bound to establish the stated
quantitative bound `chebyshev2.SineJacobi.energy < (coarseSineUpper : ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineEnergy_decimal` with the
arguments shown in the proof.
-/
theorem energy_decimal : 1.14269215 < energy ∧ energy < 1.14269221 :=
  chebyshev1.SineJacobi.sineEnergy_decimal

end SineJacobi
end
end chebyshev2
