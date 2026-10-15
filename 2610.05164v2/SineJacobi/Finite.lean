import «2610.05164v2».Finite.Subclasses
import «2606.16671v2».SineJacobi.Algorithm
import «2606.16671v2».SineJacobi.Resolvent
import «2606.16671v2».SineJacobi.GainAsymptotics
import «2606.16671v2».SineJacobi.EnergyDecimal

/-!
Article: 2610.05164v2, Section 4.1.
The actual finite Green energy E_N, with no surrogate diagonal.
Use: `«2610.05164v2».SineJacobi.energy_decimal` feeds
`«2610.05164v2».DualCertificate.coarse_sine_upper` (coarse sine upper).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2»
noncomputable section
open «2606.16671v2» Polynomial Polynomial.Chebyshev

namespace SineJacobi

/--
Constructs `chain` of type `Jacobi N` by the displayed record fields. Data fields specify the
construction; proof fields discharge its required properties.

Use: `«2610.05164v2».SineJacobi.energy_eq` rewrites with this definition to establish exact
identity `(chain N).energy = ∑ s ∈ Finset.range N, «2606.16671v2».SineJacobi.greenWeight N
s^2`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_le_sine`.
-/
def chain (N : ℕ) : Jacobi N where
  data := «2606.16671v2».SineJacobi.data N
  coupling_nonneg := «2606.16671v2».SineJacobi.data_aSq_nonneg N
  coupling_zero := «2606.16671v2».SineJacobi.data_aSq_zero N
  diagonal_tail _ _ := rfl
  coupling_tail i hi := by   simp [«2606.16671v2».SineJacobi.data, show ¬(0 < i ∧ i < N) by omega]

/--
The precise assertion is `(chain N).Terminal`.

Use: `«2610.05164v2».SineJacobi.fiber` uses this assertion in the displayed construction of
`fiber`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.5 via `«2610.05164v2».SineJacobi.gain_exact`.

Proof: Use the identities/estimates `«2610.05164v2».fiberPolynomial_eq`,
`«2606.16671v2».SineJacobi.terminal` with the arguments shown in the proof.
-/
theorem terminal (N : ℕ) (hN : 0 < N) : (chain N).Terminal := by
  change («2606.16671v2».SineJacobi.data N).leading N = fiberPolynomial N
  rw [fiberPolynomial_eq N hN]
  exact «2606.16671v2».SineJacobi.terminal N hN

/--
The precise assertion is `(chain N).Centered`.

Use: `«2610.05164v2».SineJacobi.six_classes_nonempty` uses this assertion to establish
constructs witnesses with the exact properties `∃ J : Fiber N, J.val.Centered ∧
((recurrenceEquiv I N hN) J).val.Centered I`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».SineJacobi.six_classes_nonempty`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.data_aSq`,
`«2606.16671v2».SineJacobi.couplingSq_pos` with the arguments shown in the proof.
-/
theorem centered (N : ℕ) : (chain N).Centered := by
  refine ⟨?_, fun _ _ => rfl⟩
  intro i hi hn
  change 0 < («2606.16671v2».SineJacobi.data N).aSq i
  rw [«2606.16671v2».SineJacobi.data_aSq N i hi hn]
  exact «2606.16671v2».SineJacobi.couplingSq_pos N i hi hn

/--
Defines `fiber` of type `Fiber N` by `⟨chain N, terminal N hN⟩`.

Use: `«2610.05164v2».SineJacobi.six_classes_nonempty` uses this definition to establish
constructs witnesses with the exact properties `∃ J : Fiber N, J.val.Centered ∧
((recurrenceEquiv I N hN) J).val.Centered I`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_le_sine`.
-/
def fiber (N : ℕ) (hN : 0 < N) : Fiber N := ⟨chain N, terminal N hN⟩

/--
Constructs witnesses with the exact properties `∃ J : Fiber N, J.val.Centered ∧
((recurrenceEquiv I N hN) J).val.Centered I`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 2.1.

Proof: Use the identities/estimates `«2610.05164v2».SineJacobi.centered`,
`«2610.05164v2».Jacobi.admissible`, `«2610.05164v2».SineJacobi.terminal` with the arguments
shown in the proof.
-/
theorem six_classes_nonempty (I : SpectralInterval) (N : ℕ) (hN : 0 < N) :
    ∃ J : Fiber N, J.val.Centered ∧
      ((recurrenceEquiv I N hN) J).val.Centered I := by
  refine ⟨fiber N hN, centered N, ?_⟩
  exact ((chain N).recurrence_centered_iff I ((chain N).admissible I hN (terminal N hN))).mpr
    (centered N)

/--
Defines `phi` of type `ℝ → ℝ` by `«2606.16671v2».SineJacobi.sineDensity`.

Use: `«2610.05164v2».SineContinuum.T_smooth` uses this definition to establish smoothness to
the stated order: `ContDiff ℝ ∞ T`.

Article: 2610.05164v2, Theorem 2.5 via `«2610.05164v2».SineJacobi.diagonal_l2_limit`.
-/
abbrev phi : ℝ → ℝ := «2606.16671v2».SineJacobi.sineDensity
/--
Defines `energy` of type `ℝ` by `«2606.16671v2».SineJacobi.sineEnergy`.

Use: `«2610.05164v2».SineJacobi.energy_decimal` uses this definition to establish the stated
quantitative bound `1.14269215 < energy ∧ energy < 1.14269221`.

Article: 2610.05164v2, Theorem 1.2 via `«2610.05164v2».Optimal.greenConstant_le_sine`.
-/
abbrev energy : ℝ := «2606.16671v2».SineJacobi.sineEnergy
/--
Defines `diagonalProfile` of type `` by `«2606.16671v2».SineJacobi.diagonalProfile`.

Use: `«2610.05164v2».SineJacobi.diagonal_l2_limit` uses this definition to establish the stated
quantitative bound `Filter.Tendsto (fun N : ℕ => MeasureTheory.eLpNorm (fun t =>
diagonalProfile N t-phi t) 2 (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))) Filter.atTop
(nhds 0)`.

Article: 2610.05164v2, Theorem 2.5 via `«2610.05164v2».SineJacobi.diagonal_l2_limit`.
-/
abbrev diagonalProfile := «2606.16671v2».SineJacobi.diagonalProfile

/--
The actual finite Green energy E_N, with no surrogate diagonal.

Exact identity `(chain N).energy = ∑ s ∈ Finset.range N, «2606.16671v2».SineJacobi.greenWeight
N s^2`.

Use: `«2610.05164v2».SineJacobi.energy_limit` rewrites with this identity to establish the
stated quantitative bound `Filter.Tendsto (fun N : ℕ => (chain N).energy/(N:ℝ)^3) Filter.atTop
(nhds energy)`.

Article: 2610.05164v2, Theorem 2.5 via `«2610.05164v2».SineJacobi.gain_exact`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.resolvent_diagonal` with the
arguments shown in the proof.
-/
theorem energy_eq (N : ℕ) : (chain N).energy =
    ∑ s ∈ Finset.range N, «2606.16671v2».SineJacobi.greenWeight N s^2 := by
  simp only [Jacobi.energy, Jacobi.green, Jacobi.matrix, chain,
    «2606.16671v2».SineJacobi.resolvent_diagonal]
  exact Fin.sum_univ_eq_sum_range (fun s : ℕ => «2606.16671v2».SineJacobi.greenWeight N s^2) N

/--
Exact identity `((recurrenceEquiv I N hN) (fiber N hN)).val.method.realization.gain I N =
2*I.epsilon N/I.delta * Real.sqrt (chain N).energy`.

Use: `«2610.05164v2».SineJacobi.normalized_gain_exact` rewrites with this identity to establish
exact identity `((recurrenceEquiv I N hN) (fiber N hN)).val.normalizedGain I = 2*sqrt (chain
N).normalizedEnergy`.

Article: 2610.05164v2, Theorem 2.5.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.admissible`,
`«2610.05164v2».SineJacobi.terminal`, `«2610.05164v2».Horizon.gain_eq` with the arguments shown
in the proof.
-/
theorem gain_exact (I : SpectralInterval) (N : ℕ) (hN : 0 < N) :
    ((recurrenceEquiv I N hN) (fiber N hN)).val.method.realization.gain I N =
      2*I.epsilon N/I.delta * Real.sqrt (chain N).energy := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.admissible`,
  -- `«2610.05164v2».SineJacobi.terminal`, `«2610.05164v2».Horizon.gain_eq` with the arguments
  -- shown in the proof.
  change ((chain N).recurrence I ((chain N).admissible I hN (terminal N hN))).method.realization.gain
    I N = _
  rw [Horizon.gain_eq ((chain N).recurrence_agree I
    ((chain N).admissible I hN (terminal N hN))) I]
  change ((«2606.16671v2».SineJacobi.data N).realization I).gain I N = _
  rw [energy_eq]
  exact «2606.16671v2».SineJacobi.gain_exact I N hN

/--
The stated quantitative bound `Filter.Tendsto (fun N : ℕ => MeasureTheory.eLpNorm (fun t =>
diagonalProfile N t-phi t) 2 (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))) Filter.atTop
(nhds 0)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 2.5.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.diagonalProfile_eLpNorm_limit`
with the arguments shown in the proof.
-/
theorem diagonal_l2_limit :
    Filter.Tendsto (fun N : ℕ => MeasureTheory.eLpNorm
      (fun t => diagonalProfile N t-phi t) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1)))
      Filter.atTop (nhds 0) :=
  «2606.16671v2».SineJacobi.diagonalProfile_eLpNorm_limit (by norm_num) (by norm_num)

/--
The stated quantitative bound `Filter.Tendsto (fun N : ℕ => (chain N).energy/(N:ℝ)^3)
Filter.atTop (nhds energy)`.

Use: `«2610.05164v2».Optimal.sineEnergy_limit` uses this identity to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun n : ℕ =>
(SineJacobi.chain (n+1)).normalizedEnergy) atTop (𝓝 SineJacobi.energy)`.

Article: 2610.05164v2, Theorem 2.5.

Proof: Use the identities/estimates `«2610.05164v2».SineJacobi.energy_eq`,
`«2606.16671v2».SineJacobi.greenWeight_energy_limit` with the arguments shown in the proof.
-/
theorem energy_limit : Filter.Tendsto
    (fun N : ℕ => (chain N).energy/(N:ℝ)^3) Filter.atTop (nhds energy) := by
  simp only [energy_eq]
  exact «2606.16671v2».SineJacobi.greenWeight_energy_limit

/--
The stated quantitative bound `1.14269215 < energy ∧ energy < 1.14269221`.

Use: `«2610.05164v2».DualCertificate.coarse_sine_upper` uses this bound to establish the stated
quantitative bound `«2610.05164v2».SineJacobi.energy < (coarseSineUpper : ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sineEnergy_decimal` with the
arguments shown in the proof.
-/
theorem energy_decimal : 1.14269215 < energy ∧ energy < 1.14269221 :=
  «2606.16671v2».SineJacobi.sineEnergy_decimal

end SineJacobi
end
end «2610.05164v2»
