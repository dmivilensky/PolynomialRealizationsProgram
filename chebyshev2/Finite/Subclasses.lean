import chebyshev2.Finite.Equivalence

/-!
Article: chebyshev2, Theorem 2.1.
Subclasses.
Use: `chebyshev2.Jacobi.recurrence_centered_iff` feeds
`chebyshev2.SineJacobi.six_classes_nonempty` (six classes nonempty).
-/
namespace chebyshev2
noncomputable section
open chebyshev1

namespace Jacobi
variable {N : ℕ} (J : Jacobi N) (I : SpectralInterval)

/--
Exact identity `(J.recurrence I h).beta i = J.data.aSq i * J.data.den I (i-1) / J.data.den I
(i+1)`.

Use: `chebyshev2.Jacobi.recurrence_irreducible_iff` rewrites with this identity to
establish equivalence of the displayed criteria: `(J.recurrence I h).Irreducible ↔
J.Irreducible`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence_irreducible_iff`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem recurrence_beta (h : J.data.Admissible I N) (i : ℕ) (hi : i < N) :
    (J.recurrence I h).beta i = J.data.aSq i * J.data.den I (i-1) / J.data.den I (i+1) := by simp [Recurrence.beta, recurrence, Horizon.truncate, hi, JacobiData.method]

/--
Exact identity `(J.recurrence I h).gamma i = (2/I.delta)*J.data.den I i/J.data.den I (i+1)`.

Use: `chebyshev2.Jacobi.recurrence_centered_iff` rewrites with this identity to establish
equivalence of the displayed criteria: `(J.recurrence I h).Centered I ↔ J.Centered`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence_centered_iff`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem recurrence_gamma (h : J.data.Admissible I N) (i : ℕ) (hi : i < N) :
    (J.recurrence I h).gamma i = (2/I.delta)*J.data.den I i/J.data.den I (i+1) := by simp [Recurrence.gamma, recurrence, Horizon.truncate, hi, JacobiData.method]

/--
Exact identity `(J.recurrence I h).alpha i = (I.eta-J.data.b i)*J.data.den I i/J.data.den I
(i+1)`.

Use: `chebyshev2.Jacobi.recurrence_centered_iff` rewrites with this identity to establish
equivalence of the displayed criteria: `(J.recurrence I h).Centered I ↔ J.Centered`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence_centered_iff`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem recurrence_alpha (h : J.data.Admissible I N) (i : ℕ) (hi : i < N) :
    (J.recurrence I h).alpha i =
      (I.eta-J.data.b i)*J.data.den I i/J.data.den I (i+1) := by
  simp only [Recurrence.alpha, recurrence, Horizon.truncate, hi, ite_true, JacobiData.method]
  ring

/--
Equivalence of the displayed criteria: `(J.recurrence I h).Irreducible ↔ J.Irreducible`.

Use: `chebyshev2.Jacobi.recurrence_centered_iff` rewrites with this assertion to establish
equivalence of the displayed criteria: `(J.recurrence I h).Centered I ↔ J.Centered`.

Article: chebyshev2, Theorem 2.1.

Proof: Use the identities/estimates `chebyshev2.Jacobi.recurrence_beta` with the arguments
shown in the proof.
-/
theorem recurrence_irreducible_iff (h : J.data.Admissible I N) :
    (J.recurrence I h).Irreducible ↔ J.Irreducible := by
  unfold Recurrence.Irreducible Irreducible
  have he (i : ℕ) (hi : i < N) : 0 < (J.recurrence I h).beta i ↔ 0 < J.data.aSq i := by
    rw [J.recurrence_beta I h i hi, div_pos_iff_of_pos_right (h (i+1) (by omega)),
      mul_pos_iff_of_pos_right (h (i-1) (by omega))]
  exact ⟨fun hr i hi hn => (he i hn).mp (hr i hi hn),
    fun hj i hi hn => (he i hn).mpr (hj i hi hn)⟩

/--
Equivalence of the displayed criteria: `(J.recurrence I h).Centered I ↔ J.Centered`.

Use: `chebyshev2.SineJacobi.six_classes_nonempty` uses this assertion to establish
constructs witnesses with the exact properties `∃ J : Fiber N, J.val.Centered ∧
((recurrenceEquiv I N hN) J).val.Centered I`.

Article: chebyshev2, Theorem 2.1.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem recurrence_centered_iff (h : J.data.Admissible I N) :
    (J.recurrence I h).Centered I ↔ J.Centered := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have he (i : ℕ) (hi : i < N) :
      (J.recurrence I h).alpha i = (I.L+I.mu)/2*(J.recurrence I h).gamma i ↔
      J.data.b i = 0 := by
    rw [J.recurrence_alpha I h i hi, J.recurrence_gamma I h i hi]
    have hd := (h i (by omega)).ne'
    have hd' := (h (i+1) (by omega)).ne'
    unfold SpectralInterval.eta
    field_simp [hd', I.delta_pos.ne']
    constructor <;> intro hh
    · have hz : I.delta * J.data.b i = 0 := by linarith [hh]
      exact (mul_eq_zero.mp hz).resolve_left I.delta_pos.ne'
    · rw [hh]; ring
  simp only [Recurrence.Centered, Centered, J.recurrence_irreducible_iff I h]
  exact and_congr Iff.rfl ⟨fun hr i hi => (he i hi).mp (hr i hi),
    fun hj i hi => (he i hi).mpr (hj i hi)⟩

end Jacobi
end
end chebyshev2
