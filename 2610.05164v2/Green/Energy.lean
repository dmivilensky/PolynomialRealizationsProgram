import «2610.05164v2».Finite.Gain

/-!
Article: 2610.05164v2, Theorem 1.1.
The gap in (6) is precisely the squared deviation of the Green diagonal.
Use: `«2610.05164v2».Jacobi.energy_ge_cube` feeds `«2610.05164v2».Jacobi.normalizedEnergy_ge_one`
(normalized Energy ge one).
Proof chain: `«2610.05164v2».DualCertificate.uniform_sine_of_finite_lower` — 2610.05164v2, Theorem
1.2; Analytic gain reduction and uniform sine comparison.
-/
namespace «2610.05164v2».Jacobi
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
variable {N : ℕ} (J : Jacobi N)

/--
The gap in (6) is precisely the squared deviation of the Green diagonal.

Exact identity `(∑ i : Fin N, (J.green i i-(N:ℝ))^2) = J.energy-(N:ℝ)^3`.

Use: `«2610.05164v2».Jacobi.energy_eq_cube_iff` rewrites with this identity to establish
equivalence of the displayed criteria: `J.energy = (N:ℝ)^3 ↔ ∀ i : Fin N, J.green i i = (N:ℝ)`.

Article: 2610.05164v2, Theorem 1.2 via
`«2610.05164v2».DualCertificate.uniform_sine_of_finite_lower`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.green_trace` with the arguments
shown in the proof.
-/
theorem energy_gap (hN : 0 < N) (ht : J.Terminal) :
    (∑ i : Fin N, (J.green i i-(N:ℝ))^2) = J.energy-(N:ℝ)^3 := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.green_trace` with the arguments shown
  -- in the proof.
  have he : (∑ i : Fin N, (J.green i i-(N:ℝ))^2) =
      J.energy - 2*(N:ℝ)*Matrix.trace J.green + (N:ℝ)^3 := by
    simp only [sub_sq, energy, Matrix.trace, Matrix.diag,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum (Finset.univ : Finset (Fin N)) (fun i => J.green i i) 2]
    ring
  rw [he, J.green_trace hN ht]; ring

/--
The stated quantitative bound `(N:ℝ)^3 ≤ J.energy`.

Use: `«2610.05164v2».Jacobi.normalizedEnergy_ge_one` uses this bound to establish the stated
quantitative bound `1 ≤ J.normalizedEnergy`.

Article: 2610.05164v2, Theorem 1.2 via
`«2610.05164v2».DualCertificate.uniform_sine_of_finite_lower`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.energy_gap` with the arguments shown
in the proof.
-/
theorem energy_ge_cube (hN : 0 < N) (ht : J.Terminal) : (N:ℝ)^3 ≤ J.energy := by
  have hp := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    sq_nonneg (J.green i i-(N:ℝ)))
  rw [J.energy_gap hN ht] at hp
  linarith

/--
Equivalence of the displayed criteria: `J.energy = (N:ℝ)^3 ↔ ∀ i : Fin N, J.green i i = (N:ℝ)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 1.1.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.energy_gap` with the arguments shown
in the proof.
-/
theorem energy_eq_cube_iff (hN : 0 < N) (ht : J.Terminal) :
    J.energy = (N:ℝ)^3 ↔ ∀ i : Fin N, J.green i i = (N:ℝ) := by
  rw [← sub_eq_zero, ← J.energy_gap hN ht,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (J.green i i-(N:ℝ)))]
  simp [sub_eq_zero]

end
end «2610.05164v2».Jacobi
