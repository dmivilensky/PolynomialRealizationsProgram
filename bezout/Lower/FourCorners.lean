import bezout.Lower.MassSeparation

/-!
Article: bezout, Lemma C.2 (`lem:four-corners`), including
`eq:symmetric-four-corners`.
Use: any real separated factorization with the four endpoint sums of the
odd Chebyshev Bezoutian obeys the exact sharp weighted energy inequality.
Only its four endpoint identities are required; degrees, normalization,
positivity and preservation of parity are unnecessary.
-/

namespace bezout.Lower

noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The weighted energy that respects symmetric off-diagonal perturbations. -/
def symmetricCornerEnergy (fp fm qp qm : ι → ℝ) : ℝ :=
  3 / 8 * (∑ i, ((fp i * qp i) ^ 2 + (fm i * qm i) ^ 2)) +
    1 / 16 * ∑ i, (fp i * qm i + fm i * qp i) ^ 2

/-- The corresponding energy with the two cross corners kept separately. -/
def fourCornerEnergy (fp fm qp qm : ι → ℝ) : ℝ :=
  3 / 8 * (∑ i, ((fp i * qp i) ^ 2 + (fm i * qm i) ^ 2)) +
    1 / 8 * ∑ i, ((fp i * qm i) ^ 2 + (fm i * qp i) ^ 2)

/-- Summed symmetrization is contractive for the two cross profiles. -/
theorem symmetricCornerEnergy_le_fourCornerEnergy (fp fm qp qm : ι → ℝ) :
    symmetricCornerEnergy fp fm qp qm ≤ fourCornerEnergy fp fm qp qm := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    symmetric_corner_le_four_corner (fp i) (fm i) (qp i) (qm i)
  simpa only [symmetricCornerEnergy, fourCornerEnergy,
    Finset.sum_add_distrib, ← Finset.mul_sum] using h

/-- The stronger symmetric four-corner estimate, with precisely the four
sums supplied by an odd Chebyshev Bezoutian factorization. -/
theorem symmetric_four_corner_lower (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (hcard : Fintype.card ι = N) (fp fm qp qm : ι → ℝ)
    (hpp : ∑ i, fp i * qp i = (N : ℝ) ^ 2 / 2)
    (hpm : ∑ i, fp i * qm i = 1 / 2)
    (hmp : ∑ i, fm i * qp i = 1 / 2)
    (hmm : ∑ i, fm i * qm i = (N : ℝ) ^ 2 / 2) :
    oddEnergy N ≤ symmetricCornerEnergy fp fm qp qm := by
  let a := fun i => (fp i + fm i) / 2
  let b := fun i => (fp i - fm i) / 2
  let c := fun i => (qp i + qm i) / 2
  let d := fun i => (qp i - qm i) / 2
  let u := fun i => a i * c i
  let v := fun i => b i * d i
  have hu : ∑ i, u i = evenMass N := by
    calc
      (∑ i, u i) = ∑ i,
          (fp i * qp i + fp i * qm i + fm i * qp i + fm i * qm i) / 4 := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [u, a, c]
        ring
      _ = ((∑ i, fp i * qp i) + (∑ i, fp i * qm i) +
          (∑ i, fm i * qp i) + (∑ i, fm i * qm i)) / 4 := by
        rw [← Finset.sum_div]
        simp only [Finset.sum_add_distrib]
      _ = evenMass N := by rw [hpp, hpm, hmp, hmm]; unfold evenMass; ring
  have hv : ∑ i, v i = oddMass N := by
    calc
      (∑ i, v i) = ∑ i,
          (fp i * qp i - fp i * qm i - fm i * qp i + fm i * qm i) / 4 := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [v, b, d]
        ring
      _ = ((∑ i, fp i * qp i) - (∑ i, fp i * qm i) -
          (∑ i, fm i * qp i) + (∑ i, fm i * qm i)) / 4 := by
        rw [← Finset.sum_div]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = oddMass N := by rw [hpp, hpm, hmp, hmm]; unfold oddMass; ring
  have hpoint (i : ι) : massEnergy (u i) (v i) ≤
      3 / 8 * ((fp i * qp i) ^ 2 + (fm i * qm i) ^ 2) +
        1 / 16 * (fp i * qm i + fm i * qp i) ^ 2 := by
    have h := symmetric_corner_ge_mass (a i) (b i) (c i) (d i)
    convert h using 1
    dsimp [u, v, a, b, c, d]
    ring
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i
  have hbound := signed_mass_separation N hN hodd hcard u v hu hv
  apply hbound.trans
  simpa only [symmetricCornerEnergy, Finset.sum_add_distrib,
    ← Finset.mul_sum] using hs

/-- The ordinary four-corner bound follows from the stronger symmetric
one by a single pointwise square inequality. -/
theorem four_corner_lower (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (hcard : Fintype.card ι = N) (fp fm qp qm : ι → ℝ)
    (hpp : ∑ i, fp i * qp i = (N : ℝ) ^ 2 / 2)
    (hpm : ∑ i, fp i * qm i = 1 / 2)
    (hmp : ∑ i, fm i * qp i = 1 / 2)
    (hmm : ∑ i, fm i * qm i = (N : ℝ) ^ 2 / 2) :
    oddEnergy N ≤ fourCornerEnergy fp fm qp qm :=
  (symmetric_four_corner_lower N hN hodd hcard fp fm qp qm hpp hpm hmp hmm).trans
    (symmetricCornerEnergy_le_fourCornerEnergy fp fm qp qm)

/-- The symmetric estimate in exactly the article's parity-correction normalization. -/
theorem symmetric_four_corner_lower_normalized (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (hcard : Fintype.card ι = N) (fp fm qp qm : ι → ℝ)
    (hpp : ∑ i, fp i * qp i = (N : ℝ) ^ 2 / 2)
    (hpm : ∑ i, fp i * qm i = 1 / 2)
    (hmp : ∑ i, fm i * qp i = 1 / 2)
    (hmm : ∑ i, fm i * qm i = (N : ℝ) ^ 2 / 2) :
    (N : ℝ) ^ 3 / 4 * oddCorrectionSq N ≤ symmetricCornerEnergy fp fm qp qm := by
  rw [← oddEnergy_eq_correction (by omega : 0 < N)]
  exact symmetric_four_corner_lower N hN hodd hcard fp fm qp qm hpp hpm hmp hmm

/-- The ordinary estimate in the same normalization. -/
theorem four_corner_lower_normalized (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (hcard : Fintype.card ι = N) (fp fm qp qm : ι → ℝ)
    (hpp : ∑ i, fp i * qp i = (N : ℝ) ^ 2 / 2)
    (hpm : ∑ i, fp i * qm i = 1 / 2)
    (hmp : ∑ i, fm i * qp i = 1 / 2)
    (hmm : ∑ i, fm i * qm i = (N : ℝ) ^ 2 / 2) :
    (N : ℝ) ^ 3 / 4 * oddCorrectionSq N ≤ fourCornerEnergy fp fm qp qm := by
  rw [← oddEnergy_eq_correction (by omega : 0 < N)]
  exact four_corner_lower N hN hodd hcard fp fm qp qm hpp hpm hmp hmm

end
end bezout.Lower
