import Mathlib.Tactic

/-!
Article: bezout, Lemma C.1 (`lem:two-masses`).
Use: the signed two-mass energy controls the symmetric four-corner energy
without a sign or parity restriction on the factors of the Bezoutian.
The local identities below also give coercivity and the exact polynomial
branches used in the explicit supporting-quadratic certificates.
-/

namespace bezout.Lower

noncomputable section
open scoped BigOperators

/-- The signed two-mass energy of Lemma C.1. -/
def massEnergy (u v : ℝ) : ℝ :=
  if 0 ≤ u * v then u ^ 2 + v ^ 2 + 4 * u * v else u ^ 2 + v ^ 2 + u * v

/-- The energy is invariant under interchanging the two masses. -/
theorem massEnergy_comm (u v : ℝ) : massEnergy u v = massEnergy v u := by
  simp only [massEnergy, mul_comm u v]
  split_ifs <;> ring

/-- On one closed sign cone the energy is the stated polynomial. -/
theorem massEnergy_of_mul_nonneg {u v : ℝ} (h : 0 ≤ u * v) :
    massEnergy u v = u ^ 2 + v ^ 2 + 4 * u * v := by simp [massEnergy, h]

/-- On the opposite closed sign cone the other polynomial remains valid at the axes. -/
theorem massEnergy_of_mul_nonpos {u v : ℝ} (h : u * v ≤ 0) :
    massEnergy u v = u ^ 2 + v ^ 2 + u * v := by
  unfold massEnergy
  split_ifs with h'
  · have : u * v = 0 := le_antisymm h h'
    nlinarith
  · rfl

/-- Coercivity controls arbitrary signed profiles in the mass comparison. -/
theorem massEnergy_coercive (u v : ℝ) :
    (u ^ 2 + v ^ 2) / 2 ≤ massEnergy u v := by
  unfold massEnergy
  split_ifs with h
  · nlinarith [sq_nonneg u, sq_nonneg v]
  · nlinarith [sq_nonneg (u + v)]

/-- In particular every individual energy is nonnegative. -/
theorem massEnergy_nonneg (u v : ℝ) : 0 ≤ massEnergy u v := by
  have := massEnergy_coercive u v
  nlinarith [sq_nonneg u, sq_nonneg v]

/-- Simultaneous sign reversal does not change the energy. -/
theorem massEnergy_neg_neg (u v : ℝ) : massEnergy (-u) (-v) = massEnergy u v := by
  simp only [massEnergy, neg_mul_neg, neg_sq]
  split_ifs <;> ring

/-- The exact masses read from the four corners of the odd Chebyshev Bezoutian. -/
def evenMass (N : ℕ) : ℝ := ((N : ℝ) ^ 2 + 1) / 4

/-- The exact odd-parity mass read from the same corner identities. -/
def oddMass (N : ℕ) : ℝ := ((N : ℝ) ^ 2 - 1) / 4

/-- Squared parity correction appearing in the sharp gain. -/
def oddCorrectionSq (N : ℕ) : ℝ :=
  1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2)

/-- The sharp squared corner energy, with its denominator already cancelled. -/
def oddEnergy (N : ℕ) : ℝ :=
  (N : ℝ) ^ 3 / 4 + (N : ℝ) * ((N : ℝ) - 1) / (4 * ((N : ℝ) + 1))

/-- The cancelled expression agrees with the article's cubic normalization. -/
theorem oddEnergy_eq_correction {N : ℕ} (hN : 0 < N) :
    oddEnergy N = (N : ℝ) ^ 3 / 4 * oddCorrectionSq N := by
  have h : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hp : (N : ℝ) + 1 ≠ 0 := by positivity
  unfold oddEnergy oddCorrectionSq
  field_simp

/-- An absolute-value representation makes continuity at the sign axes explicit. -/
theorem massEnergy_eq_abs (u v : ℝ) :
    massEnergy u v = u ^ 2 + v ^ 2 + (5 / 2 : ℝ) * (u * v) +
      (3 / 2 : ℝ) * |u * v| := by
  unfold massEnergy
  split_ifs with h
  · rw [abs_of_nonneg h]
    ring
  · rw [abs_of_neg (lt_of_not_ge h)]
    ring

/-- The symmetric corner combination dominates the signed mass energy pointwise.
This identity preserves the coupling of the two off-diagonal entries that is
required by symmetric Hilbert--Schmidt perturbations. -/
theorem symmetric_corner_ge_mass (a b c d : ℝ) :
    massEnergy (a * c) (b * d) ≤
      3 / 8 * (((a + b) * (c + d)) ^ 2 + ((a - b) * (c - d)) ^ 2) +
        1 / 16 * ((a + b) * (c - d) + (a - b) * (c + d)) ^ 2 := by
  unfold massEnergy
  split_ifs with h
  · nlinarith only [sq_nonneg (a * d - b * c)]
  · nlinarith only [sq_nonneg (a * d + b * c)]

/-- Replacing the symmetrized cross profile by the two separate squares can
only enlarge the weighted corner energy. -/
theorem symmetric_corner_le_four_corner (fp fm qp qm : ℝ) :
    3 / 8 * ((fp * qp) ^ 2 + (fm * qm) ^ 2) +
      1 / 16 * (fp * qm + fm * qp) ^ 2 ≤
    3 / 8 * ((fp * qp) ^ 2 + (fm * qm) ^ 2) +
      1 / 8 * ((fp * qm) ^ 2 + (fm * qp) ^ 2) := by
  nlinarith only [sq_nonneg (fp * qm - fm * qp)]

end
end bezout.Lower
