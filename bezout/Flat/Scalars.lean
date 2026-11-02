import chebyshev1.Chebyshev.Normalization
import Mathlib.Algebra.BigOperators.Fin

/-!
Article: bezout, Equation (10) (`eq:hall-data`) and Appendix B.
Use: actual scalar data of the Flat construction, fixed before every oracle call.
Proof: the second-kind Chebyshev recurrence gives positive increasing values
outside the spectral interval and the normalized degree monotonicity used by
the equal-mass feasibility proof.
-/

namespace bezout.Flat
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The second-kind Chebyshev value at the prescribed exterior point eta.
Use: the normalized virtual states and every Flat scalar coefficient. -/
def u (I : chebyshev1.SpectralInterval) (s : ℕ) : ℝ := (U ℝ s).eval I.eta

/-- The first exterior value is one.
Use: the initial normalized virtual state. -/
@[simp] theorem u_zero (I : chebyshev1.SpectralInterval) : u I 0 = 1 := by simp [u]

/-- The second exterior value is twice eta.
Use: the first physical gradient step. -/
@[simp] theorem u_one (I : chebyshev1.SpectralInterval) : u I 1 = 2 * I.eta := by simp [u]

/-- The exact scalar Chebyshev preparation recurrence.
Use: computes all exterior values using linear scalar work. -/
theorem u_add_two (I : chebyshev1.SpectralInterval) (s : ℕ) :
    u I (s + 2) = 2 * I.eta * u I (s + 1) - u I s := by
  have h := congrArg (fun p : ℝ[X] => p.eval I.eta) (U_add_two ℝ (s : ℤ))
  simpa only [u, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, eval_sub, eval_mul, eval_ofNat, eval_X, mul_assoc] using h

/-- Exterior second-kind values are positive and strictly increase with their degree.
Use: positivity of all construction masses and monotonicity of their tail. -/
theorem u_growth (I : chebyshev1.SpectralInterval) (s : ℕ) :
    0 < u I s ∧ u I s < u I (s + 1) := by
  induction s with
  | zero => simp only [u_zero, zero_add, u_one]; constructor <;> linarith [I.eta_gt_one]
  | succ s ih =>
    have hp : 0 < u I (s + 1) := lt_trans ih.1 ih.2
    have hprod : 0 < (I.eta - 1) * u I (s + 1) := mul_pos (by linarith [I.eta_gt_one]) hp
    rw [show s + 1 + 1 = s + 2 by omega, u_add_two]
    exact ⟨hp, by nlinarith [ih.2]⟩

/-- Every exterior normalizing denominator is strictly positive.
Use: all scalar divisions in Flat are valid. -/
theorem u_pos (I : chebyshev1.SpectralInterval) (s : ℕ) : 0 < u I s := (u_growth I s).1

/-- Exterior values have strictly increasing normalized degree averages.
Use: bounds all source masses by the final normalized exterior value. -/
theorem u_ratio_cross (I : chebyshev1.SpectralInterval) (s : ℕ) :
    ((s : ℝ) + 2) * u I s < ((s : ℝ) + 1) * u I (s + 1) := by
  induction s with
  | zero => simp only [Nat.cast_zero, zero_add, u_zero, u_one, mul_one, one_mul]
            linarith [I.eta_gt_one]
  | succ s ih =>
    rw [show s + 1 + 1 = s + 2 by omega, u_add_two]
    push_cast
    have hp : 0 < ((s : ℝ) + 2) * (I.eta - 1) * u I (s + 1) := by
      have := I.eta_gt_one
      exact mul_pos (mul_pos (by positivity) (by linarith)) (u_pos I _)
    nlinarith

/-- The normalized exterior sequence is increasing.
Use: obtains the equal-response mass feasibility without an integral estimate. -/
theorem u_ratio_strictMono (I : chebyshev1.SpectralInterval) :
    StrictMono (fun s : ℕ => u I s / ((s : ℝ) + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro s
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have h := u_ratio_cross I s
  push_cast
  nlinarith

/-- The source mass associated with Chebyshev degree m at horizon N.
Use: the displayed `a_m`, including its half-weight at degree zero. -/
def mass (I : chebyshev1.SpectralInterval) (N m : ℕ) : ℝ :=
  if m = 0 then u I (N - 1) / 2 else u I (N - 1 - m)

/-- Prefix sum of source masses, including both endpoint degrees.
Use: the displayed `A_m`. -/
def prefixMass (I : chebyshev1.SpectralInterval) (N m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), mass I N j

/-- Total source mass of the horizon's Bezoutian section.
Use: the displayed `M`. -/
def totalMass (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ := prefixMass I N (N - 1)

/-- Common equal-response mass.
Use: the displayed `d=M/N`. -/
def unitMass (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ := totalMass I N / N

/-- Remaining reservoir after m equal masses have been extracted.
Use: the displayed `R_m`. -/
def reservoir (I : chebyshev1.SpectralInterval) (N m : ℕ) : ℝ :=
  prefixMass I N m - (m : ℝ) * unitMass I N

/-- Query extrapolation from the remaining reversed reservoir.
Use: the displayed `tau_s` of the actual Flat construction. -/
def tau (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ :=
  reservoir I N (N - 1 - s) / unitMass I N - 1

/-- Every source mass is positive, including the half-weighted initial mass.
Use: positivity of total mass and the convex mixture coefficients. -/
theorem mass_pos (I : chebyshev1.SpectralInterval) (N m : ℕ) : 0 < mass I N m := by
  unfold mass
  split_ifs
  · exact div_pos (u_pos I _) (by norm_num)
  · exact u_pos I _

/-- Prefix mass satisfies the exact one-step preparation recursion.
Use: reservoir and telescoping identities. -/
theorem prefixMass_succ (I : chebyshev1.SpectralInterval) (N m : ℕ) :
    prefixMass I N (m + 1) = prefixMass I N m + mass I N (m + 1) := by
  exact Finset.sum_range_succ _ _

/-- Reversing the positive tail gives the explicit total mass.
Use: the source-mass feasibility estimate. -/
theorem totalMass_succ (I : chebyshev1.SpectralInterval) (n : ℕ) :
    totalMass I (n + 1) = u I n / 2 + ∑ k ∈ Finset.range n, u I k := by
  unfold totalMass prefixMass
  simp only [Nat.add_sub_cancel, Finset.sum_range_succ']
  simp only [mass, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel, ite_true]
  rw [show (∑ k ∈ Finset.range n, u I (n - (k + 1))) = ∑ k ∈ Finset.range n, u I k by
    simpa only [Nat.sub_sub, Nat.add_comm] using Finset.sum_range_reflect (u I) n]
  ring

/-- The real sum of the first n positive integers.
Use: sums normalized exterior-value estimates without integer division. -/
private theorem sum_cast_add_one (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The first half-weighted source mass is at least the target equal mass.
Use: the left endpoint condition of discrete reservoir concavity. -/
theorem unitMass_le_first (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    unitMass I N ≤ mass I N 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hbound : ∀ k < n, u I k * ((n : ℝ) + 1) ≤ u I n * ((k : ℝ) + 1) := by
    intro k hk
    have h := (u_ratio_strictMono I).monotone (Nat.le_of_lt hk)
    exact (div_le_div_iff₀ (by positivity) (by positivity)).mp h
  have hs := Finset.sum_le_sum (s := Finset.range n)
    (fun k hk => hbound k (Finset.mem_range.mp hk))
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_cast_add_one] at hs
  unfold unitMass
  rw [totalMass_succ]
  simp only [mass, ite_true, Nat.succ_sub_one, Nat.cast_succ]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  nlinarith

/-- Total source mass is positive at every nonzero horizon.
Use: validity of division by the equal target mass. -/
theorem totalMass_pos (I : chebyshev1.SpectralInterval) (N : ℕ) :
    0 < totalMass I N := by
  unfold totalMass prefixMass
  exact Finset.sum_pos (fun j _ => mass_pos I N j) (by simp)

/-- Every nonzero horizon has a positive equal target mass.
Use: query extrapolation and convex coefficient denominators. -/
theorem unitMass_pos (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    0 < unitMass I N := div_pos (totalMass_pos I N) (by exact_mod_cast hN)

/-- Source masses decrease after the initial half-weighted source.
Use: the discrete concavity of the reservoir path. -/
theorem mass_antitone_tail (I : chebyshev1.SpectralInterval) (N : ℕ)
    {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) : mass I N k ≤ mass I N j := by
  have hu : Monotone (u I) := (strictMono_nat_of_lt_succ (fun s => (u_growth I s).2)).monotone
  simp only [mass, Nat.ne_of_gt hj, ite_false, Nat.ne_of_gt (lt_of_lt_of_le hj hjk)]
  exact hu (by omega)

/-- Prefix mass always covers its share of the equal targets.
Use: the complete feasibility statement behind nonnegative extrapolation. -/
theorem prefixMass_ge (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (hm : m < N) : ((m : ℝ) + 1) * unitMass I N ≤ prefixMass I N m := by
  by_cases hmd : unitMass I N ≤ mass I N m
  · have hs : ∀ j ∈ Finset.range (m + 1), unitMass I N ≤ mass I N j := by
      intro j hj
      by_cases hj0 : j = 0
      · subst j; exact unitMass_le_first I N hN
      · exact hmd.trans (mass_antitone_tail I N (by omega) (by have := Finset.mem_range.mp hj; omega))
    have h := Finset.sum_le_sum hs
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one, prefixMass] using h
  · have hmpos : 0 < m := by
      by_contra hm0
      have hm0' : m = 0 := by omega
      subst m
      exact hmd (unitMass_le_first I N hN)
    have htail : (∑ j ∈ Finset.Ico (m + 1) N, mass I N j) ≤
        ((N : ℝ) - ((m : ℝ) + 1)) * unitMass I N := by
      have hs := Finset.sum_le_sum (s := Finset.Ico (m + 1) N)
        (fun j hj => (mass_antitone_tail I N (by omega : 0 < m + 1)
          (Finset.mem_Ico.mp hj).1).trans
          ((mass_antitone_tail I N hmpos (by omega)).trans (le_of_not_ge hmd)))
      simpa only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
        Nat.cast_sub (by omega : m + 1 ≤ N), Nat.cast_add, Nat.cast_one] using hs
    have hsplit := Finset.sum_range_add_sum_Ico (mass I N) (by omega : m + 1 ≤ N)
    have htotal : totalMass I N = (N : ℝ) * unitMass I N := by
      unfold unitMass
      field_simp
    have hprefix : prefixMass I N m + (∑ j ∈ Finset.Ico (m + 1) N, mass I N j) = totalMass I N := by
      simpa only [prefixMass, totalMass, show N - 1 + 1 = N by omega] using hsplit
    linarith

/-- The reservoir recurrence subtracts one target mass at each new source.
Use: the exact balancing telescoping identity. -/
theorem reservoir_succ (I : chebyshev1.SpectralInterval) (N m : ℕ) :
    reservoir I N (m + 1) = reservoir I N m - unitMass I N + mass I N (m + 1) := by
  unfold reservoir
  rw [prefixMass_succ]
  push_cast
  ring

/-- Every reservoir can cover a complete target mass.
Use: nonnegative extrapolation at every query. -/
theorem unitMass_le_reservoir (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (hm : m < N) : unitMass I N ≤ reservoir I N m := by
  have := prefixMass_ge I N hN m hm
  unfold reservoir
  linarith

/-- Every reservoir can cover its newest source mass.
Use: convexity of the first-kind Chebyshev mixture. -/
theorem mass_le_reservoir (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (hm : m < N) : mass I N m ≤ reservoir I N m := by
  cases m with
  | zero => simp [reservoir, prefixMass]
  | succ m =>
    rw [reservoir_succ]
    have := unitMass_le_reservoir I N hN m (by omega)
    linarith

/-- All actual reservoir denominators are positive.
Use: the Flat convex recursion is everywhere defined. -/
theorem reservoir_pos (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (hm : m < N) : 0 < reservoir I N m :=
  lt_of_lt_of_le (unitMass_pos I N hN) (unitMass_le_reservoir I N hN m hm)

/-- The final reservoir is exactly one equal target mass.
Use: zero extrapolation at the first physical call. -/
theorem reservoir_last (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    reservoir I N (N - 1) = unitMass I N := by
  have ht : totalMass I N = (N : ℝ) * unitMass I N := by unfold unitMass; field_simp
  unfold reservoir
  change totalMass I N - ((N - 1 : ℕ) : ℝ) * unitMass I N = unitMass I N
  rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one, ht]
  ring

/-- Extrapolation is nonnegative at every actual query.
Use: restoring the virtual state and its affine gradient uses a positive divisor. -/
theorem tau_nonneg (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : ℕ) (hs : s < N) : 0 ≤ tau I N s := by
  have hr := unitMass_le_reservoir I N hN (N - 1 - s) (by omega)
  have hd := unitMass_pos I N hN
  unfold tau
  exact sub_nonneg.mpr ((le_div_iff₀ hd).mpr (by simpa using hr))

/-- The initial query has no extrapolation.
Use: startup of the four-vector implementation. -/
@[simp] theorem tau_zero (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    tau I N 0 = 0 := by
  simp only [tau, Nat.sub_zero, reservoir_last I N hN, div_self (ne_of_gt (unitMass_pos I N hN)), sub_self]

end
end bezout.Flat
