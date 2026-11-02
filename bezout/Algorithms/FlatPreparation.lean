import bezout.Flat.Iteration

/-!
Article: bezout, Algorithm 1 scalar preparation.
Use: verifies the recursive scalar U table, the single running source-mass sum,
and the exact values supplied to the four-register physical loop.
Proof: finite induction compares the scalar recurrence with the Chebyshev values;
the Hall normalization gives the printed closed formula for the common mass.
-/

namespace bezout.Algorithms.Flat
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The actual scalar U preparation, with its two printed startup values. -/
def preparedU (I : chebyshev1.SpectralInterval) : ℕ → ℝ
  | 0 => 1
  | 1 => 2*I.eta
  | s+2 => 2*I.eta*preparedU I (s+1)-preparedU I s

/-- The recursive scalar preparation equals every exterior U value. -/
theorem preparedU_eq (I : chebyshev1.SpectralInterval) (s : ℕ) :
    preparedU I s = bezout.Flat.u I s := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    match s with
    | 0 => simp [preparedU]
    | 1 => simp [preparedU]
    | s+2 => rw [preparedU, ih (s+1) (by omega), ih s (by omega), bezout.Flat.u_add_two]

/-- The article's scalar C is obtained from the final two prepared U values. -/
def preparedDen (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  I.eta * preparedU I (N-1) - preparedU I (N-2)

/-- The scalar preparation C is the prescribed terminal Chebyshev denominator. -/
theorem preparedDen_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    preparedDen I N = I.den N := by
  have h := congrArg (fun p : ℝ[X] => p.eval I.eta)
    (T_eq_X_mul_U_sub_U ℝ ((N-2 : ℕ) : ℤ))
  simp only [eval_sub, eval_mul, eval_X] at h
  rw [show ((N-2 : ℕ):ℤ)+1=((N-1 : ℕ):ℤ) by omega,
    show ((N-2 : ℕ):ℤ)+2=(N:ℤ) by omega] at h
  simpa only [preparedDen, preparedU_eq, bezout.Flat.u, chebyshev1.SpectralInterval.den] using h.symm

/-- The common response mass computed by the printed closed scalar formula. -/
def preparedMass (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  (preparedDen I N - 1)/(2*(N:ℝ)*(I.eta-1))

/-- The prepared scalar d is exactly the construction's equal target mass. -/
theorem preparedMass_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    preparedMass I N = bezout.Flat.unitMass I N := by
  rw [preparedMass, preparedDen_eq I N hN, bezout.Flat.unitMass,
    bezout.Flat.totalMass_formula I N (by omega)]
  rw [div_div]
  congr 1
  ring

/-- The running scalar S, initialized by the half-weighted degree-zero source. -/
def preparedPrefix (I : chebyshev1.SpectralInterval) (N : ℕ) : ℕ → ℝ
  | 0 => preparedU I (N-1)/2
  | m+1 => preparedPrefix I N m + preparedU I (N-2-m)

/-- The running sum equals the exact prefix source mass at every prepared index. -/
theorem preparedPrefix_eq (I : chebyshev1.SpectralInterval) (N : ℕ)
    (m : ℕ) (hm : m<N) : preparedPrefix I N m = bezout.Flat.prefixMass I N m := by
  induction m with
  | zero => simp [preparedPrefix, preparedU_eq, bezout.Flat.prefixMass, bezout.Flat.mass]
  | succ m ih =>
    rw [preparedPrefix, preparedU_eq, ih (by omega), bezout.Flat.prefixMass_succ]
    simp only [bezout.Flat.mass, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    congr 2
    omega

/-- The actual extrapolation scalar produced by the reversed running-sum loop. -/
def preparedTau (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ :=
  (preparedPrefix I N (N-1-s) - ((N-1-s:ℕ):ℝ)*preparedMass I N) /
    preparedMass I N - 1

/-- Every scalar emitted by the preparation loop is the exact Flat extrapolation. -/
theorem preparedTau_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : preparedTau I N s.val = bezout.Flat.tau I N s.val := by
  rw [preparedTau, preparedPrefix_eq I N _ (by omega), preparedMass_eq I N hN]
  rfl

end
end bezout.Algorithms.Flat
