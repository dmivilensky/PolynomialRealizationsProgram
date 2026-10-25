import polyak.Levels.Geometry.JointAnalytic
import polyak.Levels.Geometry.LagEnds
import polyak.Levels.Program.AtomicProgram
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Literal finite data and the three primary regularity conditions. The rows
and columns have a common finite index, so the equality of cardinalities in
(R1) is part of the indexing, not a later identification of matrices. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels
open scoped BigOperators

def lagExtension (q : Tuning) (s : ℝ) (n : ℤ) (x : ℝ) : ℝ :=
  Geometry.extendedLag (fun x => Geometry.jointAngle
    ![q.kappa, q.y, q.beta, s, x]) n x

def finiteSymbol (q : Tuning) (s : ℝ) (N : Finset ℤ) (a : ℤ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ N, a n * lagExtension q s n x

def pinningPolynomial (N : Finset ℤ) (a : ℤ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ N, a n * (1 - Real.cos ((n : ℝ) * x))

/-- All inequalities are on the original lag functions. The zero residue is
kept separately: its weights are not dropped from the dual symbol. -/
structure RegularData (q : Tuning) (s : ℝ) (L : ℕ) where
  period_ge : 3 ≤ L
  d : ℕ
  atoms : Fin d → Frequency
  atoms_injective : Function.Injective atoms
  atoms_grid : ∀ i, atoms i ∈ periodicGrid L
  atoms_lt_pi : ∀ i, (atoms i : ℝ) < Real.pi
  reps : Fin d → ℤ
  reps_pos : ∀ i, 0 < reps i
  reps_lt : ∀ i, reps i < L
  reps_injective : Function.Injective reps
  lags : Finset ℤ
  lags_nonzero : ∀ n ∈ lags, n ≠ 0
  classes : ∀ n ∈ lags, n % (L : ℤ) = 0 ∨ ∃ i, n % (L : ℤ) = reps i
  primal : Fin d → NNReal
  primal_pos : ∀ i, 0 < primal i
  primal_sum : ∑ i, primal i = 1
  dual : ℤ → ℝ
  dual_pos : ∀ n ∈ lags, 0 < dual n
  dual_sum : ∑ n ∈ lags, dual n = 1
  tight : ∀ r, ∑ i, (primal i : ℝ) * (Geometry.shiftedCurve q s).lag (reps r) (atoms i) = 0
  inactive : ∀ r : ℤ, 0 < r → r < L → (∀ i, r ≠ reps i) →
    0 < ∑ i, (primal i : ℝ) * (Geometry.shiftedCurve q s).lag r (atoms i)
  minimizer_strict : 0 < ∑ i, (primal i : ℝ) * (Geometry.shiftedCurve q s).minimizer (atoms i)
  rank : Matrix.rank (fun r i : Fin d => (Geometry.shiftedCurve q s).lag (reps r) (atoms i)) = d - 1
  dual_strict : ∀ x : ℝ, 0 < x → x ≤ Real.pi → (∀ i, x ≠ (atoms i : ℝ)) →
    finiteSymbol q s lags dual x < 0
  support_curvature : ∀ i, deriv^[2] (finiteSymbol q s lags dual) (atoms i : ℝ) < 0
  endpoint_curvature : 0 < ∑ n ∈ lags, dual n * (n : ℝ) * ((n : ℝ) + 2 * Geometry.tau q)
  pinning_pos : ∀ i, 0 < pinningPolynomial lags dual (atoms i)
  class_pair : ∀ i, ∃ n₁ ∈ lags, ∃ n₂ ∈ lags,
    n₁ ≠ n₂ ∧ n₁ % (L : ℤ) = reps i ∧ n₂ % (L : ℤ) = reps i
  pinning_det : Matrix.det (fun i r : Fin d => Real.sin ((reps r : ℝ) * (atoms i : ℝ) -
    Geometry.shiftedCurve q s (atoms i))) ≠ 0

def RegularPoint (q : Tuning) (s : ℝ) (L : ℕ) : Prop := Nonempty (RegularData q s L)

theorem lagExtension_actual (q : Tuning) (s : ℝ) (n : ℤ) (ω : Frequency) :
    lagExtension q s n ω = (Geometry.shiftedCurve q s).lag n ω := by
  unfold lagExtension Geometry.extendedLag Curve.lag
  simp only [Geometry.jointAngle_actual q s ω.property]
  rfl

theorem finiteSymbol_actual (q : Tuning) (s : ℝ) (N : Finset ℤ) (a : ℤ → ℝ)
    (ω : Frequency) : finiteSymbol q s N a ω =
      ∑ n ∈ N, a n * (Geometry.shiftedCurve q s).lag n ω := by
  simp only [finiteSymbol, lagExtension_actual]

namespace RegularData
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def matrix : Matrix (Fin D.d) (Fin D.d) ℝ :=
  fun r i => (Geometry.shiftedCurve q s).lag (D.reps r) (D.atoms i)

def zeroClass : Finset ℤ := by
  classical
  exact D.lags.filter (fun n => n % (L : ℤ) = 0)

def lagClass (i : Fin D.d) : Finset ℤ := by
  classical
  exact D.lags.filter (fun n => n % (L : ℤ) = D.reps i)

def measure : MeasureTheory.Measure Frequency := atomicMeasure D.primal D.atoms

theorem d_pos : 0 < D.d := by
  by_contra hn
  have he : ∑ i, D.primal i = 0 := Finset.sum_eq_zero (fun i _ => by have hi := i.isLt; omega)
  exact zero_ne_one (he.symm.trans D.primal_sum)

theorem matrix_mul_primal : D.matrix.mulVec (fun i => (D.primal i : ℝ)) = 0 := by
  funext r
  simpa only [matrix, Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using D.tight r

theorem primal_feasible : ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags D.measure := by
  rw [measure, atomic_program_iff (Geometry.shiftedCurve q s) (lt_of_lt_of_le (by norm_num : 0 < 3) D.period_ge)
    D.primal D.atoms (by rw [D.primal_sum]; norm_num) D.atoms_grid]
  refine ⟨D.minimizer_strict.le, ?_⟩
  intro r hr hrL
  by_cases ht : ∃ i, (r : ℤ) = D.reps i
  · obtain ⟨i, hi⟩ := ht
    rw [hi, D.tight i]
  · apply le_of_lt
    exact D.inactive r (by exact_mod_cast hr) (by exact_mod_cast hrL)
      (by simpa only [not_exists] using ht)

include D in
theorem periodic_feasible : PeriodicFP (Geometry.shiftedCurve q s) L :=
  ⟨D.measure, D.primal_feasible, atomicMeasure_carried_grid D.primal D.atoms L D.atoms_grid⟩

end RegularData
end polyak.ModeLocking
