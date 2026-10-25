import polyak.ModeLocking.Continuation.ResidueSums
import polyak.ModeLocking.Continuation.JointSlope

/-! Exact slope moments for every signed lag in every tight class. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open General Levels
open scoped BigOperators

def phaseExtension (q : Tuning) (s x : ℝ) : ℝ :=
  Geometry.jointAngle ![q.kappa, q.y, q.beta, s, x]

theorem analyticAt_phaseExtension (q : Tuning) (s : ℝ) (ω : Frequency) :
    AnalyticAt ℝ (phaseExtension q s) (ω : ℝ) := by
  have hp : AnalyticAt ℝ (fun x : ℝ => ![q.kappa, q.y, q.beta, s, x]) (ω : ℝ) := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    all_goals first | exact analyticAt_const | exact analyticAt_id
  exact (Geometry.analyticAt_jointAngle_actual q s ω.property).comp
    (f := fun x : ℝ => ![q.kappa, q.y, q.beta, s, x]) hp

theorem slope_mod_grid (q : Tuning) (s : ℝ) {L : ℕ} (ω : Frequency)
    (hω : ω ∈ periodicGrid L) (n : ℤ) :
    deriv (lagExtension q s n) ω = deriv (lagExtension q s (n % (L : ℤ))) ω +
      ((n / (L : ℤ) : ℤ) : ℝ) * L *
        Real.sin (((n % (L : ℤ) : ℤ) : ℝ) * (ω : ℝ) - Geometry.shiftedCurve q s ω) := by
  have he : n = n % (L : ℤ) + (n / (L : ℤ)) * L := (Int.emod_add_ediv_mul n L).symm
  have hp := pinning_derivative (analyticAt_phaseExtension q s ω).differentiableAt.hasDerivAt
    hω (n % (L : ℤ)) (n / (L : ℤ))
  have ha : phaseExtension q s ω = Geometry.shiftedCurve q s ω := by
    rw [phaseExtension, Geometry.jointAngle_actual q s ω.property]
    rfl
  rw [ha] at hp
  conv_lhs => rw [he]
  exact hp

end polyak.ModeLocking.Continuation

namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def classSlope (i r : Fin D.d) : ℝ := deriv (lagExtension q s (D.reps r)) (D.atoms i)

def pinningMatrix : Matrix (Fin D.d) (Fin D.d) ℝ :=
  fun i r => (L : ℝ) * Real.sin ((D.reps r : ℝ) * (D.atoms i : ℝ) - Geometry.shiftedCurve q s (D.atoms i))

def zeroClassSlope (i : Fin D.d) : ℝ :=
  ∑ n ∈ D.lags, if n % (L : ℤ) = 0 then D.dual n * deriv (lagExtension q s n) (D.atoms i) else 0

theorem symbol_slope_identity (i : Fin D.d) :
    deriv (finiteSymbol q s D.lags D.dual) (D.atoms i : ℝ) =
      (∑ r, D.classWeight r * D.classSlope i r) +
        D.pinningMatrix.mulVec D.slopeMoment i + D.zeroClassSlope i := by
  classical
  have he : deriv (finiteSymbol q s D.lags D.dual) (D.atoms i : ℝ) =
      ∑ n ∈ D.lags, D.dual n * deriv (lagExtension q s n) (D.atoms i) := by
    unfold finiteSymbol
    rw [deriv_fun_sum (fun n _ => (analyticAt_lagExtension q s n (D.atoms i).property).differentiableAt.const_mul _)]
    simp only [deriv_const_mul_field]
  rw [he, D.sum_classes]
  change (∑ r, ∑ n ∈ D.lags, if n % (L : ℤ) = D.reps r then _ else 0) + D.zeroClassSlope i = _
  congr 1
  change (∑ r, ∑ n ∈ D.lags, if n % (L : ℤ) = D.reps r then _ else 0) =
    (∑ r, D.classWeight r * D.classSlope i r) + ∑ r, D.pinningMatrix i r * D.slopeMoment r
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  change (∑ n ∈ D.lags, if n % (L : ℤ) = D.reps r then _ else 0) =
    D.classWeight r * D.classSlope i r + D.pinningMatrix i r * D.slopeMoment r
  simp only [classWeight, slopeMoment, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n % (L : ℤ) = D.reps r
  · rw [ite_eq_left hn]
    rw [Continuation.slope_mod_grid q s (D.atoms i) (D.atoms_grid i) n, hn]
    simp only [ite_true, classSlope, pinningMatrix]
    ring
  · simp only [ite_eq_right hn, zero_mul, mul_zero, add_zero]

theorem pinning_system_base : D.pinningMatrix.mulVec D.slopeMoment =
    fun i => -(∑ r, D.classWeight r * D.classSlope i r) - D.zeroClassSlope i := by
  funext i
  have he := D.symbol_slope_identity i
  rw [D.symbol_slope_support i] at he
  change D.pinningMatrix.mulVec D.slopeMoment i = _
  linarith

end polyak.ModeLocking.RegularData
