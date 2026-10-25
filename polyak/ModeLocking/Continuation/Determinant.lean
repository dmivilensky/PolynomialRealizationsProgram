import polyak.ModeLocking.Regular.Kernel
import polyak.ModeLocking.Continuation.Implicit

/-! The actual tight matrix, extended analytically in the four original
source coordinates (kappa,y,beta,shift), and its determinant. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open General Levels
open scoped BigOperators

abbrev SourcePoint := Fin 4 → ℝ

def sourcePoint (q : Tuning) (s : ℝ) : SourcePoint := ![q.kappa, q.y, q.beta, s]

theorem analyticAt_source_coordinate (p : SourcePoint) (i : Fin 4) :
    AnalyticAt ℝ (fun p : SourcePoint => p i) p :=
  (ContinuousLinearMap.proj (R := ℝ) i).analyticAt p

def ambientPhase (ω : Frequency) (p : SourcePoint) : ℝ :=
  Geometry.jointAngle ![p 0, p 1, p 2, p 3, (ω : ℝ)]

def ambientLag (n : ℤ) (ω : Frequency) (p : SourcePoint) : ℝ :=
  Real.cos (ambientPhase ω p) - Real.cos ((n : ℝ) * (ω : ℝ) - ambientPhase ω p)

def tightMatrix {d : ℕ} (r : Fin d → ℤ) (a : Fin d → Frequency) (p : SourcePoint) :
    Matrix (Fin d) (Fin d) ℝ := fun i j => ambientLag (r i) (a j) p

def tightDeterminant {d : ℕ} (r : Fin d → ℤ) (a : Fin d → Frequency) (p : SourcePoint) : ℝ :=
  Matrix.det (tightMatrix r a p)

theorem ambientPhase_actual (q : Tuning) (s : ℝ) (ω : Frequency) :
    ambientPhase ω (sourcePoint q s) = Geometry.shiftedCurve q s ω := by
  change Geometry.jointAngle ![q.kappa, q.y, q.beta, s, (ω : ℝ)] = _
  rw [Geometry.jointAngle_actual q s ω.property]
  rfl

theorem ambientLag_actual (q : Tuning) (s : ℝ) (n : ℤ) (ω : Frequency) :
    ambientLag n ω (sourcePoint q s) = (Geometry.shiftedCurve q s).lag n ω := by
  simp only [ambientLag, ambientPhase_actual, Curve.lag]

theorem analyticAt_ambientPhase (q : Tuning) (s : ℝ) (ω : Frequency) :
    AnalyticAt ℝ (ambientPhase ω) (sourcePoint q s) := by
  have hp : AnalyticAt ℝ (fun p : SourcePoint => ![p 0, p 1, p 2, p 3, (ω : ℝ)])
      (sourcePoint q s) := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact analyticAt_source_coordinate _ 0
    · exact analyticAt_source_coordinate _ 1
    · exact analyticAt_source_coordinate _ 2
    · exact analyticAt_source_coordinate _ 3
    · exact analyticAt_const
  exact (Geometry.analyticAt_jointAngle_actual q s ω.property).comp
    (f := fun p : SourcePoint => ![p 0, p 1, p 2, p 3, (ω : ℝ)]) hp

theorem analyticAt_ambientLag (q : Tuning) (s : ℝ) (n : ℤ) (ω : Frequency) :
    AnalyticAt ℝ (ambientLag n ω) (sourcePoint q s) := by
  exact (Real.analyticAt_cos.comp (analyticAt_ambientPhase q s ω)).sub
    (Real.analyticAt_cos.comp (analyticAt_const.sub (analyticAt_ambientPhase q s ω)))

theorem analyticAt_tightDeterminant (q : Tuning) (s : ℝ) {d : ℕ}
    (r : Fin d → ℤ) (a : Fin d → Frequency) :
    AnalyticAt ℝ (tightDeterminant r a) (sourcePoint q s) := by
  classical
  unfold tightDeterminant
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  exact analyticAt_ambientLag q s (r (σ i)) (a i)

end polyak.ModeLocking.Continuation

namespace polyak.ModeLocking.RegularData
open General Levels
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem tightDeterminant_zero : Continuation.tightDeterminant D.reps D.atoms
    (Continuation.sourcePoint q s) = 0 := by
  have hne : ¬ Function.Injective D.matrix.mulVec := by
    intro hi
    apply D.primal_ne_zero
    apply hi
    simpa only [Matrix.mulVec_zero] using D.matrix_mul_primal
  have hdet : D.matrix.det = 0 := by
    by_contra hn
    exact hne (Matrix.mulVec_injective_of_det_ne_zero hn)
  have hm : Continuation.tightMatrix D.reps D.atoms (Continuation.sourcePoint q s) = D.matrix := by
    ext i j
    exact Continuation.ambientLag_actual q s (D.reps i) (D.atoms j)
  rw [Continuation.tightDeterminant, hm]
  exact hdet

end polyak.ModeLocking.RegularData
