import polyak.Global.Circle.Fold
import polyak.Levels.Program.Definitions

/-! Exact transfer of every signed lag and the minimizer moment. -/
noncomputable section
namespace polyak.Global.Circle
open MeasureTheory Set
open scoped ENNReal NNReal

def lag (Θ : Levels.Curve) (n : ℤ) (x : Circle) : ℝ := Θ.lag n (fold x)
def minimizer (Θ : Levels.Curve) (x : Circle) : ℝ := Θ.minimizer (fold x)

theorem lag_continuous (Θ : Levels.Curve) (n:ℤ) : Continuous (lag Θ n) :=
  (Θ.continuous_lag n).comp continuous_fold

theorem minimizer_continuous (Θ : Levels.Curve) : Continuous (minimizer Θ) :=
  Θ.continuous_minimizer.comp continuous_fold

@[simp] theorem lag_neg (Θ : Levels.Curve) (n:ℤ) (x:Circle) : lag Θ n (-x)=lag Θ n x := by simp [lag]
@[simp] theorem minimizer_neg (Θ : Levels.Curve) (x:Circle) : minimizer Θ (-x)=minimizer Θ x := by simp [minimizer]

@[simp] theorem integral_folded {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ:Measure Circle) (f:Levels.Frequency→E) (hf:Continuous f) :
    ∫ω,f ω∂folded μ=∫x,f (fold x)∂μ :=
  integral_map continuous_fold.measurable.aemeasurable hf.aestronglyMeasurable

theorem integral_symmetrize_fold {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w:Measure Levels.Frequency) (f:Levels.Frequency→E) (hf:Continuous f) :
    ∫x,f (fold x)∂symmetrize w=∫ω,f ω∂w := by
  rw [←integral_folded _ _ hf,fold_symmetrize]

def moment (Θ:Levels.Curve) (μ:Measure Circle) (n:ℤ) : ℝ := ∫x,lag Θ n x∂μ

def cZero (Θ:Levels.Curve) (μ:Measure Circle) : ℝ := ∫x,minimizer Θ x∂μ

@[simp] theorem moment_symmetrize (Θ:Levels.Curve) (w:Measure Levels.Frequency) (n:ℤ) :
    moment Θ (symmetrize w) n=∫ω,Θ.lag n ω∂w :=
  integral_symmetrize_fold w (Θ.lag n) (Θ.continuous_lag n)

@[simp] theorem cZero_symmetrize (Θ:Levels.Curve) (w:Measure Levels.Frequency) :
    cZero Θ (symmetrize w)=∫ω,Θ.minimizer ω∂w :=
  integral_symmetrize_fold w Θ.minimizer Θ.continuous_minimizer

@[simp] theorem moment_folded (Θ:Levels.Curve) (μ:Measure Circle) (n:ℤ) :
    ∫ω,Θ.lag n ω∂folded μ=moment Θ μ n :=
  integral_folded μ (Θ.lag n) (Θ.continuous_lag n)

@[simp] theorem cZero_folded (Θ:Levels.Curve) (μ:Measure Circle) :
    ∫ω,Θ.minimizer ω∂folded μ=cZero Θ μ :=
  integral_folded μ Θ.minimizer Θ.continuous_minimizer

end polyak.Global.Circle
