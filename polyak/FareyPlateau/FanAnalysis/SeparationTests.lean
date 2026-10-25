import polyak.FareyPlateau.FanAnalysis.DualJets
import polyak.FareyPlateau.FanAnalysis.OriginJets
import polyak.FareyPlateau.FanAnalysis.AmbientTests

/-! Four actual finite separating tests with a constant negative quadratic
margin. This form makes necessity uniform on compact tuning families. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels ModeLocking Filter
open scoped Topology
namespace Parameters

def separatingCorrection (j k : ℕ) (n : ℤ) (p : Point) : ℝ :=
  ((k : ℝ)-2)*curvature j k n p/((k : ℝ)*Real.sin (gamma k))

theorem analytic_separatingCorrection (j k : ℕ) (n : ℤ) (p : Point) :
    AnalyticAt ℝ (separatingCorrection j k n) p :=
  (analyticAt_const.mul (analytic_curvature j k n p)).div_const

def originTest (j k : ℕ) (e : Point → ℝ) (h ρ : ℝ) (z : Point×ℝ) : ℝ :=
  lagPath 0 (h*ρ*k) (fun δ => phase j k z.1 (e z.1) h δ) z.2

def separatingTest (j k : ℕ) (n : ℤ) (e : Point → ℝ) (h ρ : ℝ) (z : Point×ℝ) : ℝ :=
  dualTest j k n e h z+ρ*separatingCorrection j k n z.1*z.2*originTest j k e h ρ z

theorem analytic_originTest {j k : ℕ} {e : Point → ℝ} (he : ∀p,AnalyticAt ℝ e p)
    (h ρ : ℝ) (z : Point×ℝ) (hs : Real.sin (omega j k+h*z.2)≠0) :
    AnalyticAt ℝ (originTest j k e h ρ) z := by
  have hp := analytic_phase he h z hs
  unfold originTest lagPath
  simp only [zero_add]
  exact (Real.analyticAt_cos.comp hp).sub
    (Real.analyticAt_cos.comp ((analyticAt_const.mul analyticAt_snd).sub hp))

theorem analytic_separatingTest {j k : ℕ} {n : ℤ} {e : Point → ℝ} (he : ∀p,AnalyticAt ℝ e p)
    (h ρ : ℝ) (z : Point×ℝ) (hs : Real.sin (omega j k+h*z.2)≠0) :
    AnalyticAt ℝ (separatingTest j k n e h ρ) z :=
  (analytic_dualTest he h z hs).add
    (((analyticAt_const.mul ((analytic_separatingCorrection j k n z.1).comp analyticAt_fst)).mul analyticAt_snd).mul
      (analytic_originTest he h ρ z hs))
end Parameters

namespace Actual
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

def separatingCorrection : ℝ := ((k : ℝ)-2)*deriv^[2] A.function A.frequency/((k : ℝ)*Real.sin (Real.pi/k))

def separatingTest (e h ρ δ : ℝ) : ℝ :=
  dualPath A (anglePath q A.edgeShift A.frequency h e) h δ+
    ρ*separatingCorrection A*δ*lagPath 0 (h*ρ*k) (anglePath q A.edgeShift A.frequency h e) δ

theorem path_first (e h : ℝ) : deriv (anglePath q A.edgeShift A.frequency h e) 0=h*first A := by
  rw [anglePath_first q A.edgeShift A.frequency h e (frequency_interior A)]
  unfold first
  ring

theorem path_second (e h : ℝ) : deriv^[2] (anglePath q A.edgeShift A.frequency h e) 0=
    h^2*second A+2*e*(Real.sin (Real.pi/k))^2 := by
  rw [anglePath_second q A.edgeShift A.frequency h e (frequency_interior A),div_eq_mul_inv,←one_div,inverse_radius A]
  unfold second
  ring

theorem path_value (e h : ℝ) : anglePath q A.edgeShift A.frequency h e 0=Real.pi/k := by
  rw [anglePath_value q A.edgeShift A.frequency h e (frequency_interior A)]
  exact Edge.phase_at_shift q A.period_ge (frequency_interior A)

theorem separatingTest_limit (η h ρ : ℝ) (hh : h=1 ∨ h= -((k : ℝ)-1)) (hρ : ρ=1 ∨ ρ= -1) :
    Tendsto (fun δ => separatingTest A (critical A+η) h ρ δ/δ^2) (𝓝[≠] 0)
      (𝓝 (-2*η*(Real.sin (Real.pi/k))^3)) := by
  let e := critical A+η
  have hp := analyticAt_anglePath q A.edgeShift A.frequency h e (frequency_interior A)
  have hd := dualPath_limit A hp (path_value A e h) (path_first A e h) (path_second A e h)
  have ho := linear_limit (analyticAt_lagPath hp 0 (h*ρ*k)) (zero_lag_value (path_value A e h) (h*ρ*k))
  rw [zero_lag_first hp (path_value A e h)] at ho
  have he := hd.add (ho.const_mul (ρ*separatingCorrection A))
  have hfun : (fun δ => separatingTest A e h ρ δ/δ^2)=
      (fun δ => dualPath A (anglePath q A.edgeShift A.frequency h e) h δ/δ^2+
        ρ*separatingCorrection A*(lagPath 0 (h*ρ*k) (anglePath q A.edgeShift A.frequency h e) δ/δ)) := by
    funext δ
    unfold separatingTest
    by_cases hz : δ=0
    · simp only [hz,zero_pow (by norm_num : (2:ℕ)≠0),div_zero,mul_zero,add_zero]
    · field_simp
  rw [←hfun] at he
  have hkz : (k : ℝ)≠0 := by exact_mod_cast (show k≠0 by have := A.period_ge; omega)
  have hsz : Real.sin (Real.pi/k)≠0 := (sin_positive A).ne'
  convert he using 1
  unfold e critical separatingCorrection
  rcases hh with rfl|rfl <;> rcases hρ with rfl|rfl <;> field_simp <;> ring

theorem separatingTest_actual (e : Parameters.Point → ℝ) (h ρ δ : ℝ) :
    Parameters.separatingTest j k A.lower e h ρ (Parameters.coordinates q,δ)=
      separatingTest A (e (Parameters.coordinates q)) h ρ δ := by
  have hx : Parameters.separatingCorrection j k A.lower (Parameters.coordinates q)=separatingCorrection A := by
    unfold Parameters.separatingCorrection separatingCorrection Parameters.gamma
    rw [Parameters.curvature_actual A]
  unfold Parameters.separatingTest separatingTest Parameters.originTest
  rw [Parameters.dualTest_actual A,hx]
  congr 1
  congr 1
  congr 1
  funext d
  exact Parameters.phase_actual A _ _ _

end Actual
end polyak.FareyPlateau.FanAnalysis
