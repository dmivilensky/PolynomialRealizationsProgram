import polyak.FareyPlateau.FanAnalysis.AmbientTests
import polyak.FareyPlateau.FanAnalysis.AllGrid

/-! Continuous families of actual tunings in a single adjacent-lag interval.
The data contain only the source tuning and the arithmetic interval; all
analytic regularity is derived from the ambient coefficient extension. -/
noncomputable section
set_option maxHeartbeats 800000
namespace polyak.FareyPlateau.FanAnalysis.CompactFamily
open General Levels Filter Set
open scoped Topology

structure Data (X : Type*) [TopologicalSpace X] (j k : ℕ) where
  tuning : X → Tuning
  continuous_tuning : Continuous tuning
  adjacent : (x : X) → Edge.AdjacentData (tuning x) j k
  lower : ℤ
  lower_eq : ∀x, (adjacent x).lower=lower

namespace Data
variable {X : Type*} [TopologicalSpace X] {j k : ℕ} (B : Data X j k)

def coordinates (x : X) : Parameters.Point := Parameters.coordinates (B.tuning x)
def shiftError (ε : ℝ) (p : Parameters.Point) : ℝ := Parameters.critical j k B.lower p+ε

theorem continuous_coordinates : Continuous B.coordinates :=
  Parameters.continuous_coordinates.comp B.continuous_tuning

theorem analytic_shiftError (ε : ℝ) (p : Parameters.Point) :
    AnalyticAt ℝ (B.shiftError ε) p :=
  (Parameters.analytic_critical j k B.lower p).add analyticAt_const

theorem critical_actual (x : X) : Parameters.critical j k B.lower (B.coordinates x)=Actual.critical (B.adjacent x) := by
  rw [← B.lower_eq x]
  exact Parameters.critical_actual (B.adjacent x)

theorem correction_actual (x : X) : Parameters.correction j k B.lower (B.coordinates x)=Actual.correction (B.adjacent x) := by
  rw [← B.lower_eq x]
  exact Parameters.correction_actual (B.adjacent x)

theorem shiftError_actual (ε : ℝ) (x : X) : B.shiftError ε (B.coordinates x)=Actual.critical (B.adjacent x)+ε := by
  unfold shiftError
  rw [critical_actual]

def angle (ε h : ℝ) (x : X) (δ : ℝ) : ℝ :=
  Parameters.phase j k (B.coordinates x) (B.shiftError ε (B.coordinates x)) h δ

theorem angle_actual (ε h : ℝ) (x : X) (δ : ℝ) :
    B.angle ε h x δ=anglePath (B.tuning x) (B.adjacent x).edgeShift
      (B.adjacent x).frequency h (Actual.critical (B.adjacent x)+ε) δ := by
  unfold angle
  rw [shiftError_actual]
  exact Parameters.phase_actual (B.adjacent x) _ _ _

theorem angle_continuousAt (ε h : ℝ) (x : X) (δ : ℝ)
    (hs : Real.sin (Parameters.omega j k+h*δ)≠0) :
    ContinuousAt (fun p : X×ℝ => B.angle ε h p.1 p.2) (x,δ) := by
  let F : Parameters.Point×ℝ→ℝ := fun z=>
    Parameters.phase j k z.1 (B.shiftError ε z.1) h z.2
  let g : X×ℝ→Parameters.Point×ℝ := fun z=>(B.coordinates z.1,z.2)
  have hg : Continuous g :=
    (B.continuous_coordinates.comp continuous_fst).prodMk continuous_snd
  have he : Continuous (B.shiftError ε) := continuous_iff_continuousAt.mpr
    (fun p => (B.analytic_shiftError ε p).continuousAt)
  have hF : ContinuousAt F (g (x,δ)) :=
    Parameters.continuousAt_phase he h (B.coordinates x,δ) hs
  have hcomp : ContinuousAt (F ∘ g) (x,δ) := hF.comp hg.continuousAt
  have hfun : (fun p : X×ℝ=>B.angle ε h p.1 p.2)=F ∘ g := by
    funext z
    rfl
  rw [hfun]
  exact hcomp

theorem zero_angle (ε h : ℝ) (x : X) : B.angle ε h x 0=Real.pi/k := by
  rw [angle_actual,anglePath_value _ _ _ _ _ (Actual.frequency_interior (B.adjacent x))]
  exact Edge.phase_at_shift _ (B.adjacent x).period_ge (Actual.frequency_interior (B.adjacent x))

def correction (x : X) : ℝ := Parameters.correction j k B.lower (B.coordinates x)

theorem continuous_correction : Continuous B.correction := by
  exact (continuous_iff_continuousAt.mpr (fun p => (Parameters.analytic_correction j k B.lower p).continuousAt)).comp
    B.continuous_coordinates

def phi (ε : ℝ) (x : X) (δ θ : ℝ) : ℝ :=
  constraint ((k : ℝ)-1) (B.correction x) (B.angle ε 1 x) (B.angle ε (-((k : ℝ)-1)) x) δ θ

theorem phi_actual (ε : ℝ) (x : X) (δ θ : ℝ) :
    B.phi ε x δ θ=Actual.phi (B.adjacent x) (Actual.critical (B.adjacent x)+ε) δ θ := by
  have hn : B.angle ε 1 x=Actual.nearAngle (B.adjacent x) (Actual.critical (B.adjacent x)+ε) :=
    funext (fun d => B.angle_actual ε 1 x d)
  have hc : B.angle ε (-((k : ℝ)-1)) x=Actual.farAngle (B.adjacent x) (Actual.critical (B.adjacent x)+ε) :=
    funext (fun d => B.angle_actual ε (-((k : ℝ)-1)) x d)
  unfold phi Actual.phi correction
  rw [correction_actual]
  rw [hn,hc]

theorem phi_ambient (ε τ y δ : ℝ) (x : X) :
    Parameters.test j k B.lower (B.shiftError ε) τ y (B.coordinates x,δ)=B.phi ε x δ (τ+y*δ) := rfl

theorem phi_continuousAt (ε : ℝ) (x : X) (δ θ : ℝ)
    (ha : Real.sin (Parameters.omega j k+δ)≠0)
    (hc : Real.sin (Parameters.omega j k-((k : ℝ)-1)*δ)≠0) :
    ContinuousAt (fun p : ℝ×(X×ℝ) => B.phi ε p.2.1 p.1 p.2.2) (δ,(x,θ)) := by
  have hnear := (B.angle_continuousAt ε 1 x δ (by simpa only [one_mul] using ha)).comp
    (f := fun p : ℝ×(X×ℝ) => (p.2.1,p.1))
    (show ContinuousAt (fun p : ℝ×(X×ℝ) => (p.2.1,p.1)) (δ,(x,θ)) by fun_prop)
  have hfar := (B.angle_continuousAt ε (-((k : ℝ)-1)) x δ (by convert hc using 1; congr 1; ring)).comp
    (f := fun p : ℝ×(X×ℝ) => (p.2.1,p.1))
    (show ContinuousAt (fun p : ℝ×(X×ℝ) => (p.2.1,p.1)) (δ,(x,θ)) by fun_prop)
  have hz : ContinuousAt (fun p : ℝ×(X×ℝ) => B.correction p.2.1) (δ,(x,θ)) := by
    exact (B.continuous_correction.comp (continuous_fst.comp continuous_snd)).continuousAt
  unfold phi constraint
  exact (((continuousAt_const.add (hz.mul continuous_fst.continuousAt)).mul
    ((Real.continuous_cos.continuousAt.comp hnear).sub
      (Real.continuous_cos.continuousAt.comp ((continuous_snd.comp continuous_snd).continuousAt.sub hnear)))).add
    (Real.continuous_cos.continuousAt.comp hfar)).sub
    (Real.continuous_cos.continuousAt.comp
      ((continuousAt_const.mul (continuous_snd.comp continuous_snd).continuousAt).add hfar))

end Data
end polyak.FareyPlateau.FanAnalysis.CompactFamily
