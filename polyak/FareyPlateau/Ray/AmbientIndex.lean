import polyak.FareyPlateau.Ray.Slope
import polyak.FareyPlateau.Edge.Basic
import polyak.ModeLocking.TwoLag.Extension

/-! The literal shift and slope index have real analytic extensions in
the original ambient tuning coordinates, for every admissible tuning. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set Filter
open scoped Topology

def ambientEdgeShift (j k : ℕ) (p : Chart.AmbientPoint) : ℝ :=
  Real.cos (Real.pi/k)/Real.sin (Real.pi/k)-
    Geometry.polyCotangent (Chart.rawToCoefficient p 0) (Chart.rawToCoefficient p 1)
      (Chart.rawToCoefficient p 2) (Regions.rationalAngle j k)

def ambientSlopeIndex (j k : ℕ) (p : Chart.AmbientPoint) : ℝ :=
  -2*(Real.sin (Real.pi/k))^2*
    Geometry.polyCotangentFirst (Chart.rawToCoefficient p 0) (Chart.rawToCoefficient p 1)
      (Chart.rawToCoefficient p 2) (Regions.rationalAngle j k)

theorem analyticAt_edge_indices (q : Tuning) (j k : ℕ) :
    AnalyticAt ℝ (ambientEdgeShift j k) ![q.kappa,q.y,q.beta,0,Regions.rationalAngle j k] ∧
      AnalyticAt ℝ (ambientSlopeIndex j k) ![q.kappa,q.y,q.beta,0,Regions.rationalAngle j k] := by
  let p : Chart.AmbientPoint := ![q.kappa,q.y,q.beta,0,Regions.rationalAngle j k]
  have hraw : AnalyticAt ℝ Chart.rawToCoefficient p := Chart.analyticAt_rawToCoefficient_actual q 0 _
  have h0 := (Chart.analyticAt_coordinate (Chart.rawToCoefficient p) 0).comp hraw
  have h1 := (Chart.analyticAt_coordinate (Chart.rawToCoefficient p) 1).comp hraw
  have h2 := (Chart.analyticAt_coordinate (Chart.rawToCoefficient p) 2).comp hraw
  constructor
  · unfold ambientEdgeShift Geometry.polyCotangent
    exact analyticAt_const.sub (((h0.add (h1.mul analyticAt_const)).add
      (h2.mul analyticAt_const)).div_const)
  · unfold ambientSlopeIndex Geometry.polyCotangentFirst
    exact analyticAt_const.mul (((h1.neg.sub ((h0.add (analyticAt_const.mul h2)).mul
      analyticAt_const)).add (h2.mul analyticAt_const)).div_const)

theorem ambientEdgeShift_actual (q : Tuning) (j k : ℕ) :
    ambientEdgeShift j k ![q.kappa,q.y,q.beta,0,Regions.rationalAngle j k]=
      Edge.shift q k (Regions.rationalAngle j k) := by
  unfold ambientEdgeShift
  rw [Chart.rawToCoefficient_actual,Edge.shift,Geometry.cotangent_eq_poly]
  rfl

theorem slopeIndex_at_shift (q : Tuning) {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k) :
    2*deriv (ModeLocking.TwoLag.phase q (Edge.shift q k (Regions.rationalAngle j k)))
      (Regions.rationalAngle j k)=
        -2*(Real.sin (Real.pi/k))^2*Geometry.cotangentFirst q (Regions.rationalAngle j k) := by
  let ω := Regions.rationalAngle j k
  let s := Edge.shift q k ω
  have hω : ω∈Ioo (0:ℝ) Real.pi := Regions.rationalAngle_mem hj hjk
  have heq : ModeLocking.TwoLag.phase q s =ᶠ[𝓝 ω] Geometry.shiftedAngle q s := by
    filter_upwards [isOpen_Ioo.mem_nhds hω] with x hx
    exact Geometry.jointAngle_actual q s ⟨hx.1.le,hx.2.le⟩
  have hshift : Geometry.cotangent q ω+s=Real.cos (Real.pi/k)/Real.sin (Real.pi/k) := by
    dsimp [s,Edge.shift]
    ring
  rw [heq.deriv_eq,(Geometry.hasDerivAt_shiftedAngle q s hω).deriv,Geometry.shiftedFirst,hshift]
  have hk : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hs := Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith : (0:ℝ)<k))
    (div_lt_self Real.pi_pos hk)
  have hid : 1+(Real.cos (Real.pi/k)/Real.sin (Real.pi/k))^2=1/(Real.sin (Real.pi/k))^2 := by
    field_simp [hs.ne']
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi/k)]
  rw [hid]
  field_simp
  rfl

theorem ambientSlopeIndex_actual (q : Tuning) {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k) :
    ambientSlopeIndex j k ![q.kappa,q.y,q.beta,0,Regions.rationalAngle j k]=
      2*deriv (ModeLocking.TwoLag.phase q (Edge.shift q k (Regions.rationalAngle j k)))
        (Regions.rationalAngle j k) := by
  rw [slopeIndex_at_shift q hj hjk]
  unfold ambientSlopeIndex
  rw [Chart.rawToCoefficient_actual]
  rfl

end polyak.FareyPlateau.Ray
