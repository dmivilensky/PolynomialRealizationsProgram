import polyak.FareyPlateau.Ray.SourceCurvature
import polyak.FareyPlateau.Plateau.SingletonCharacterization
import polyak.FareyPlateau.FanAnalysis.Advantage
import polyak.GapEdges.Junction.Consequence

/-! The lower explicit curve is a genuine divergence obstruction: below
a₂ the actual fine Farey fans improve on the source singleton shift. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Set Filter
open scoped Topology

theorem source_edge_shift_zero {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k)
    (q : Tuning) {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    Edge.shift q k (Edge.atom j k (by omega) hjk.le)=0 := by
  rw [Ray.source_atom_value,Edge.shift,Geometry.cotangent,
    ←q.cot_angle (Regions.rationalAngle_mem hj hjk),source_edge_phase q hj hjk he,sub_self]

theorem source_phase_derivative {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k)
    (q : Tuning) {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    2*deriv (TwoLag.phase q (Edge.shift q k (Edge.atom j k (by omega) hjk.le)))
      (Edge.atom j k (by omega) hjk.le:ℝ)=
        Ray.edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D := by
  rw [source_edge_shift_zero hj hjk q he,Ray.source_atom_value]
  have hh : TwoLag.phase q 0 =ᶠ[𝓝 (Regions.rationalAngle j k)] Geometry.shiftedAngle q 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (Regions.rationalAngle_mem hj hjk)] with x hx
    exact Geometry.jointAngle_actual q 0 ⟨hx.1.le,hx.2.le⟩
  rw [hh.deriv_eq]
  exact Ray.source_slope_index q hj hjk he

def sourceAdjacentData {K j k : ℕ} (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (q : Tuning) {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D)
    (hres : ∀m : ℤ,Ray.edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k) :
    Edge.AdjacentData q j k where
  period_ge := by have := Chart.fraction_window_arithmetic hK hf;omega
  numerator_pos := by have := Chart.fraction_window_arithmetic hK hf;omega
  numerator_lt := (Chart.fraction_window_arithmetic hK hf).2
  inverse := b
  inverse_pos := hb0
  inverse_lt := hbk
  inverse_mod := hb
  lower := Ray.lowerLag k b (Ray.edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D)
  lower_class := by rw [Ray.lowerLag_class,Int.emod_eq_of_lt hb0.le hbk]
  mix := Ray.edgeFraction k b (Ray.edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D)
  mix_pos := (Ray.floor_adjacent hf.1 b _ hres).1
  mix_lt := (Ray.floor_adjacent hf.1 b _ hres).2.1
  slope := (source_phase_derivative (by have := Chart.fraction_window_arithmetic hK hf;omega)
    (Chart.fraction_window_arithmetic hK hf).2 q he).trans
      (Ray.floor_adjacent hf.1 b _ hres).2.2

theorem sourceAdjacentData_shift {K j k : ℕ} (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (q : Tuning) {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D)
    (hres : ∀m : ℤ,Ray.edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k) :
    (sourceAdjacentData hK hf b hb0 hbk hb q he hres).edgeShift=0 :=
  source_edge_shift_zero (by have := Chart.fraction_window_arithmetic hK hf;omega)
    (Chart.fraction_window_arithmetic hK hf).2 q he

theorem sourceAdjacentData_curvature {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) (q : Tuning) {a D : ℝ}
    (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D)
    (hres : ∀m : ℤ,Ray.edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k) :
    deriv^[2] (sourceAdjacentData hK hf b hb0 hbk hb q he hres).function
      (sourceAdjacentData hK hf b hb0 hbk hb q he hres).frequency=
        2*Real.sin (Regions.rationalAngle j k)*(Real.sin (Real.pi/k))^3*(a-Ray.a2 j k b D) := by
  let A := sourceAdjacentData hK hf b hb0 hbk hb q he hres
  have hs : A.edgeShift=0 := sourceAdjacentData_shift hK hf b hb0 hbk hb q he hres
  have hj : 1≤j := by have := Chart.fraction_window_arithmetic hK hf;omega
  have hjk := (Chart.fraction_window_arithmetic hK hf).2
  have hω := Regions.rationalAngle_mem hj hjk
  have hh : TwoLag.phase q 0 =ᶠ[𝓝 (Regions.rationalAngle j k)] Geometry.shiftedAngle q 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hω] with x hx
    exact Geometry.jointAngle_actual q 0 ⟨hx.1.le,hx.2.le⟩
  have hd := hh.iteratedDeriv_eq 2
  simp only [iteratedDeriv_eq_iterate] at hd
  change deriv^[2] A.function A.frequency=_
  rw [A.second,show (A.frequency:ℝ)=Regions.rationalAngle j k from Ray.source_atom_value _ _,hs,hd]
  have hkR : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hγ : Real.pi/k∈Ioo (0:ℝ) Real.pi :=
    ⟨by positivity,div_lt_self Real.pi_pos hkR⟩
  exact Ray.edge_curvature_a2 q hω hγ he (source_edge_phase q hj hjk he)

theorem subcritical_source_interior {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) (q : Tuning) {a D : ℝ}
    (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D)
    (hres : ∀m : ℤ,Ray.edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k)
    (ha : a<Ray.a2 j k b D) : Threshold.sigma q<0 ∧ q∈interior Regions.divergenceSet := by
  let A := sourceAdjacentData hK hf b hb0 hbk hb q he hres
  have hcurv : deriv^[2] A.function A.frequency<0 := by
    rw [sourceAdjacentData_curvature hK hf b hb0 hbk hb q he hres]
    have hω := Regions.rationalAngle_mem
      (show 1≤j by have := Chart.fraction_window_arithmetic hK hf;omega)
      (Chart.fraction_window_arithmetic hK hf).2
    have hkR : (1:ℝ)<k := by exact_mod_cast (show 1<k by have := Chart.fraction_window_arithmetic hK hf;omega)
    have hγ : 0<Real.sin (Real.pi/k) := Real.sin_pos_of_pos_of_lt_pi
      (by positivity) (div_lt_self Real.pi_pos hkR)
    exact mul_neg_of_pos_of_neg (by positivity [Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2])
      (sub_neg.mpr ha)
  have hs : Threshold.sigma q<0 := by
    have hh := FanAnalysis.Actual.negative_curvature_advantage A hcurv
    rwa [sourceAdjacentData_shift hK hf b hb0 hbk hb q he hres] at hh
  exact ⟨hs,GapEdges.Junction.sigma_negative_interior hs⟩

end polyak.FareyPlateau
