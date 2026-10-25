import polyak.FareyPlateau.Ray.SecondContact
import polyak.FareyPlateau.Ray.Regularity
import polyak.FareyPlateau.Ray.EdgeCurvature
import polyak.FareyPlateau.Edge.LatticeCurvature

/-! The exact finite second moment of an arbitrary admissible symbol on
both tight classes. It is the bridge to the sharp curvature comparison. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels ModeLocking Set Filter
open scoped BigOperators Topology Classical

theorem tuningAngle_eq_shifted (q : Tuning) : q.angle=Geometry.shiftedAngle q 0 := by
  funext x
  simp only [Geometry.shiftedAngle,Geometry.shiftRadius,Geometry.shiftNumerator,
    zero_mul,add_zero,Tuning.angle,Tuning.angleRadius]

theorem source_phase_trig_one {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k)
    {n b : ℤ} (hb : (b*j)%k=1) (hn : n%k=b%k) :
    Real.sin ((n:ℝ)*Regions.rationalAngle j k-Real.pi/k)=Real.sin (Real.pi/k) ∧
      Real.cos ((n:ℝ)*Regions.rationalAngle j k-Real.pi/k)=Real.cos (Real.pi/k) := by
  have hh := Edge.lag_trig_reduce hk hjk n (Real.pi/k)
  have ha := source_atom_value hk hjk
  rw [ha,residue_product_one hb hn] at hh
  simp only [Int.cast_one,mul_one] at hh
  have hid : 2*Real.pi/(k:ℝ)-Real.pi/k=Real.pi/k := by ring
  rw [hid] at hh
  exact ⟨hh.2,hh.1⟩

theorem source_phase_trig_zero {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k)
    {n : ℤ} (hn : n%k=0) :
    Real.sin ((n:ℝ)*Regions.rationalAngle j k-Real.pi/k)= -Real.sin (Real.pi/k) ∧
      Real.cos ((n:ℝ)*Regions.rationalAngle j k-Real.pi/k)=Real.cos (Real.pi/k) := by
  have hh := Edge.lag_trig_reduce hk hjk n (Real.pi/k)
  rw [source_atom_value hk hjk,residue_product_zero (j:=j) hn] at hh
  simp only [Int.cast_zero,mul_zero,zero_div,zero_sub,Real.sin_neg,Real.cos_neg] at hh
  exact ⟨hh.2,hh.1⟩

def curvatureMoment {I : Type*} [Fintype I] (n : I→ℤ) (w : I→ℝ) (bar : ℝ) : ℝ :=
  ∑i,w i*(n i:ℝ)*((n i:ℝ)-bar)

theorem SourceCertificate.second_moment {j k : ℕ} {b : ℤ} {D a : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    deriv^[2] (LargeCurvature.indexedSymbol q 0 C.lag C.weight) (Regions.rationalAngle j k)=
      Real.cos (Real.pi/k)*curvatureMoment C.lag C.weight
        (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D)-
      2*Real.sin (Real.pi/k)*deriv^[2] (Geometry.shiftedAngle q 0) (Regions.rationalAngle j k)*
        oneMass k b C.lag C.weight := by
  let ω := Regions.rationalAngle j k
  have hω : ω∈Ioo (0:ℝ) Real.pi := Regions.rationalAngle_mem hj hjk
  have hθ := analyticAt_tuningAngle q hω
  have hphase := source_edge_phase q hj hjk he
  have hslope := source_slope_index q hj hjk he
  have hsum : deriv^[2] (LargeCurvature.indexedSymbol q 0 C.lag C.weight) ω=
      ∑i,C.weight i*deriv^[2] (lagExtension q 0 (C.lag i)) ω := by
    have hh : iteratedDeriv 2 (fun x=>∑i,C.weight i*lagExtension q 0 (C.lag i) x) ω=
        ∑i,iteratedDeriv 2 (fun x=>C.weight i*lagExtension q 0 (C.lag i) x) ω :=
      iteratedDeriv_fun_sum (fun i _=>
      ((analyticAt_const.mul (ModeLocking.analyticAt_lagExtension q 0 (C.lag i)
        ⟨hω.1.le,hω.2.le⟩)).contDiffAt : ContDiffAt ℝ 2 (fun x=>C.weight i*lagExtension q 0 (C.lag i) x) ω))
    change deriv^[2] (fun x=>∑i,C.weight i*lagExtension q 0 (C.lag i) x) ω=_
    simpa only [iteratedDeriv_const_mul_field,iteratedDeriv_eq_iterate] using hh
  have hpoint (i) : deriv^[2] (lagExtension q 0 (C.lag i)) ω=
      Real.cos (Real.pi/k)*(C.lag i:ℝ)*((C.lag i:ℝ)-edgeSlope ω (Real.pi/k) D)-
      (if i∈oneClass k b C.lag then 2*Real.sin (Real.pi/k)*deriv^[2] q.angle ω else 0) := by
    have heq : lagExtension q 0 (C.lag i) =ᶠ[𝓝 ω] Geometry.extendedLag q.angle (C.lag i) := by
      filter_upwards [isOpen_Ioo.mem_nhds hω] with x hx
      rw [lagExtension_actual q 0 (C.lag i) ⟨x,hx.1.le,hx.2.le⟩,Geometry.shiftedCurve_zero]
      rfl
    change deriv (deriv (lagExtension q 0 (C.lag i))) ω=_
    rw [heq.deriv.deriv_eq]
    by_cases hi : i∈oneClass k b C.lag
    · have ho := (Finset.mem_filter.mp hi).2
      have ht := source_phase_trig_one (by omega) hjk.le hb ho
      have hsin : Real.sin ((C.lag i:ℝ)*ω-q.angle ω)=Real.sin (Real.pi/k) := by rw [hphase]; exact ht.1
      have hcos : Real.cos ((C.lag i:ℝ)*ω-q.angle ω)=Real.cos (Real.pi/k) := by rw [hphase]; exact ht.2
      change deriv^[2] (Geometry.extendedLag q.angle (C.lag i)) ω=_
      rw [Edge.lag_second_position_one hθ hphase _ hsin hcos,tuningAngle_eq_shifted q,hslope,
        ite_eq_left hi]
    · have ho : C.lag i%k≠b%k := by simpa [oneClass] using hi
      have hz := (C.admissible.positions i).resolve_left ho
      have ht := source_phase_trig_zero (by omega) hjk.le hz
      have hsin : Real.sin ((C.lag i:ℝ)*ω-q.angle ω)= -Real.sin (Real.pi/k) := by rw [hphase]; exact ht.1
      have hcos : Real.cos ((C.lag i:ℝ)*ω-q.angle ω)=Real.cos (Real.pi/k) := by rw [hphase]; exact ht.2
      change deriv^[2] (Geometry.extendedLag q.angle (C.lag i)) ω=_
      rw [Edge.lag_second_position_zero hθ hphase _ hsin hcos,tuningAngle_eq_shifted q,hslope,
        ite_eq_right hi,sub_zero]
  rw [hsum]
  simp_rw [hpoint]
  unfold curvatureMoment oneMass oneClass
  rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_filter,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [tuningAngle_eq_shifted q]
  by_cases hi : C.lag i%k=b%k <;> simp [hi] <;> ring

end polyak.FareyPlateau.Ray
