import polyak.GapEdges.Junction.Nonresonance
import polyak.FareyPlateau.FanAnalysis.Advantage

/-! Every amplitude in the explicit nonempty junction interval is truly
divergent, and divergence holds on a whole neighborhood reaching the gap. -/
noncomputable section
namespace polyak.GapEdges.Junction
open General Levels Set

theorem sigma_negative_interior {q : Tuning} (hσ : Threshold.sigma q<0) :
    q∈interior Regions.divergenceSet := by
  have ho : IsOpen {p : Tuning | Threshold.sigma p<0} :=
    isOpen_lt Global.Threshold.continuous_sigma continuous_const
  exact (ho.subset_interior_iff.mpr
    (fun p (hp : Threshold.sigma p<0)=>(divergenceSet_iff_sigma_nonpos p).mpr hp.le)) hσ

theorem source_junction_interval_nonempty (K : ℕ) (hK : 3≤K) :
    (Ioo (junctionLower (Chart.boundaryCosine (K+1)) (Chart.boundaryCosine K))
      (junctionUpper (K+1) (Chart.boundaryCosine (K+1)) (Chart.boundaryCosine K)
        (Real.sin (Real.pi/(K+1))))).Nonempty := by
  apply nonempty_Ioo.mpr
  simpa only [junctionT,Chart.boundaryCosine,Chart.boundaryAngle,Nat.cast_add,
    Nat.cast_one,add_sub_cancel_right] using junction_interval_nonempty (K+1) (by omega)

theorem junction_interval_sigma_negative (q : Tuning) {k : ℕ} (hk : 4≤k) {a t₂ : ℝ}
    (hd : t₂<Real.cos (2*(Real.pi/k)))
    (ha : a∈Ioo (junctionLower (Real.cos (2*(Real.pi/k))) t₂)
      (junctionUpper k (Real.cos (2*(Real.pi/k))) t₂ (Real.sin (Real.pi/k))))
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂) :
    Threshold.sigma q<0 := by
  obtain ⟨A,hF⟩ := junction_interval_adjacent q hk hd ha hXi
  have hs : A.edgeShift=0 := by
    unfold FareyPlateau.Edge.AdjacentData.edgeShift
    rw [adjacent_frequency_one A]
    exact junction_edge_shift q hk hXi
  simpa only [hs] using FareyPlateau.FanAnalysis.Actual.negative_curvature_advantage A hF

theorem junctionTuning_sigma_negative (K : ℕ) (hK : 3≤K) {a : ℝ}
    (ha : a∈Ioo (junctionLower (Chart.boundaryCosine (K+1)) (Chart.boundaryCosine K))
      (junctionUpper (K+1) (Chart.boundaryCosine (K+1)) (Chart.boundaryCosine K)
        (Real.sin (Real.pi/(K+1))))) :
    Threshold.sigma (junctionTuning K hK a (by
      simpa only [Chart.amplitudeFloor,junctionLower,mul_comm] using ha.1))<0 := by
  have horder := Chart.boundaryCosine_lt_succ (show 2≤K by omega)
  apply junction_interval_sigma_negative (k:=K+1) (a:=a) (t₂:=Real.cos (2*Real.pi/K))
    _ (show 4≤K+1 by omega)
  · simpa only [Chart.boundaryCosine,Chart.boundaryAngle,Nat.cast_add,Nat.cast_one,
      show 2*(Real.pi/((K:ℝ)+1))=2*Real.pi/((K:ℝ)+1) by ring] using horder
  · simpa only [Chart.boundaryCosine,Chart.boundaryAngle,Nat.cast_add,Nat.cast_one,
      show 2*(Real.pi/((K:ℝ)+1))=2*Real.pi/((K:ℝ)+1) by ring] using ha
  · simpa only [Nat.cast_add,Nat.cast_one] using junctionTuning_source_coefficients K hK a _

theorem junctionTuning_negative_neighborhood (K : ℕ) (hK : 3≤K) {a : ℝ}
    (ha : a∈Ioo (junctionLower (Chart.boundaryCosine (K+1)) (Chart.boundaryCosine K))
      (junctionUpper (K+1) (Chart.boundaryCosine (K+1)) (Chart.boundaryCosine K)
        (Real.sin (Real.pi/(K+1))))) :
    ∃V : Set Tuning,IsOpen V ∧
      junctionTuning K hK a (by simpa only [Chart.amplitudeFloor,junctionLower,mul_comm] using ha.1)∈V ∧
      V⊆{p | Threshold.sigma p<0} ∧
      (V∩{p | Geometry.Gap K p}).Nonempty := by
  let q := junctionTuning K hK a (by
    simpa only [Chart.amplitudeFloor,junctionLower,mul_comm] using ha.1)
  let V : Set Tuning := {p | Threshold.sigma p<0}
  have hV : IsOpen V := isOpen_lt Global.Threshold.continuous_sigma continuous_const
  have hqV : q∈V := junctionTuning_sigma_negative K hK ha
  have hcl : q∈closure {p : Tuning | Geometry.Gap K p} := junctionTuning_mem_closure K hK a _
  have hne := mem_closure_iff.mp hcl V hV hqV
  exact ⟨V,hV,hqV,Subset.rfl,by simpa only [inter_comm] using hne⟩

theorem junctionTuning_interior_neighborhood (K : ℕ) (hK : 3≤K) {a : ℝ}
    (ha : a∈Ioo (junctionLower (Chart.boundaryCosine (K+1)) (Chart.boundaryCosine K))
      (junctionUpper (K+1) (Chart.boundaryCosine (K+1)) (Chart.boundaryCosine K)
        (Real.sin (Real.pi/(K+1))))) :
    ∃V : Set Tuning,IsOpen V ∧
      junctionTuning K hK a (by simpa only [Chart.amplitudeFloor,junctionLower,mul_comm] using ha.1)∈V ∧
      V⊆interior Regions.divergenceSet ∧
      (V∩{p | Geometry.Gap K p}).Nonempty := by
  obtain ⟨V,hV,hq,hneg,hgap⟩ := junctionTuning_negative_neighborhood K hK ha
  exact ⟨V,hV,hq,fun p hp=>sigma_negative_interior (hneg hp),hgap⟩

end polyak.GapEdges.Junction
