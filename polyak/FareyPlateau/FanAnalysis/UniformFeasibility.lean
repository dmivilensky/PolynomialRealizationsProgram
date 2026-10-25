import polyak.FareyPlateau.FanAnalysis.UniformAllGrid
import polyak.FareyPlateau.FanAnalysis.CompactFinite
import polyak.FareyPlateau.FanAnalysis.Cutoff

/-! One constructive order cutoff on a compact tuning family. The actual
near mass is positive and equals k-1+z(q)delta before NNReal conversion. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.CompactFamily.Data
open General Levels ModeLocking Filter MeasureTheory Set
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
variable {j k : ℕ} (B : CompactFamily.Data X j k)

theorem uniform_fan_feasible_small {η : ℝ} (hη : 0<η) :
    ∀ᶠ δ in 𝓝[≠] 0, ∀x : X, ∀P : Fan.Data, P.j=j → P.k=k → P.delta=δ →
      0<(k : ℝ)-1+B.correction x*δ ∧
      ∃a c : Frequency, (a : ℝ)=P.near ∧ (c : ℝ)=P.far ∧
        ProgramSolution (Geometry.shiftedCurve (B.tuning x)
          ((B.adjacent x).edgeShift-(Actual.critical (B.adjacent x)-η)*δ^2)) nonzeroLags
          (atomicMeasure ![Real.toNNReal ((k : ℝ)-1+B.correction x*δ),1] ![a,c]) := by
  have hgrid := B.uniform_all_grid_nonnegative (-η) (B.uniform_core_tests hη)
    (B.uniform_outer_tests (-η)) (B.uniform_zero_neighbors (-η))
  filter_upwards [hgrid,
    (B.uniform_mass_and_minimizer (-η)).filter_mono nhdsWithin_le_nhds,
    (B.uniform_frequencies 1).filter_mono nhdsWithin_le_nhds,
    (B.uniform_frequencies (-((k : ℝ)-1))).filter_mono nhdsWithin_le_nhds,
    (B.uniform_angle_actual (-η) 1).filter_mono nhdsWithin_le_nhds,
    (B.uniform_angle_actual (-η) (-((k : ℝ)-1))).filter_mono nhdsWithin_le_nhds]
    with δ hgrid hmass hnear hfar hanglea hanglec x P hj hk hδ
  let A := B.adjacent x
  let e := Actual.critical A-η
  have hcenter : P.center=(A.frequency : ℝ) := by
    change 2*Real.pi*P.j/P.k=2*Real.pi*j/k
    rw [hj,hk]
    push_cast
    rfl
  have hne : P.near=(A.frequency : ℝ)+δ := by
    have hh := P.near_displacement
    rw [hcenter,hδ] at hh
    linarith
  have hfa : P.far=(A.frequency : ℝ)+(-((k : ℝ)-1))*δ := by
    have hh := P.far_displacement
    rw [hcenter,hk,hδ] at hh
    push_cast at hh
    linarith
  have hN := hnear x
  have hF := hfar x
  simp only [one_mul] at hN
  let a : Frequency := ⟨P.near,by rw [hne]; exact ⟨hN.1.le,hN.2.le⟩⟩
  let c : Frequency := ⟨P.far,by rw [hfa]; exact ⟨hF.1.le,hF.2.le⟩⟩
  let w : Fin 2 → NNReal := ![Real.toNNReal ((k : ℝ)-1+B.correction x*δ),1]
  let ω : Fin 2 → Frequency := ![a,c]
  have hw : (Real.toNNReal ((k : ℝ)-1+B.correction x*δ) : ℝ)=(k : ℝ)-1+B.correction x*δ :=
    Real.coe_toNNReal _ (hmass x).1.le
  have hca : Geometry.shiftedCurve (B.tuning x) (A.edgeShift-e*δ^2) a=B.angle (-η) 1 x δ := by
    change Geometry.shiftedAngle (B.tuning x) _ P.near=_
    rw [hne]
    simpa only [A,e,one_mul,sub_eq_add_neg] using (hanglea x).symm
  have hcc : Geometry.shiftedCurve (B.tuning x) (A.edgeShift-e*δ^2) c=B.angle (-η) (-((k : ℝ)-1)) x δ := by
    change Geometry.shiftedAngle (B.tuning x) _ P.far=_
    rw [hfa]
    simpa only [A,e,sub_eq_add_neg] using (hanglec x).symm
  have hgridA : ∀θ∈Icc (-Real.pi) Real.pi,
      (∃n : ℤ,θ=(n : ℝ)*k*δ) →
      (∃n : ℤ,θ=2*Real.pi/k+((A.lower : ℝ)+(n : ℝ)*k)*δ) →
      0≤Actual.phi A e δ θ := by
    intro θ hθ h0 h1
    have hh := hgrid x θ hθ h0 (by simpa only [A,B.lower_eq x] using h1)
    rw [B.phi_actual] at hh
    simpa only [A,e,sub_eq_add_neg] using hh
  dsimp only [A,e] at hca hcc
  refine ⟨(hmass x).1,a,c,rfl,rfl,inferInstance,atomicMeasure_ne_zero w ω ?_,?_,?_⟩
  · simp only [w,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    positivity
  · rw [atomicMeasure_integral]
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,hw,
      NNReal.coe_one,one_mul,Curve.minimizer,hca,hcc]
    exact (hmass x).2.le
  · intro n _
    rw [atomicMeasure_integral]
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,hw,
      NNReal.coe_one,one_mul,Curve.lag,hca,hcc]
    rw [show B.angle (-η) 1 x δ=Actual.nearAngle A e δ from B.angle_actual (-η) 1 x δ,
      show B.angle (-η) (-((k : ℝ)-1)) x δ=Actual.farAngle A e δ from B.angle_actual (-η) (-((k : ℝ)-1)) x δ]
    change 0≤((k : ℝ)-1+B.correction x*δ)*
      (Real.cos (Actual.nearAngle A e δ)-Real.cos ((n : ℝ)*P.near-Actual.nearAngle A e δ))+
      (Real.cos (Actual.farAngle A e δ)-Real.cos ((n : ℝ)*P.far-Actual.farAngle A e δ))
    rw [companion_cosine P n (Actual.farAngle A e δ),hk]
    push_cast
    rw [show B.correction x=Actual.correction A from B.correction_actual x]
    have hh := Actual.phase_constraints A P hj hk hδ hgridA n
    simpa only [Actual.phi,constraint,add_sub_assoc] using hh

theorem uniform_fan_feasible {η : ℝ} (hη : 0<η) :
    ∃L₀ : ℕ, ∀x : X, ∀P : Fan.Data, P.j=j → P.k=k → (L₀ : ℤ)≤P.L →
      0<(k : ℝ)-1+B.correction x*P.delta ∧
      ∃a c : Frequency, (a : ℝ)=P.near ∧ (c : ℝ)=P.far ∧
        ProgramSolution (Geometry.shiftedCurve (B.tuning x)
          ((B.adjacent x).edgeShift-(Actual.critical (B.adjacent x)-η)*P.delta^2)) nonzeroLags
          (atomicMeasure ![Real.toNNReal ((k : ℝ)-1+B.correction x*P.delta),1] ![a,c]) := by
  have hk : 3≤k := (B.adjacent (Classical.choice (inferInstance : Nonempty X))).period_ge
  obtain ⟨L₀,hL₀⟩ := large_order_small_delta hk (B.uniform_fan_feasible_small hη)
  exact ⟨L₀,fun x P hj hk hPL => hL₀ P hk hPL x P hj hk rfl⟩

end polyak.FareyPlateau.FanAnalysis.CompactFamily.Data
