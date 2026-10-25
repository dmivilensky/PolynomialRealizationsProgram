import polyak.FareyPlateau.FanAnalysis.MassLimit
import polyak.FareyPlateau.FanAnalysis.Advantage
import polyak.FareyPlateau.FanAnalysis.CarriedPair

/-! Source-facing positivity of the constructive masses, and the mass
fraction limit for arbitrary actual finite measures on the shrinking pair. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels ModeLocking MeasureTheory Set Filter
open scoped Topology

theorem pair_total_toReal {μ : Measure Frequency} [IsFiniteMeasure μ] {a c : Frequency}
    (hne : a≠c) (hcar : ∀ᵐ x ∂μ,x=a ∨ x=c) :
    (μ univ).toReal=(pairWeight μ a c 0:ℝ)+(pairWeight μ a c 1:ℝ) := by
  calc
    _ = ((atomicMeasure (pairWeight μ a c) (pairFrequencies a c)) univ).toReal :=
      congrArg (fun ν:Measure Frequency=>(ν univ).toReal) (carried_pair_eq hne hcar)
    _ = _ := by simp only [atomicMeasure,Fin.sum_univ_two,Measure.add_apply,
    Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ _),smul_eq_mul,mul_one,
    ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top,ENNReal.coe_toReal]

theorem pair_frequency_ne (P : Fan.Data) {a c : Frequency}
    (ha : (a:ℝ)=P.near) (hc : (c:ℝ)=P.far) : a≠c := by
  intro he
  have hh := congrArg (fun x:Frequency=>(x:ℝ)) he
  rw [ha,hc] at hh
  have h₁ := P.near_displacement
  have h₂ := P.far_displacement
  have hk : (0:ℝ)<P.k := by exact_mod_cast (show 0<P.k by have := P.period_ge; omega)
  have hp : (P.k:ℝ)*P.delta=0 := by nlinarith
  exact delta_ne_zero P ((mul_eq_zero.mp hp).resolve_left hk.ne')

namespace Actual
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem fan_feasible_positive_mass {e : ℝ} (he : e<critical A) :
    ∃z : ℝ,∃L₀ : ℕ,∀P : Fan.Data,P.j=j → P.k=k → (L₀:ℤ)≤P.L →
      0<(k:ℝ)-1+z*P.delta ∧
      (Real.toNNReal ((k:ℝ)-1+z*P.delta):ℝ)=(k:ℝ)-1+z*P.delta ∧
      ∃a c : Frequency,(a:ℝ)=P.near ∧ (c:ℝ)=P.far ∧
        ProgramSolution (Geometry.shiftedCurve q (A.edgeShift-e*P.delta^2)) nonzeroLags
          (atomicMeasure ![Real.toNNReal ((k:ℝ)-1+z*P.delta),1] ![a,c]) := by
  have hkR : (3:ℝ)≤k := by exact_mod_cast A.period_ge
  have hm : ∀ᶠ δ:ℝ in 𝓝 0,0<(k:ℝ)-1+correction A*δ :=
    (show ContinuousAt (fun δ:ℝ=>(k:ℝ)-1+correction A*δ) 0 by fun_prop).eventually
      (eventually_gt_nhds (by simpa only [mul_zero,add_zero] using (show 0<(k:ℝ)-1 by linarith)))
  obtain ⟨L₀,hL₀⟩ := large_order_small_delta A.period_ge
    ((hm.filter_mono nhdsWithin_le_nhds).and (fan_feasible_small A he))
  refine ⟨correction A,L₀,fun P hj hk hPL=>?_⟩
  have hh := hL₀ P hk hPL
  exact ⟨hh.1,Real.coe_toNNReal _ hh.1.le,hh.2 P hj hk rfl⟩

theorem arbitrary_carried_mass_fraction {X : Type*} {l : Filter X}
    (P : X→Fan.Data) (a c : X→Frequency) (μ : X→Measure Frequency) (e : ℝ)
    (hδ : Tendsto (fun x=>(P x).delta) l (𝓝[≠] 0))
    (hlabels : ∀ᶠ x in l,(P x).j=j ∧ (P x).k=k ∧
      (a x:ℝ)=(P x).near ∧ (c x:ℝ)=(P x).far)
    (hprog : ∀ᶠ x in l,ProgramSolution
      (Geometry.shiftedCurve q (A.edgeShift-e*(P x).delta^2)) nonzeroLags (μ x))
    (hcar : ∀ᶠ x in l,∀ᵐ ω ∂μ x,ω=a x ∨ ω=c x) :
    Tendsto (fun x=>((μ x) {a x}).toReal/((μ x) univ).toReal) l (𝓝 (((k:ℝ)-1)/k)) := by
  let u := fun x=>(pairWeight (μ x) (a x) (c x) 0:ℝ)
  let v := fun x=>(pairWeight (μ x) (a x) (c x) 1:ℝ)
  let wa := fun x=>u x/(u x+v x)
  let wc := fun x=>v x/(u x+v x)
  have hsum : ∀ᶠ x in l,0<u x+v x := by
    filter_upwards [hlabels,hprog,hcar] with x hx hp hc
    let : IsFiniteMeasure (μ x) := hp.1
    have hh := pairWeight_sum_pos (pair_frequency_ne (P x) hx.2.2.1 hx.2.2.2) hc hp.2.1
    simp only [Fin.sum_univ_two] at hh
    exact_mod_cast hh
  have hw : ∀ᶠ x in l,0≤wa x ∧ 0≤wc x ∧ wa x+wc x=1 := by
    filter_upwards [hsum] with x hx
    refine ⟨div_nonneg (NNReal.coe_nonneg _) hx.le,div_nonneg (NNReal.coe_nonneg _) hx.le,?_⟩
    dsimp [wa,wc]
    rw [←add_div,div_self hx.ne']
  have hnear := hδ.eventually ((anglePath_actual q A.edgeShift A.frequency 1 e (frequency_interior A)).filter_mono nhdsWithin_le_nhds)
  have hfar := hδ.eventually ((anglePath_actual q A.edgeShift A.frequency (-((k:ℝ)-1)) e (frequency_interior A)).filter_mono nhdsWithin_le_nhds)
  have hfeas : ∀ᶠ x in l,∃Q : Fan.Data,Q.k=k ∧ Q.delta=(P x).delta ∧
      ∀n : ℤ,0≤pairLag A Q e (P x).delta (wa x) (wc x) n := by
    filter_upwards [hlabels,hprog,hcar,hsum,hnear,hfar] with x hx hp hc hsumx hna hfa
    have hcenter : (P x).center=(A.frequency:ℝ) := by
      change 2*Real.pi*(P x).j/(P x).k=2*Real.pi*j/k
      rw [hx.1,hx.2.1]
      push_cast
      rfl
    have hnaP : (P x).near=(A.frequency:ℝ)+(P x).delta := by linarith [(P x).near_displacement]
    have hfaP : (P x).far=(A.frequency:ℝ)-((k:ℝ)-1)*(P x).delta := by
      have hh := (P x).far_displacement
      rw [hcenter,hx.2.1] at hh
      simpa only [Int.cast_natCast] using hh
    have hca : Geometry.shiftedCurve q (A.edgeShift-e*(P x).delta^2) (a x)=nearAngle A e (P x).delta := by
      change Geometry.shiftedAngle q _ (a x:ℝ)=_
      rw [hx.2.2.1,hnaP]
      simpa only [one_mul,nearAngle] using hna.symm
    have hcc : Geometry.shiftedCurve q (A.edgeShift-e*(P x).delta^2) (c x)=farAngle A e (P x).delta := by
      change Geometry.shiftedAngle q _ (c x:ℝ)=_
      rw [hx.2.2.2,hfaP]
      change Geometry.shiftedAngle q _ ((A.frequency:ℝ)-((k:ℝ)-1)*(P x).delta)=
        anglePath q A.edgeShift A.frequency (-((k:ℝ)-1)) e (P x).delta
      convert hfa.symm using 1; congr 1; ring
    have hm := pair_solution_inequalities (pair_frequency_ne (P x) hx.2.2.1 hx.2.2.2) hc hp
    refine ⟨P x,hx.2.1,rfl,fun n=>?_⟩
    have hraw : 0≤pairLag A (P x) e (P x).delta (u x) (v x) n := by
      simpa only [Curve.lag,hca,hcc,hx.2.2.1,hx.2.2.2,pairLag] using hm.2.2 n
    have heq : pairLag A (P x) e (P x).delta (wa x) (wc x) n=
        pairLag A (P x) e (P x).delta (u x) (v x) n/(u x+v x) := by
      unfold pairLag wa wc
      ring
    rw [heq]
    exact div_nonneg hraw hsumx.le
  have hlim := fan_mass_fraction A e hδ hw hfeas
  apply hlim.congr'
  filter_upwards [hlabels,hprog,hcar] with x hx hp hc
  let : IsFiniteMeasure (μ x) := hp.1
  have htotal := pair_total_toReal (pair_frequency_ne (P x) hx.2.2.1 hx.2.2.2) hc
  rw [htotal]
  rfl

end Actual
end polyak.FareyPlateau.FanAnalysis
