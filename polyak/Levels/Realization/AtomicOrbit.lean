import polyak.Levels.Realization.PeriodicProgram
import polyak.Levels.Program.AtomicProgram

/-! The periodic realization with its exact number of positive input weights. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace polyak.Levels
open Dynamics
variable {J : Type*} [Fintype J]

theorem atomic_source_spectrum (q : General.Tuning) (w : J→NNReal) (a : J→Frequency)
    (hw : 0<∑j,w j) (h : ProgramSolution (tuningCurve q) nonzeroLags (atomicMeasure w a)) :
    ∃(v : J→NNReal)(hv : ∑j,v j=1),
      (∀j,v j=0 ↔ w j=0) ∧
      Waves.MixtureFeasible (Waves.finiteSpectrum v (fun j=>Spectral.cosineCoordinates (a j)) hv)
        (Waves.multiplierMap q.A q.B q.beta 0) 0 0 := by
  classical
  let d:J→NNReal:=fun j=>⟨sourceDensity q (a j),(sourceDensity_pos q (a j)).le⟩
  have hd (j:J) : 0<d j:=sourceDensity_pos q (a j)
  let b:J→NNReal:=fun j=>w j/d j
  let Z:NNReal:=∑j,b j
  have hZ : 0<Z := by
    have hex : ∃j,0<w j:=by
      by_contra hn
      push Not at hn
      have hz : ∑j,w j=0:=Finset.sum_eq_zero (fun j _=>le_antisymm (hn j) (show 0≤w j from zero_le))
      exact (ne_of_gt hw) hz
    obtain ⟨j,hj⟩:=hex
    exact lt_of_lt_of_le (div_pos hj (hd j)) (show b j≤∑i,b i from Finset.single_le_sum (fun _ _=>zero_le) (Finset.mem_univ j))
  let v:J→NNReal:=fun j=>b j/Z
  have hv : ∑j,v j=1 := by
    simp only [v,←Finset.sum_div,Z]
    exact div_self (ne_of_gt hZ)
  let μ:ProbabilityMeasure Frequency:=⟨atomicMeasure v a,⟨by
    simp [atomicMeasure,←ENNReal.ofNNReal_finsetSum,hv]⟩⟩
  have hcoef (j:J) : (v j:ℝ)*sourceDensity q (a j)=(1/(Z:ℝ))*(w j:ℝ) := by
    change (((w j:ℝ)/(d j:ℝ))/(Z:ℝ))*sourceDensity q (a j)=_
    have hdR : (d j:ℝ)=sourceDensity q (a j):=rfl
    rw [hdR]
    field_simp [ne_of_gt (sourceDensity_pos q (a j))]
  have hraw : RawSpectrumSolution q (μ:Measure Frequency) := by
    refine ⟨inferInstance,IsProbabilityMeasure.ne_zero _,?_,fun n hn=>?_⟩
    · change 0≤∫ω,sourceG q ω ∂atomicMeasure v a
      rw [atomicMeasure_integral]
      simp_rw [sourceG_polar,←mul_assoc,hcoef,mul_assoc]
      rw [←Finset.mul_sum]
      have hh:=h.2.2.1
      rw [atomicMeasure_integral] at hh
      exact mul_nonneg (by positivity) hh
    · change 0≤∫ω,sourceLag q n ω ∂atomicMeasure v a
      rw [atomicMeasure_integral]
      simp_rw [sourceLag_polar,←mul_assoc,hcoef,mul_assoc]
      rw [←Finset.mul_sum]
      have hh:=h.2.2.2 n hn
      rw [atomicMeasure_integral] at hh
      exact mul_nonneg (by positivity) hh
  have he : Spectral.spectrumCoordinates μ=
      Waves.finiteSpectrum v (fun j=>Spectral.cosineCoordinates (a j)) hv := by
    apply Subtype.ext
    change Measure.map Spectral.cosineCoordinates (atomicMeasure v a)=_
    simp only [atomicMeasure,Waves.finiteSpectrum]
    rw [Measure.map_finset_sum' Spectral.cosineCoordinates.measurable.aemeasurable]
    apply Finset.sum_congr rfl
    intro j _
    rw [Measure.map_smul _ Spectral.cosineCoordinates.measurable.aemeasurable,
      Measure.map_dirac' Spectral.cosineCoordinates.measurable]
  refine ⟨v,hv,?_,?_⟩
  · intro j
    simp only [v,b,div_eq_zero_iff,ne_of_gt hZ,ne_of_gt (hd j),or_false]
  · rw [←he]
    exact (rawSpectrum_probability_iff q μ).mp hraw

/-- A periodic measure with r positive input weights yields dimension 2r+1.
The same coefficients index the literal finite LP and the actual orbit. -/
theorem atomic_periodic_actual_orbit (q : General.Tuning) {k : ℕ} 
    (w : J→NNReal) (a : J→Frequency) (hw : 0<∑j,w j)
    (ha : ∀j,a j∈periodicGrid k)
    (h : ProgramSolution (tuningCurve q) nonzeroLags (atomicMeasure w a)) :
    ∃f : EuclideanSpace ℝ (Fin (2*Fintype.card J+1))→ℝ,
      CenteredSmoothStronglyConvex q.x q.y f ∧
      ∃x₀,x₀≠0 ∧ ∃c₀ : ℝ,0<c₀ ∧
      ∃orbit : ℕ→EuclideanSpace ℝ (Fin (2*Fintype.card J+1)),
        Function.Periodic orbit k ∧
        (∀n,c₀*‖x₀‖≤‖iterate (gradient f) 1 q.beta x₀ n‖) ∧
        Tendsto (fun n=>iterate (gradient f) 1 q.beta x₀ n-orbit n) atTop (𝓝 0) := by
  obtain ⟨v,hv,_,hν⟩:=atomic_source_spectrum q w a hw h
  apply exists_finite_periodic_orbit q.x_pos q.x_lt_y (by norm_num)
    q.beta_nonneg q.beta_lt_one (by simpa using q.y_lt) v (fun j=>Spectral.cosineCoordinates (a j)) hv ?_ k ?_
  · simpa only [q.normalizedA_eq,q.normalizedB_eq] using hν
  · intro j
    change Waves.z 0 (Real.arccos (Real.cos (a j:ℝ)))^k=1
    rw [Real.arccos_cos (a j).property.1 (a j).property.2]
    exact root_unity_of_mem_periodicGrid (ha j)

/-- Zero input weights contribute no dimensions: r is exactly the number of
nonzero weights, represented by its finite subtype. -/
theorem atomic_periodic_orbit_positive_count (q : General.Tuning) {k : ℕ}
    (w : J→NNReal) (a : J→Frequency) (hw : 0<∑j,w j)
    (ha : ∀j,a j∈periodicGrid k)
    (h : ProgramSolution (tuningCurve q) nonzeroLags (atomicMeasure w a)) :
    ∃f : EuclideanSpace ℝ (Fin (2*Fintype.card {j // 0<w j}+1))→ℝ,
      CenteredSmoothStronglyConvex q.x q.y f ∧
      ∃x₀,x₀≠0 ∧ ∃c₀ : ℝ,0<c₀ ∧
      ∃orbit : ℕ→EuclideanSpace ℝ (Fin (2*Fintype.card {j // 0<w j}+1)),
        Function.Periodic orbit k ∧
        (∀n,c₀*‖x₀‖≤‖iterate (gradient f) 1 q.beta x₀ n‖) ∧
        Tendsto (fun n=>iterate (gradient f) 1 q.beta x₀ n-orbit n) atTop (𝓝 0) := by
  classical
  apply atomic_periodic_actual_orbit q (fun j:{j // 0<w j}=>w j.val) (fun j=>a j.val)
    (by simpa only [sum_trim_weights] using hw) (fun j=>ha j.val)
  simpa only [atomicMeasure_trim] using h

end polyak.Levels
