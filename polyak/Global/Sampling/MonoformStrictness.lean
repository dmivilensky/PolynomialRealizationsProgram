import polyak.Levels.Threshold.MonoformMonotonicity
import polyak.Levels.Program.Grid

/-! A genuinely nonperiodic monotone-form measure has a positive defect
at every nonzero signed lag. A strict profile increase therefore makes
all lag moments and the minimizer moment strictly positive. -/
noncomputable section
namespace polyak.Global.Sampling
open Levels Levels.Threshold MeasureTheory Set Filter

 def Nonperiodic (ν : Measure Frequency) : Prop :=
  ∀k : ℕ,3≤k→¬(∀ᵐω∂ν,ω∈periodicGrid k)

def gridDefect (n : ℤ) (ω : Frequency) : ℝ := 1-Real.cos ((n:ℝ)*(ω:ℝ))

theorem gridDefect_nonneg (n : ℤ) (ω : Frequency) : 0≤gridDefect n ω :=
  sub_nonneg.mpr (Real.cos_le_one _)

theorem integrable_gridDefect (n : ℤ) (ν : Measure Frequency) [IsFiniteMeasure ν] :
    Integrable (gridDefect n) ν :=
  (show Continuous (gridDefect n) by unfold gridDefect;fun_prop).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem grid_of_zero_defect {n : ℤ} (_hn : n≠0) {ω : Frequency} (hω : 0<(ω:ℝ))
    (hz : gridDefect n ω=0) : ω∈periodicGrid (3*n.natAbs) := by
  have hc : Real.cos ((n:ℝ)*(ω:ℝ))=1 := by unfold gridDefect at hz;linarith
  obtain ⟨j,hj⟩ := (Real.cos_eq_one_iff _).mp hc
  have habs : (n.natAbs:ℝ)=|(n:ℝ)| := by simp only [Nat.cast_natAbs,Int.cast_abs]
  refine ⟨hω,?_⟩
  by_cases hnon : 0≤(n:ℝ)
  · refine ⟨3*j,?_⟩
    push_cast
    rw [habs,abs_of_nonneg hnon]
    nlinarith [hj]
  · refine ⟨-3*j,?_⟩
    push_cast
    rw [habs,abs_of_neg (lt_of_not_ge hnon)]
    nlinarith [hj]

theorem nonperiodic_defect_pos {ν : Measure Frequency} [IsFiniteMeasure ν]
    (hcar : ∀ᵐω∂ν,ω∈interiorCarrier) (hν : Nonperiodic ν)
    (n : ℤ) (hn : n≠0) : 0<∫ω,gridDefect n ω∂ν := by
  by_contra hh
  have hzero : (∫ω,gridDefect n ω∂ν)=0 :=
    le_antisymm (le_of_not_gt hh) (integral_nonneg (gridDefect_nonneg n))
  have hae := (integral_eq_zero_iff_of_nonneg (gridDefect_nonneg n)
    (integrable_gridDefect n ν)).mp hzero
  apply hν (3*n.natAbs) (by
    have hp : 0<n.natAbs := Int.natAbs_pos.mpr hn
    omega)
  filter_upwards [hcar,hae] with ω hω hz
  exact grid_of_zero_defect hn hω.1 hz

theorem strict_monoform_increase {h h' : Frequency→ℝ} {ν : Measure Frequency}
    (hν : MonotoneSolution h ν) (hNP : Nonperiodic ν)
    (hm' : AEStronglyMeasurable h' ν) {e H : ℝ} (he : 0<e)
    (horder : ∀ᵐω∂ν,h ω+e≤h' ω) (hupper : ∀ᵐω∂ν,h' ω≤H) :
    MonotoneSolution h' ν ∧ (0<∫ω,h' ω∂ν) ∧
      ∀n : ℤ,n≠0→0<∫ω,monotoneLag h' n ω∂ν := by
  let : IsFiniteMeasure ν := hν.1
  let : NeZero ν := ⟨hν.2.1⟩
  have hord : ∀ᵐω∂ν,h ω≤h' ω := horder.mono (fun _ hh=>by linarith)
  obtain ⟨hν',hid⟩ := hν.mono_ae hm' hord hupper
  have hi := hν.2.2.2.1
  have hi' := hν'.2.2.2.1
  refine ⟨hν',?_,?_⟩
  · have hh := integral_mono_ae (hi.add (integrable_const e)) hi' horder
    change (∫ω,h ω+e∂ν)≤(∫ω,h' ω∂ν) at hh
    rw [integral_add hi (integrable_const e),integral_const,smul_eq_mul] at hh
    have hp : 0<ν.real univ := measureReal_univ_pos
    nlinarith [hν.2.2.2.2.1]
  · intro n hn
    have hd : Integrable (fun ω=>(h' ω-h ω)*gridDefect n ω) ν := by
      have heq : (fun ω=>(h' ω-h ω)*gridDefect n ω)=
          fun ω=>monotoneLag h' n ω-monotoneLag h n ω := by
        funext ω
        unfold monotoneLag gridDefect
        ring
      rw [heq]
      exact (integrable_monotoneLag hi' n).sub (integrable_monotoneLag hi n)
    have hb := integral_mono_ae ((integrable_gridDefect n ν).const_mul e) hd
      (horder.mono fun ω hω=>mul_le_mul_of_nonneg_right (by linarith : e≤h' ω-h ω)
        (gridDefect_nonneg n ω))
    rw [integral_const_mul] at hb
    have hpos := nonperiodic_defect_pos hν.2.2.1 hNP n hn
    have heq := hid n
    change (∫ω,monotoneLag h' n ω∂ν)=(∫ω,monotoneLag h n ω∂ν)+
      ∫ω,(h' ω-h ω)*gridDefect n ω∂ν at heq
    nlinarith [hν.2.2.2.2.2 n hn]

end polyak.Global.Sampling
