import polyak.Levels.Realization.Periodic
import polyak.Levels.Program.FiniteAtoms
import polyak.Levels.Program.Carried

/-! From the actual periodic measure program to a genuine Euclidean orbit. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace polyak.Levels
open Dynamics

theorem root_unity_of_mem_periodicGrid {k : ℕ} {ω : Frequency}
    (hω : ω∈periodicGrid k) : Waves.z 0 ω^k=1 := by
  obtain ⟨_,j,hj⟩:=hω
  rw [Waves.z_pow]
  have he : (k:ℂ)*((0:ℂ)+(ω:ℂ)*Complex.I)=(j:ℂ)*(2*Real.pi*Complex.I) := by
    have hh:=congrArg (fun x:ℝ=>(x:ℂ)) hj
    push_cast at hh
    linear_combination hh*Complex.I
  simp only [Complex.ofReal_zero]
  rw [he]
  simpa only [Complex.exp_zero] using Complex.exp_periodic.int_mul_eq j

theorem periodicFP_finite_spectral (q : General.Tuning) {k : ℕ} (hk : 0<k)
    (h : PeriodicFP (tuningCurve q) k) :
    ∃(J : Type)(_:Fintype J)(w:J→NNReal)(a:J→Spectral.Frequency),
      Function.Injective a ∧ (∀j,0<w j) ∧
      ∃hw : ∑j,w j=1,
        Waves.MixtureFeasible (Waves.finiteSpectrum w a hw)
          (Waves.multiplierMap q.A q.B q.beta 0) 0 0 ∧
        (∀j,Waves.z 0 (Real.arccos (a j:ℝ))^k=1) := by
  classical
  obtain ⟨μ,hμ,hS⟩:=h.choose_spec.1.source_probability_carried h.choose_spec.2
  let s:Finset Spectral.Frequency:=(periodicGrid_finite hk).toFinset.image Spectral.cosineCoordinates
  let ν:=Spectral.spectrumCoordinates μ
  have hs : ∀ᵐc ∂(ν:Measure Spectral.Frequency),c∈s := by
    change ∀ᵐc ∂Measure.map Spectral.cosineCoordinates (μ:Measure Frequency),c∈s
    apply (ae_map_iff Spectral.cosineCoordinates.measurable.aemeasurable
      s.finite_toSet.measurableSet).mpr
    filter_upwards [hS] with ω hω
    exact Finset.mem_image.mpr ⟨ω,by simpa using hω,rfl⟩
  obtain ⟨J,inst,w,a,hinj,hpos,ha,hw,he⟩:=probability_finite_atoms ν hs
  refine ⟨J,inst,w,a,hinj,hpos,hw,?_,?_⟩
  · rw [he]
    exact (rawSpectrum_probability_iff q μ).mp hμ
  · intro j
    obtain ⟨ω,hω,he⟩:=Finset.mem_image.mp (ha j)
    have hg : ω∈periodicGrid k:=by simpa using hω
    have hangle : Real.arccos (a j:ℝ)=(ω:ℝ):=by
      rw [←he]
      exact Real.arccos_cos ω.property.1 ω.property.2
    rw [hangle]
    exact root_unity_of_mem_periodicGrid hg

theorem periodicFP_actual_orbit (q : General.Tuning) {k : ℕ} (hk : 0<k)
    (h : PeriodicFP (tuningCurve q) k) :
    ∃r : ℕ,0<r ∧ ∃f : EuclideanSpace ℝ (Fin (2*r+1))→ℝ,
      CenteredSmoothStronglyConvex q.x q.y f ∧
      ∃x₀,x₀≠0 ∧ ∃c₀ : ℝ,0<c₀ ∧
      ∃orbit : ℕ→EuclideanSpace ℝ (Fin (2*r+1)),
        Function.Periodic orbit k ∧
        (∀n,c₀*‖x₀‖≤‖iterate (gradient f) 1 q.beta x₀ n‖) ∧
        Tendsto (fun n=>iterate (gradient f) 1 q.beta x₀ n-orbit n) atTop (𝓝 0) := by
  obtain ⟨J,inst,w,a,_,_,hw,hν,hp⟩:=periodicFP_finite_spectral q hk h
  have hcard : 0<Fintype.card J := by
    apply Fintype.card_pos_iff.mpr
    by_contra hn
    have : IsEmpty J:=not_nonempty_iff.mp hn
    simp at hw
  refine ⟨Fintype.card J,hcard,?_⟩
  apply exists_finite_periodic_orbit q.x_pos q.x_lt_y (by norm_num)
    q.beta_nonneg q.beta_lt_one (by simpa using q.y_lt) w a hw ?_ k hp
  simpa only [q.normalizedA_eq,q.normalizedB_eq] using hν

end polyak.Levels
