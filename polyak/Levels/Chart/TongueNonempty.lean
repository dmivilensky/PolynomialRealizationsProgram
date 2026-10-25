import polyak.Levels.Chart.TongueGraph
import polyak.Levels.Lattice.Atoms
import polyak.General.Regions.Periodic

/-! Every fraction inside a gap has a nonempty, constructively realized
tongue; its specified atom solves the full program and gives an actual orbit. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set MeasureTheory Filter Topology

def tongueWitnessParameters {K j k : ℕ} (hK : 2≤K) (hf : FractionInWindow K j k) :
    GapParameters K := by
  let c := rationalCosine j k
  let r₁ := (boundaryCosine K+c)/2
  let r₂ := (c+boundaryCosine (K+1))/2
  let a := max (amplitudeFloor r₁ r₂) (tongueAmplitude j k r₁ r₂)+1
  have hc := fraction_cosine_window hK hf
  refine ⟨(a,r₁,r₂),?_,?_,?_,?_⟩
  · dsimp [r₁,c]; linarith [hc.1]
  · dsimp [r₁,r₂,c]; linarith [hc.1,hc.2]
  · dsimp [r₂,c]; linarith [hc.2]
  · dsimp [a]; linarith [le_max_left (amplitudeFloor r₁ r₂) (tongueAmplitude j k r₁ r₂)]

def tongueWitness {K j k : ℕ} (hK : 2≤K) (hf : FractionInWindow K j k) : GapTunings K :=
  gapInverse hK (tongueWitnessParameters hK hf)

theorem tongueWitness_phase {K j k : ℕ} (hK : 2≤K) (hf : FractionInWindow K j k) :
    (tongueWitness hK hf).val.angle (Regions.rationalAngle j k)≤Real.pi/k := by
  apply (gap_tongue_graph hK hf (tongueWitness hK hf)).mpr
  rw [show coordinates (tongueWitness hK hf).val=(tongueWitnessParameters hK hf).val from
    coordinates_gapInverse hK _]
  have hc := fraction_cosine_window hK hf
  change (boundaryCosine K+rationalCosine j k)/2<rationalCosine j k ∧
    rationalCosine j k<(rationalCosine j k+boundaryCosine (K+1))/2 ∧ _
  refine ⟨by linarith [hc.1],by linarith [hc.2],?_⟩
  exact (le_max_right _ _).trans (le_add_of_nonneg_right (by norm_num))

theorem exists_gap_tongue {K j k : ℕ} (hK : 2≤K) (hf : FractionInWindow K j k) :
    ∃q : Tuning,Geometry.Gap K q ∧ q.angle (Regions.rationalAngle j k)≤Real.pi/k :=
  ⟨(tongueWitness hK hf).val,(tongueWitness hK hf).property,tongueWitness_phase hK hf⟩

def rationalFrequency {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k) : Frequency :=
  ⟨Regions.rationalAngle j k,(Regions.rationalAngle_mem hj hjk).1.le,
    (Regions.rationalAngle_mem hj hjk).2.le⟩

theorem gap_tongue_dirac_program {K j k : ℕ} (hK : 2≤K)
    (hf : FractionInWindow K j k) (hcop : j.Coprime k) :
    ProgramSolution (tuningCurve (tongueWitness hK hf).val) nonzeroLags
      (Measure.dirac (rationalFrequency (show 1≤j from by
        have h := (fraction_window_arithmetic hK hf).1; omega)
        (fraction_window_arithmetic hK hf).2)) := by
  obtain ⟨hj,hjk⟩ := fraction_window_arithmetic hK hf
  exact (Lattice.rational_atom_program_iff _ hcop (show 2≤k by omega) _ rfl).mpr
    (tongueWitness_phase hK hf)

theorem gap_tongue_rate_lower {K j k : ℕ} (hK : 2≤K)
    (hf : FractionInWindow K j k) (hcop : j.Coprime k) :
    1≤(tongueWitness hK hf).val.rate := by
  obtain ⟨hj,hjk⟩ := fraction_window_arithmetic hK hf
  exact Regions.one_le_rate_of_rational_phase _ hcop (show 1≤j by omega) hjk
    (tongueWitness_phase hK hf)

/-- The same constructed tuning has a single actual function and start,
with convergence to the source's k-periodic planar orbit. -/
theorem gap_tongue_actual_periodic_orbit {K j k : ℕ} (hK : 2≤K)
    (hf : FractionInWindow K j k) (hcop : j.Coprime k) :
    let q := (tongueWitness hK hf).val
    ∃ f : EuclideanSpace ℝ (Fin 3)→ℝ,
      CenteredSmoothStronglyConvex q.x q.y f ∧ ∃ x₀,x₀≠0 ∧ ∃ c₀ : ℝ,0<c₀ ∧
      ∃ J : EuclideanSpace ℂ (Fin 1)→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∃ orbit : ℕ→EuclideanSpace ℝ (Fin 3),Function.Periodic orbit k ∧
        (∀ n,orbit n=J (Waves.finitePosition (fun _ : Fin 1=>1)
          (fun _=>Regions.cosineFrequency (Regions.rationalAngle j k)) 0 (some n))) ∧
        (∀ n,c₀*‖x₀‖≤‖Dynamics.iterate (gradient f) 1 q.beta x₀ n‖) ∧
        Tendsto (fun n=>Dynamics.iterate (gradient f) 1 q.beta x₀ n-orbit n) atTop (𝓝 0) := by
  obtain ⟨hj,hjk⟩ := fraction_window_arithmetic hK hf
  exact Regions.exists_periodic_orbit _ hcop (show 1≤j by omega) hjk (tongueWitness_phase hK hf)

end polyak.Levels.Chart
