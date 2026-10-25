import polyak.Global.Sampling.PhaseCircle
import polyak.Global.Sampling.AliasingGrid
import polyak.Levels.Program.EndpointRemoval
import polyak.Levels.Program.FiniteAtoms
import polyak.Levels.Threshold.MeasureTools

/-! The sampled density defines an actual positive finite measure.
Folding and deleting endpoint atoms preserves every program constraint. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.Levels MeasureTheory Set
open scoped ENNReal NNReal

def sampleMeasure (f : Circle→ℝ) (L : ℕ) : Measure Circle :=
  ∑j:Fin L,Real.toNNReal (f (samplePoint L j)/(L:ℝ)) • Measure.dirac (samplePoint L j)

instance sampleMeasure_finite (f : Circle→ℝ) (L : ℕ) : IsFiniteMeasure (sampleMeasure f L) := by
  unfold sampleMeasure
  infer_instance

theorem integral_sampleMeasure {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Circle→ℝ) (hf : ∀x,0≤f x) {L:ℕ} (hL:0<L) (g : Circle→E) (hg:Continuous g) :
    (∫x,g x∂sampleMeasure f L)=(L:ℝ)⁻¹ • ∑j:Fin L,f (samplePoint L j) • g (samplePoint L j) := by
  rw [sampleMeasure,integral_finsetSum_measure]
  · simp only [integral_smul_nnreal_measure,integral_dirac,NNReal.smul_def]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.coe_toNNReal _ (div_nonneg (hf _) (by positivity)),div_eq_mul_inv,mul_smul,
      smul_comm]
  · intro j _
    exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem fold_samplePoint_grid {L:ℕ} (hL:0<L) (j:Fin L) :
    Circle.fold (samplePoint L j)=frequencyZero ∨ Circle.fold (samplePoint L j)∈periodicGrid L := by
  let t:ℝ:=2*Real.pi*j.val/L
  have hLR : 0<(L:ℝ):=by exact_mod_cast hL
  have ht0 : 0≤t:=by dsimp [t]; positivity
  have htpi : t<2*Real.pi := by
    apply (div_lt_iff₀ hLR).mpr
    have hjR : (j.val:ℝ)<L:=by exact_mod_cast j.isLt
    exact mul_lt_mul_of_pos_left hjR Real.two_pi_pos
  by_cases htp : t≤Real.pi
  · let u : Frequency:=⟨t,ht0,htp⟩
    have hu : Circle.fold (samplePoint L j)=u:=Circle.fold_embed u
    by_cases hz:t=0
    · left
      rw [hu]
      exact Subtype.ext hz
    · right
      rw [hu]
      refine ⟨lt_of_le_of_ne ht0 (Ne.symm hz),(j.val:ℤ),?_⟩
      change (L:ℝ)*(2*Real.pi*j.val/L)=((j.val:ℤ):ℝ)*(2*Real.pi)
      push_cast
      field_simp
  · right
    have hu : (Circle.fold (samplePoint L j):ℝ)=2*Real.pi-t:=
      circle_fold_complement ⟨le_of_not_ge htp,htpi.le⟩
    refine ⟨by rw [hu]; linarith,(L:ℤ)-j.val,?_⟩
    rw [hu]
    dsimp [t]
    push_cast
    field_simp


theorem ae_fold_sampleMeasure_grid (f:Circle→ℝ) {L:ℕ} (hL:0<L) :
    ∀ᵐω∂Circle.folded (sampleMeasure f L),ω=frequencyZero ∨ ω∈periodicGrid L := by
  apply (ae_map_iff Circle.continuous_fold.measurable.aemeasurable
    ((measurableSet_singleton frequencyZero).union ?_)).mpr
  · rw [sampleMeasure]
    apply ae_finsetSum_measure_iff.mpr
    intro j _
    apply Measure.ae_smul_measure _ _
    apply (ae_dirac_iff ?_).mpr
    · exact fold_samplePoint_grid hL j
    · exact Circle.continuous_fold.measurable (
        (measurableSet_singleton frequencyZero).union (periodicGrid_finite hL).measurableSet)
  · exact (periodicGrid_finite hL).measurableSet

theorem periodicFP_of_sampled_moments (Θ:Curve) (f:Circle→ℝ) {L:ℕ} (hL:0<L)
    (hmin : 0<∫x,Circle.minimizer Θ x∂sampleMeasure f L)
    (hlag : ∀n:ℤ,n≠0→0≤∫x,Circle.lag Θ n x∂sampleMeasure f L) : PeriodicFP Θ L := by
  let w:=Circle.folded (sampleMeasure f L)
  have : IsFiniteMeasure w:=by unfold w Circle.folded; infer_instance
  have hminw : 0<∫ω,Θ.minimizer ω∂w := by
    change 0<∫ω,Θ.minimizer ω∂Circle.folded (sampleMeasure f L)
    rw [Circle.integral_folded _ _ Θ.continuous_minimizer]
    exact hmin
  have hlagw : ∀n:ℤ,n≠0→0≤∫ω,Θ.lag n ω∂w := by
    intro n hn
    change 0≤∫ω,Θ.lag n ω∂Circle.folded (sampleMeasure f L)
    rw [Circle.integral_folded _ _ (Θ.continuous_lag n)]
    exact hlag n hn
  have hw : ProgramSolution Θ nonzeroLags w := ⟨inferInstance,by
    intro he
    rw [he,integral_zero_measure] at hminw
    exact lt_irrefl _ hminw,hminw.le,fun n hn=>hlagw n hn⟩
  refine ⟨w.restrict {ω | 0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi},hw.remove_endpoints,?_⟩
  have hcar:=ae_fold_sampleMeasure_grid f hL
  have hsub : ∀ᵐω∂w.restrict Threshold.interiorCarrier,ω=frequencyZero ∨ ω∈periodicGrid L :=
    ae_mono Measure.restrict_le_self hcar
  filter_upwards [hsub,ae_restrict_mem Threshold.measurableSet_interiorCarrier] with ω hω hint
  rcases hω with hω|hω
  · subst ω
    exact False.elim ((lt_irrefl (0:ℝ)) hint.1)
  · exact hω

end polyak.Global.Sampling
