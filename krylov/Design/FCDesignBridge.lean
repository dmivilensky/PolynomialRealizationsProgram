import krylov.Design.DegenerateWeights
import krylov.Design.FiniteMajorants
import krylov.Reference.AtomicEnergyRealization
import krylov.Stability.FCWorstReferences

/-!
Article: main_krylov, Gamma_omega = Gamma*_(w,1/2), before thm:B.
Use: identify the actual full-active FC reference supremum with the genuine
all-probability-measures mixed design optimum, including every nonnegative
budget vector and the empty criterion.
Source: the actual CG/Christoffel dictionary, explicit diagonal spectral
realization, and the proved prescribed-atom approximation theorem.
-/
namespace krylov.Design
noncomputable section
open Matrix Set MeasureTheory jacobi.Finite krylov.Reference krylov.Stability
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The preterminal FC budgets attached to the original design weights.
The last full-cycle budget contributes zero because actual CG has terminated.
Article: main_krylov, Gamma_omega = Gamma*_(w,1/2). -/
def fcDesignBudgets {M : ℕ} (w : Fin M → ℝ) (l : ℕ) : ℝ :=
  if h : l<M then w ⟨l,h⟩ else 0

private theorem fcDesignBudgets_nonneg {M : ℕ} (w : Fin M → ℝ)
    (hw : ∀ i, 0≤w i) (l : ℕ) : 0≤fcDesignBudgets w l := by
  unfold fcDesignBudgets
  split
  · exact hw _
  · exact le_rfl

private theorem interval_upper_eq (I : chebyshev1.SpectralInterval) : I.mu*I.kappa=I.L := by
  change I.mu*(I.L/I.mu)=I.L
  field_simp [I.mu_pos.ne']

private theorem coefficient_finite_sum {M : ℕ} {μ κ : ℝ}
    (R : FCReference (M+1) μ κ) (w : Fin M → ℝ) :
    R.coefficient (fcDesignBudgets w)=
      (∑ i : Fin M, w i*‖cgCanonicalError R.base R.gradient (i.val+1)‖)/R.initialNorm := by
  unfold FCReference.coefficient
  rw [Finset.sum_range_succ]
  simp only [fcDesignBudgets,lt_self_iff_false,dite_false,zero_mul,add_zero]
  congr 1
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [i.isLt,dite_true]

private theorem half_objective_profile (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (ν : ProbabilityMeasure (Spectrum I)) (a : ℝ) (ha : 0<a)
    (e : ℕ → ℝ) (he : ∀ m, 0≤e m)
    (hp : ∀ i : Fin M, (e (i.val+1))^2=
      a^2*christoffel (i.val+1) 0 (spectralCoordinate I) ν) :
    intervalObjective I M w (1/2) ν=(∑ i : Fin M, w i*e (i.val+1))/a := by
  unfold intervalObjective mixedObjective
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Real.sqrt_eq_rpow]
  have hh : e (i.val+1)=a*Real.sqrt (christoffel (i.val+1) 0 (spectralCoordinate I) ν) := by
    apply (sq_eq_sq₀ (he _) (mul_nonneg ha.le (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt (christoffel_nonneg _ _ _ _)]
    exact hp i
  rw [hh]
  field_simp

/-- The actual aggregated energy measure of any genuine FC reference lies in
its original physical spectral interval. Article: main_krylov, lem:chris. -/
theorem fcReference_energy_nodes {n : ℕ} (I : chebyshev1.SpectralInterval)
    (R : FCReference n I.mu I.kappa) :
    ∀ j, (energySpectralData R.base R.positive R.gradient R.nonzero).node j∈Icc I.mu I.L := by
  intro j
  let v := cgCanonicalError R.base R.gradient 0
  let t := (activeSpectralValues R.base R.positive.1 v).equivFin.symm j
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp t.property
  change I.mu≤t.val ∧ t.val≤I.L
  rw [←hi]
  simpa only [interval_upper_eq I] using R.interval i

/-- Every actual full-active FC reference coefficient is the original mixed
half-power criterion of its genuine energy probability measure.
Article: main_krylov, Gamma_omega = Gamma*_(w,1/2). -/
theorem fcReference_coefficient_eq_objective (I : chebyshev1.SpectralInterval) (M : ℕ)
    (R : FCReference (M+1) I.mu I.kappa) (w : Fin M → ℝ) :
    R.coefficient (fcDesignBudgets w)=intervalObjective I M w (1/2)
      (atomicProbability (energySpectralData R.base R.positive R.gradient R.nonzero)
        (fun i=>⟨_,fcReference_energy_nodes I R i⟩)) := by
  rw [coefficient_finite_sum]
  symm
  apply half_objective_profile I M w _ R.initialNorm R.initialNorm_pos
    (fun m=>‖cgCanonicalError R.base R.gradient m‖) (fun _=>norm_nonneg _)
  intro i
  rw [interval_christoffel_atomic I _ (fcReference_energy_nodes I R) (by have := R.full; omega : i.val+1<referenceAtomCount R.base R.positive R.gradient)]
  exact cg_energy_christoffel R.base R.positive R.gradient R.nonzero (by have := R.full; omega)

/-- Every genuine exactly-(M+1)-atom design is realized by an actual full-active
positive FC reference, with exactly the same original coefficient.
Article: main_krylov, Gamma_omega = Gamma*_(w,1/2), reverse realization. -/
theorem atomicDesign_fcReference_realization (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (Q : AtomicIntervalDesign I (M+1)) :
    ∃ R : FCReference (M+1) I.mu I.kappa,
      R.initialNorm=1 ∧ R.coefficient (fcDesignBudgets w)=atomicDesignObjective I M w (1/2) Q := by
  obtain ⟨A,hA,g,hg,hcount,hband,hinit,hprofile⟩ :=
    atomic_energy_reference_realization Q.val I.mu I.L I.mu_pos Q.property
  let R : FCReference (M+1) I.mu I.kappa :=
    ⟨A,hA,g,hg,hcount,fun i=>by simpa only [interval_upper_eq I] using hband i⟩
  refine ⟨R,hinit,?_⟩
  rw [coefficient_finite_sum]
  symm
  apply half_objective_profile I M w _ R.initialNorm R.initialNorm_pos
    (fun m=>‖cgCanonicalError A g m‖) (fun _=>norm_nonneg _)
  intro i
  rw [interval_christoffel_atomic I Q.val Q.property (by omega : i.val+1<M+1)]
  change ‖cgCanonicalError A g (i.val+1)‖^2=‖cgCanonicalError A g 0‖^2*_
  rw [hinit,one_pow,one_mul,hprofile,finiteChristoffelValue,ite_eq_left (by omega : i.val+1<M+1)]

/-- The original FC worst-reference coefficient equals the genuine mixed
all-measures design optimum. No spectral realization hypothesis is assumed.
This includes empty, zero and trailing-zero weights.
Article: main_krylov, Gamma_omega = Gamma*_(w,1/2), before thm:B. -/
theorem fcWorstCoefficient_eq_optimalValue (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0≤w i) :
    fcWorstCoefficient (M+1) I.mu I.kappa (fcDesignBudgets w)=optimalValue I M w (1/2) := by
  have hω : ∀ l<M+1, 0≤fcDesignBudgets w l := fun l _=>fcDesignBudgets_nonneg w hw l
  have hnonneg : 0≤optimalValue I M w (1/2) :=
    (mixedObjective_nonneg M w hw (1/2) 0 (spectralCoordinate I) (lobattoProbability I 0)).trans
      (intervalObjective_half_le_optimalValue I M w hw _)
  apply le_antisymm
  · apply csSup_le ⟨0,Set.mem_insert 0 _⟩
    intro x hx
    rcases hx with rfl|⟨R,rfl⟩
    · exact hnonneg
    · change R.coefficient (fcDesignBudgets w)≤_
      rw [fcReference_coefficient_eq_objective]
      exact intervalObjective_half_le_optimalValue I M w hw _
  · rw [←atomicDesignValue_eq_optimalValue_all I M (M+1) le_rfl w hw (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1)]
    have hne := exists_atomicIntervalDesign I (M+1) (by omega)
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨Q,rfl⟩
    obtain ⟨R,_,hR⟩ := atomicDesign_fcReference_realization I M w Q
    rw [←hR]
    exact le_csSup (fcCoefficientSet_bounded (fcDesignBudgets w) hω)
      (Set.mem_insert_of_mem _ (Set.mem_range_self R))

/-- The final actual CG error is zero, so only the preterminal budgets affect
any genuine full-cycle reference coefficient. Article: main_krylov, thm:A. -/
theorem fcReference_coefficient_preterminal (I : chebyshev1.SpectralInterval) (M : ℕ)
    (R : FCReference (M+1) I.mu I.kappa) (ω : ℕ → ℝ) :
    R.coefficient ω=R.coefficient (fcDesignBudgets (fun i : Fin M=>ω i.val)) := by
  have hz : cgCanonicalError R.base R.gradient (M+1)=0 := by
    have hh := (cg_stopping_iff R.base R.positive R.gradient (M+1)).mpr (by rw [R.full])
    simp only [cgCanonicalError,hh,map_zero]
  unfold FCReference.coefficient
  congr 1
  rw [Finset.sum_range_succ,Finset.sum_range_succ,hz,norm_zero,mul_zero,mul_zero,add_zero,add_zero]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [fcDesignBudgets,Finset.mem_range.mp hl,dite_true]

/-- The literal original-budget FC/design identity, with
w_m = omega_(m-1); the unused terminal budget may be arbitrary.
Article: main_krylov, Gamma_omega = Gamma*_(w,1/2), before thm:B. -/
theorem fcWorstCoefficient_eq_design (I : chebyshev1.SpectralInterval) (M : ℕ)
    (ω : ℕ → ℝ) (hω : ∀ l<M, 0≤ω l) :
    fcWorstCoefficient (M+1) I.mu I.kappa ω=
      optimalValue I M (fun i : Fin M=>ω i.val) (1/2) := by
  have hh : (fun R : FCReference (M+1) I.mu I.kappa=>R.coefficient ω)=
      fun R=>R.coefficient (fcDesignBudgets (fun i : Fin M=>ω i.val)) :=
    funext (fun R=>fcReference_coefficient_preterminal I M R ω)
  change sSup (insert 0 (Set.range (fun R : FCReference (M+1) I.mu I.kappa=>R.coefficient ω)))=_
  rw [hh]
  exact fcWorstCoefficient_eq_optimalValue I M _ (fun i=>hω i.val i.isLt)

/-- Uniform original budgets give exactly omega times the unweighted finite
optimal design value, including omega=0 and M=0.
Article: main_krylov, Gamma_omega = omega Gamma*_(n-1), before thm:B. -/
theorem fcWorstCoefficient_uniform (I : chebyshev1.SpectralInterval) (M : ℕ)
    (ω : ℝ) (hω : 0≤ω) :
    fcWorstCoefficient (M+1) I.mu I.kappa (fun _=>ω)=
      ω*optimalValue I M (fun _=>1) (1/2) := by
  rw [fcWorstCoefficient_eq_design I M _ (fun _ _=>hω)]
  have hscale (ν : ProbabilityMeasure (Spectrum I)) :
      intervalObjective I M (fun _=>ω) (1/2) ν=
        ω*intervalObjective I M (fun _=>1) (1/2) ν := by
    unfold intervalObjective mixedObjective
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  obtain ⟨ν,hν⟩ := intervalObjective_attains I M (fun _=>1) (fun _=>zero_le_one)
    (by norm_num : (0:ℝ)≤1/2)
  have hων : ∀ η, intervalObjective I M (fun _=>ω) (1/2) η≤
      intervalObjective I M (fun _=>ω) (1/2) ν := by
    intro η
    rw [hscale,hscale]
    exact mul_le_mul_of_nonneg_left (hν η) hω
  rw [optimalValue_eq_of_maximizer I M (fun _=>ω) (1/2) ν hων,
    optimalValue_eq_of_maximizer I M (fun _=>1) (1/2) ν hν,hscale]

end
end krylov.Design
