import krylov.Cancellation.DCCompactCanonicalCycle
import krylov.Correction.ScenarioExpansion
import krylov.Envelope.JointScenarioRegularity
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), all original symmetric sources at once.
Use: instantiate the actual compact C-one cycle theorem on the already
defined real subspace of original finite symmetric matrix scenarios.
Source: reused true symmetric scenario space, genuine joint primitive
source regularity and the actual compact full-vector reconstruction.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset Set Filter krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Correction krylov.Envelope
open scoped Topology BigOperators Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The actual full-memory consistent DC-slide output has one weighted
quadratic remainder over compact reference families and every genuine
symmetric finite source scenario, under C-one observed estimates alone.
Use: the matrix direction and its budgets are chosen after the common
reference/scenario radius and constant, so this is true source uniformity.
Article: main_krylov, apH:dcs2(b), original compact-uniform symmetric scenario cycle.
Proof: use the already defined closed real linear space of the original
symmetric source matrices. Joint primitive regularity gives the true C-one
query fields; the genuine symmetric coordinate property proves actual query
symmetry everywhere in this chart. Apply the proved compact full-vector
canonical theorem on the real reference/zero-source compact slice. -/
theorem dc_slide_consistent_compact_symmetric_scenario
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hfull : k+1=n) (K : Set X) (hK : IsCompact K)
    (hbsym : ∀ x,(base x).IsSymm)
    (hb : ∀ x∈K,ContDiffAt ℝ 1 base x) (hpos : ∀ x∈K,∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hg : ∀ x∈K,ContDiffAt ℝ 1 g x)
    (hcount : ∀ x (hx : x∈K),referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x)=n)
    (ha : ∀ x∈K,∀ j<n,
      let Q := cgOperator (base x)
      let H := methodRun (dcSlideMethod fullMemory estimate) (fun _ => Q) (fun _ => Q) (g x) j
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ x∈K,∀ j<n,0<estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) j))
    (hcal : ∀ x∈K,∀ j<n,estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) j)=CG.length (cgOperator (base x)) (g x) j) :
    let m := dcSlideMethod fullMemory estimate
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ Theta : symmetricScenarios n (k+1),‖Theta‖≤delta →
      let R := cgOperator (metricRoot (base x))⁻¹
      ‖R (probedGradient m (scenarioProbe (base x) Theta.val) (scenarioCorrection (base x) Theta.val) (g x) n)-
        deferredResponse (base x) (g x) k 0 (matrixSequenceExtension ((k+1)-1) Theta.val.1)‖≤C*‖Theta‖^2*‖R (g x)‖ := by
  let Z := X × symmetricScenarios n (k+1)
  let b : Z → Matrix (Fin n) (Fin n) ℝ := fun p => base p.1
  let h : Z → EuclideanSpace ℝ (Fin n) := fun p => g p.1
  let Theta : Z → CanonicalScenario n (k+1) := fun p => p.2.val
  let A := fun p : Z => scenarioProbe (b p) (Theta p)
  let B := fun p : Z => scenarioCorrection (b p) (Theta p)
  let D : Set Z := K×ˢ{0}
  have hD : IsCompact D := hK.prod isCompact_singleton
  have hb' (p : Z) (hp : p∈D) : ContDiffAt ℝ 1 b p := (hb p.1 hp.1).comp p contDiffAt_fst
  have hh' (p : Z) (hp : p∈D) : ContDiffAt ℝ 1 h p := (hg p.1 hp.1).comp p contDiffAt_fst
  have hpos' (p : Z) (hp : p∈D) : ∀ᶠ q in 𝓝 p,(b q).PosDef :=
    (continuous_fst.tendsto p).eventually (hpos p.1 hp.1)
  have hTheta (p : Z) : ContDiffAt ℝ 1 Theta p :=
    (symmetricScenarios n (k+1)).subtypeL.contDiff.contDiffAt.comp p contDiffAt_snd
  have hAB (p : Z) (hp : p∈D) (j : ℕ) := jointScenarioPrimitive_regular b Theta p 1
    (hb' p hp) (hpos' p hp) (hTheta p) j
  have hAzero (p : Z) (hp : p∈D) : A p=fun _ => cgOperator (b p) := by
    have hz : p.2=0 := Set.mem_singleton_iff.mp hp.2
    change scenarioProbe (base p.1) p.2.val=_
    rw [hz]
    exact scenarioProbe_zero _
  have hBzero (p : Z) (hp : p∈D) : B p=fun _ => cgOperator (b p) := by
    have hz : p.2=0 := Set.mem_singleton_iff.mp hp.2
    change scenarioCorrection (base p.1) p.2.val=_
    rw [hz]
    exact scenarioCorrection_zero _
  have hAsym (p : Z) (j : ℕ) : (A p j).toLinearMap.IsSymmetric := by
    let E := matrixSequenceExtension ((k+1)-1) p.2.val.1
    have hsum : (∑ l∈range j,E l).IsHermitian := by
      change (∑ l∈range j,E l)ᴴ=∑ l∈range j,E l
      rw [conjTranspose_sum]
      exact sum_congr rfl (fun l _ =>
        (Matrix.isHermitian_iff_isSymm.mpr (symmetricScenario_increment_symm p.2 l)).eq)
    have hr : (metricRoot (base p.1)).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr (metricRoot_isSymm _)
    have hc := Matrix.isHermitian_conjTranspose_mul_mul (metricRoot (base p.1)) hsum
    rw [hr.eq] at hc
    have hd : (cumulativeDrift (base p.1) E j).toLinearMap.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hc
    have hq : (cgOperator (base p.1)).toLinearMap.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (hbsym p.1))
    change ((cgOperator (base p.1)).toLinearMap+(1 : ℝ) • (cumulativeDrift (base p.1) E j).toLinearMap).IsSymmetric
    simpa only [one_smul] using hq.add hd
  obtain ⟨delta,C,hd,hC,hbound⟩ := dc_slide_consistent_compact_canonical_cycle estimate b h A B k hfull D hD
    hb' hpos' (fun p hp => hcount p.1 hp.1)
    (fun p hp j _ => (hAB p hp j).1) (fun p hp j _ => (hAB p hp j).2) hh'
    hAzero hBzero hAsym (fun p hp => ha p.1 hp.1) (fun p hp => ha0 p.1 hp.1) (fun p hp => hcal p.1 hp.1)
  refine ⟨delta,C,hd,hC,?_⟩
  intro x hx theta htheta
  have hnorm : ‖(x,theta)-(x,(0 : symmetricScenarios n (k+1)))‖=‖theta‖ := by
    simp only [Prod.sub_def,sub_self,sub_zero,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
  have he := hbound (x,0) ⟨hx,rfl⟩ (x,theta) (by rw [hnorm];exact htheta)
    (matrixSequenceExtension ((k+1)-1) theta.val.1) rfl
  simpa only [hnorm] using he

end
end krylov.Cancellation
