import krylov.Cancellation.DeferredDataFirstVariation
import krylov.Envelope.JointScenarioOutput
import krylov.Envelope.ScenarioPaths
import krylov.Stability.WeightedCompactTaylor
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, genuine compact-reference original source expansion.
Use: obtain one true radius and weighted quadratic constant across compact
families of positive full-atom references and all finite canonical sources.
Source: original primitive observed-estimate compilation, joint actual source
operators, proved native full first variation and compact weighted Taylor.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Envelope
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The original data-dependent deferred output has the literal sharp fresh
plus damped-tail response with a single genuine weighted quadratic remainder
on every compact family of full-atom references and every finite symmetric
source scenario. Only the actual final observed estimate chart is assumed
C-two and positive at those references.
Use: the source's compact-uniform applicability has one radius and constant
chosen before the reference, its source direction or its matrix budget.
Article: main_krylov, thm:DC, full compact-reference source expansion.
Proof: true joint primitive source and metric-root calculus derives C-two
regularity of the original executed output from the original final estimate
chart. The actual native full first variation identifies each symmetric
scenario-direction derivative. Compact weighted Taylor on the genuine
reference/zero-source slice gives one common tube; full CG termination
removes the constant term and the proved derivative gives the printed response. -/
theorem deferred_data_compact_scenario_expansion
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hfull : k+1=n) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K,ContDiffAt ℝ 2 base x)
    (hpos : ∀ x∈K,∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hg : ∀ x∈K,ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K),referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x)=n)
    (ha : ∀ x∈K,
      let Q := cgOperator (base x)
      let H := methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) (g x) k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ x∈K,0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) k)) :
    let m := deferredDataMethod fullMemory (k+1) estimate
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ Theta : CanonicalScenario n (k+1),‖Theta‖≤delta →
      (∀ l,(Theta.1 l).IsSymm) →
      let Q := cgOperator (base x)
      let R := cgOperator (metricRoot (base x))⁻¹
      let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) (g x) k)
      ‖R (scenarioGradient m (base x) (g x) (k+1) Theta)-
        deferredResponse (base x) (g x) k (1-CG.length Q (g x) k/a0)
          (matrixSequenceExtension ((k+1)-1) Theta.1)‖≤C*‖Theta‖^2*‖R (g x)‖ := by
  let m := deferredDataMethod fullMemory (k+1) estimate
  let Phi := jointScenarioOutput m base g (k+1)
  let e := fun x => ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖
  have hp (x : X) (hx : x∈K) : (base x).PosDef := (hpos x hx).self_of_nhds
  have hPhi (x : X) (hx : x∈K) : ContDiffAt ℝ 2 Phi (x,0) := by
    let b : X × CanonicalScenario n (k+1) → Matrix (Fin n) (Fin n) ℝ := fun p => base p.1
    let h : X × CanonicalScenario n (k+1) → EuclideanSpace ℝ (Fin n) := fun p => g p.1
    have hb' : ContDiffAt ℝ 2 b (x,0) := (hb x hx).comp _ contDiffAt_fst
    have hg' : ContDiffAt ℝ 2 h (x,0) := (hg x hx).comp _ contDiffAt_fst
    have hp' : ∀ᶠ p in 𝓝 ((x,0) : X × CanonicalScenario n (k+1)),(b p).PosDef :=
      (continuous_fst.tendsto (x,(0 : CanonicalScenario n (k+1)))).eventually (hpos x hx)
    have hAB (j : ℕ) := jointScenarioPrimitive_regular b (fun p : X × CanonicalScenario n (k+1) => p.2)
      (x,0) 2 hb' hp' contDiffAt_snd j
    let Q := cgOperator (base x)
    have hpre (j : ℕ) (hj : j<k+1) : CG.gradient Q (g x) j≠0 :=
      cg_nonstagnation _ (hp x hx) _ j (by rw [hcount x hx];omega)
    have hG := deferred_data_gradient_contDiffAt fullMemory (fun _ hj => hj) (k+1) estimate
      (fun p => scenarioProbe (b p) p.2) (fun p => scenarioCorrection (b p) p.2) h (x,0) (k+1)
      (fun j _ => (hAB j).1) (fun j _ => (hAB j).2) hg' Q (scenarioProbe_zero _) (scenarioCorrection_zero _)
      (cgOperator_positive _ (hp x hx)).1 (cgOperator_positive _ (hp x hx)).2 hpre
      (fun j _ hj => by
        have he : j=k := by omega
        subst j
        exact ha x hx)
      (fun j _ hj => by
        have he : j=k := by omega
        subst j
        exact ha0 x hx)
    exact (matrixOperator_contDiffAt _ (x,0) (metricRoot_inverse_contDiffAt b (x,0) hb' hp')).clm_apply hG
  have he : ContinuousOn e K := canonical_error_continuousOn base g K
    (fun x hx => (hb x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hp
  have hepos (x : X) (hx : x∈K) : 0<e x := canonical_error_pos (base x) (hp x hx) (g x)
    (cg_nonstagnation _ (hp x hx) _ 0 (by rw [hcount x hx];omega))
  have hzero (x : X) (hx : x∈K) : Phi (x,0)=0 := by
    change cgOperator (metricRoot (base x))⁻¹
      (probedGradient m (scenarioProbe (base x) 0) (scenarioCorrection (base x) 0) (g x) (k+1))=0
    rw [scenarioProbe_zero,scenarioCorrection_zero]
    have hG : probedGradient m (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) (k+1)=0 :=
      (quadratic_gradient_eq_cg m (deferred_data_consistent fullMemory (fun _ hj => hj) (k+1) estimate)
        _ (cgOperator_positive _ (hp x hx)).1 (cgOperator_positive _ (hp x hx)).2 (g x) (k+1)).trans
        ((cg_stopping_iff _ (hp x hx) _ (k+1)).mpr (by rw [hcount x hx];omega))
    rw [hG,map_zero]
  have hD (x : X) (hx : x∈K) (Theta : CanonicalScenario n (k+1)) (hTheta : ∀ l,(Theta.1 l).IsSymm) :
      fderiv ℝ Phi (x,0) (0,Theta)=
        deferredResponse (base x) (g x) k
          (1-CG.length (cgOperator (base x)) (g x) k/
            estimate (methodRun m (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) k))
          (matrixSequenceExtension ((k+1)-1) Theta.1) := by
    let E := matrixSequenceExtension ((k+1)-1) Theta.1
    let B := fun t : ℝ => scenarioCorrection (base x) (t • Theta)
    have hE (l : ℕ) : (E l).IsSymm := by
      dsimp only [E,matrixSequenceExtension]
      split
      · exact hTheta _
      · exact Matrix.isSymm_zero
    have hB (j : ℕ) : ContDiffAt ℝ 2 (fun t => B t j) 0 := (scenarioCorrection_path_analytic (base x) Theta j).contDiffAt
    have hB0 : B 0=fun _ => cgOperator (base x) := by dsimp only [B];rw [zero_smul,scenarioCorrection_zero]
    have hn := deferred_data_full_hasDerivAt estimate (base x) (hp x hx) (g x) E hE B k
      (fun j _ => hB j) hB0 (hcount x hx) hfull (ha x hx) (ha0 x hx)
    have heq : (fun t : ℝ => Phi (x,t • Theta))=
        fun t => cgOperator (metricRoot (base x))⁻¹
          (probedGradient m (canonicalFCPath (base x) E t) (B t) (g x) (k+1)) := by
      funext t
      dsimp only [Phi,jointScenarioOutput,scenarioGradient]
      rw [scenarioProbe_scale]
    have hn' := hn.congr_of_eventuallyEq (Eventually.of_forall (fun t => congrFun heq t))
    have hline : HasDerivAt (fun t : ℝ => t • Theta) Theta 0 := by
      convert! (hasDerivAt_id (0 : ℝ)).smul_const Theta using 1
      simp only [one_smul]
    have hcurve : HasDerivAt (fun t : ℝ => (x,t • Theta)) (0,Theta) 0 := (hasDerivAt_const 0 x).prodMk hline
    have hf : HasFDerivAt Phi (fderiv ℝ Phi (x,0)) (x,(0 : ℝ) • Theta) := by
      rw [zero_smul]
      exact ((hPhi x hx).differentiableAt (by norm_num)).hasFDerivAt
    have haxis := hf.comp_hasDerivAt 0 hcurve
    change HasDerivAt (fun t : ℝ => Phi (x,t • Theta)) ((fderiv ℝ Phi (x,0)) (0,Theta)) 0 at haxis
    exact haxis.unique hn'
  let U := interior {p | ContDiffAt ℝ 2 Phi p}
  have hKU : ∀ x∈K,(x,(0 : CanonicalScenario n (k+1)))∈U := fun x hx =>
    mem_interior_iff_mem_nhds.mpr ((hPhi x hx).eventually (by simp))
  obtain ⟨delta,C,hd,hC,hbound⟩ := compact_reference_taylor Phi e 2 U K isOpen_interior hK hKU
    (fun p hp => (show ContDiffAt ℝ 2 Phi p from interior_subset hp).contDiffWithinAt) he hepos
  refine ⟨delta,C,hd,hC,?_⟩
  intro x hx Theta hnorm hTheta
  have hT : taylorPolynomial Phi 2 (x,0) (0,Theta)=
      deferredResponse (base x) (g x) k
        (1-CG.length (cgOperator (base x)) (g x) k/
          estimate (methodRun m (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) k))
        (matrixSequenceExtension ((k+1)-1) Theta.1) := by
    simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,iteratedFDeriv_zero_apply,
      iteratedFDeriv_one_apply,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,zero_add]
    rw [hzero x hx,zero_add,hD x hx Theta hTheta]
  have hh := hbound x hx Theta hnorm 2 (by omega) le_rfl
  rw [hT] at hh
  exact hh

end
end krylov.Cancellation
