import krylov.Cancellation.DeferredDataFirstVariation
import krylov.Envelope.ScenarioPaths
import krylov.Envelope.ScenarioVariation
import krylov.Stability.CompactSmooth
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, actual uniform finite-source deferred expansion.
Use: obtain one quadratic remainder constant for every genuine finite
canonical source scenario, not a separate constant for each real source axis.
Source: primitive native C-two execution on actual finite observed coordinates,
the proved genuine full-cycle first jet and compact vector Taylor at zero.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Envelope
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original arbitrary-positive-observed-estimate deferred full-cycle
canonical gradient has one genuine quadratic remainder bound for every true
finite symmetric canonical increment/correction scenario near zero.
Use: independent matrix budget suprema share the same actual remainder;
regularity and the first derivative are derived from original observed data.
Article: main_krylov, thm:DC, uniform original finite-source O(omega squared).
Proof: actual primitive finite scenario operators and the original native
coefficient chart derive joint scenario C-two gradient regularity. Every true
symmetric scenario axis has its proved literal deferred response first jet,
which identifies the genuine joint Frechet derivative. The real compact
Taylor theorem at the singleton zero therefore gives a common quadratic tube. -/
theorem deferred_data_scenario_expansion
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (ha :
      let H := methodRun (deferredDataMethod fullMemory (k+1) estimate)
        (fun _ => cgOperator base) (fun _ => cgOperator base) g k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : 0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)) :
    let Q := cgOperator base
    let a0 := estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) g k)
    let m := deferredDataMethod fullMemory (k+1) estimate
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ Theta : CanonicalScenario n (k+1),‖Theta‖≤delta →
      (∀ l,(Theta.1 l).IsSymm) →
      ‖cgOperator (metricRoot base)⁻¹ (scenarioGradient m base g (k+1) Theta)-
        deferredResponse base g k (1-CG.length Q g k/a0) (matrixSequenceExtension ((k+1)-1) Theta.1)‖≤C*‖Theta‖^2 := by
  let Q := cgOperator base
  let m := deferredDataMethod fullMemory (k+1) estimate
  let R := cgOperator (metricRoot base)⁻¹
  let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) g k)
  let epsilon := 1-CG.length Q g k/a0
  let Phi := fun Theta : CanonicalScenario n (k+1) => R (scenarioGradient m base g (k+1) Theta)
  have hQ := (cgOperator_positive base hb).1
  have hpos := (cgOperator_positive base hb).2
  have hN : k+1≤referenceAtomCount base hb g := by omega
  have hpre (j : ℕ) (hj : j<k+1) : CG.gradient Q g j≠0 := cg_nonstagnation base hb g j (hj.trans_le hN)
  have hG : ContDiffAt ℝ 2 (scenarioGradient m base g (k+1)) 0 :=
    deferred_data_gradient_contDiffAt fullMemory (fun _ hj => hj) (k+1) estimate (scenarioProbe base) (scenarioCorrection base)
      (fun _ => g) 0 (k+1) (fun j _ => (scenarioPrimitive_regular base hb j 2).1)
      (fun j _ => (scenarioPrimitive_regular base hb j 2).2) contDiffAt_const Q
      (scenarioProbe_zero base) (scenarioCorrection_zero base) hQ hpos hpre
      (fun j _ hj => by
        have he : j=k := by omega
        subst j
        exact ha)
      (fun j _ hj => by
        have he : j=k := by omega
        subst j
        exact ha0)
  have hPhi : ContDiffAt ℝ 2 Phi 0 := R.contDiff.contDiffAt.comp 0 hG
  have hPhi0 : Phi 0=0 := by
    change R (probedGradient m (scenarioProbe base 0) (scenarioCorrection base 0) g (k+1))=0
    rw [scenarioProbe_zero,scenarioCorrection_zero]
    have hg0 : probedGradient m (fun _ => Q) (fun _ => Q) g (k+1)=CG.gradient Q g (k+1) :=
      quadratic_gradient_eq_cg m (deferred_data_consistent fullMemory (fun _ hj => hj) (k+1) estimate) Q hQ hpos g (k+1)
    rw [hg0]
    have hstop : CG.gradient Q g (k+1)=0 := (cg_stopping_iff base hb g (k+1)).mpr (by omega)
    rw [hstop,map_zero]
  have hD (Theta : CanonicalScenario n (k+1)) (hTheta : ∀ l,(Theta.1 l).IsSymm) :
      fderiv ℝ Phi 0 Theta=deferredResponse base g k epsilon (matrixSequenceExtension ((k+1)-1) Theta.1) := by
    let E := matrixSequenceExtension ((k+1)-1) Theta.1
    let B := fun t : ℝ => scenarioCorrection base (t • Theta)
    have hE (l : ℕ) : (E l).IsSymm := by
      dsimp only [E,matrixSequenceExtension]
      split
      · exact hTheta _
      · exact Matrix.isSymm_zero
    have hB (j : ℕ) : ContDiffAt ℝ 2 (fun t => B t j) 0 := (scenarioCorrection_path_analytic base Theta j).contDiffAt
    have hB0 : B 0=fun _ => Q := by dsimp only [B];rw [zero_smul,scenarioCorrection_zero]
    have hn := deferred_data_full_hasDerivAt estimate base hb g E hE B k (fun j _ => hB j) hB0 hcount hfull ha ha0
    have heq : (fun t : ℝ => Phi (t • Theta))=
        fun t => R (probedGradient m (canonicalFCPath base E t) (B t) g (k+1)) := by
      funext t
      dsimp only [Phi,scenarioGradient]
      rw [scenarioProbe_scale]
    have hn' : HasDerivAt (fun t : ℝ => Phi (t • Theta)) (deferredResponse base g k epsilon E) 0 :=
      hn.congr_of_eventuallyEq (Eventually.of_forall (fun t => congrFun heq t))
    have hline : HasDerivAt (fun t : ℝ => t • Theta) Theta 0 := by
      convert! (hasDerivAt_id (0 : ℝ)).smul_const Theta using 1
      simp only [one_smul]
    have hf : HasFDerivAt Phi (fderiv ℝ Phi 0) ((0 : ℝ) • Theta) := by
      rw [zero_smul]
      exact (hPhi.differentiableAt (by norm_num)).hasFDerivAt
    have haxis := hf.comp_hasDerivAt 0 hline
    change HasDerivAt (fun t : ℝ => Phi (t • Theta)) ((fderiv ℝ Phi 0) Theta) 0 at haxis
    exact haxis.unique hn'
  obtain ⟨delta,C,hd,hC,hbound⟩ := compact_smooth_taylor Phi 2 ({0} : Set (CanonicalScenario n (k+1))) isCompact_singleton
    (by intro x hx;rw [Set.mem_singleton_iff.mp hx];exact hPhi)
  refine ⟨delta,C,hd,hC,?_⟩
  intro Theta hnorm hTheta
  have hT : taylorPolynomial Phi 2 0 Theta=deferredResponse base g k epsilon (matrixSequenceExtension ((k+1)-1) Theta.1) := by
    simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,iteratedFDeriv_zero_apply,
      iteratedFDeriv_one_apply,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,zero_add]
    rw [hPhi0,zero_add,hD Theta hTheta]
  have he := hbound 0 (Set.mem_singleton 0) Theta hnorm 2 (by omega) le_rfl
  rw [hT] at he
  simpa only [zero_add] using he

end
end krylov.Cancellation
