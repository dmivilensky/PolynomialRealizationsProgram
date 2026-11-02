import krylov.Convergence.EvaluatedLaunchDictionary
import krylov.Convergence.EvaluatedRegularity

/-!
Article: main_krylov, prop:EL, complete original evaluated-launch variation.
Use: retain genuine varying initial-gradient data and the true chronological
observed model while deriving the printed full old-flag launch response.
Source: actual full-model first variation and real evaluated reference geometry.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
  krylov.OneGradient krylov.Correction
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Original evaluated-launch response with the full accumulated trial
miss and the genuine observed old flags. Article: main_krylov, prop:EL. -/
def evaluatedLaunchResponse (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (∑ l∈Finset.range n,cgOperator (transportedFlag (evaluatedCanonicalColumns trial base g) l)ᵀ*
    E l*cgOperator (transportedFlag (evaluatedCanonicalColumns trial base g) l))
      (∑ i∈Finset.range n,(evaluatedTrialError trial base g i*Real.sqrt (cgEnergy base g i)) •
        canonicalCGUnitStep base g i)

/-- Actual primitive evaluated-launch data give exactly the original
full launch first variation, including a varying initial gradient.
Article: main_krylov, prop:EL. -/
theorem evaluatedLaunch_output_first_jet_varying_gradient
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : ℝ → EuclideanSpace ℝ (Fin n)) (hg : ContDiffAt ℝ 1 g 0)
    (hc : referenceAtomCount base hb (g 0)=n)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun t => A t k) 0)
    (hsym : ∀ t k,(A t k).IsSymm) (hA0 : ∀ k,A 0 k=base)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) (g 0) i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (evaluatedLaunchMethod trial) (fun _ => cgOperator base) (g 0) k)) :
    let m := evaluatedLaunchMethod trial
    let op := fun t k => cgOperator (A t k)
    let R := cgOperator (metricRoot base)⁻¹
    let E := fun l => R*(deriv (fun t => op t (l+1)) 0-deriv (fun t => op t l) 0)*R
    HasDerivAt (fun t => R (m.outputGradient (op t n) (oneGradientRun m (op t) (g t) n)))
      (evaluatedLaunchResponse trial base (g 0) E) 0 := by
  let m := evaluatedLaunchMethod trial
  let op := fun t k => cgOperator (A t k)
  let S := fun t=>fullBasisMatrix (fun i : Fin n=>oneGradientStep m (op t) (g t) i.val)
  let G := fun t => oneGradientGradient m (op t) (g t) n
  let R := cgOperator (metricRoot base)⁻¹
  let E := fun l => R*(deriv (fun t => op t (l+1)) 0-deriv (fun t => op t l) 0)*R
  let P := fun l => transportedFlag (evaluatedCanonicalColumns trial base (g 0)) l
  let C := ∑ l∈Finset.range n,cgOperator (P l)ᵀ*E l*cgOperator (P l)
  have hAx : op 0=(fun _=>cgOperator base) := funext (fun k=>by simp only [op,hA0])
  have hreg := quadraticEvaluatedLaunch_prefix_contDiffAt trial op g 0
    (fun k=>matrixOperator_contDiffAt _ 0 (hA k)) hg (cgOperator base) hAx
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 n
    (fun i hi=>cg_nonstagnation base hb (g 0) i (by rw [hc];exact hi)) ht (by rw [hAx];exact hT)
  have hS : ContDiffAt ℝ 1 S 0 := by
    apply contDiff_spectral_matrix
    intro i j
    change ContDiffAt ℝ 1 (fun t=>(oneGradientStep m (op t) (g t) j.val) i) 0
    let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv
    exact contDiffAt_pi.mp (e.toContinuousLinearMap.contDiff.contDiffAt.comp 0 (hreg.2 j.val j.isLt)) i
  have hdata : ContDiffAt ℝ 1 S 0 ∧ ContDiffAt ℝ 1 G 0 := ⟨hS,hreg.1 n le_rfl⟩
  have hS0 : S 0=evaluatedLaunchPhysicalColumns trial base (g 0) := by
    dsimp only [S]
    rw [hAx]
    rfl
  have hu : IsUnit (S 0).det := by
    rw [hS0]
    exact (evaluatedLaunch_columns_nonsingular trial base hb (g 0) hc ht).1
  have hfirst := launch_semantic_first_jet base hb S hdata.1 hu A hA hsym hA0 G hdata.2
  let C0 := ∑ l∈Finset.range n,cgOperator (transportedFlag (metricRoot base*S 0) l)ᵀ*
    E l*cgOperator (transportedFlag (metricRoot base*S 0) l)
  change HasDerivAt (fun t => R (launchSemanticGradient (S t) (A t) (G t))) (-(C0 (R (G 0)))) 0 at hfirst
  have hC : C0=C := by
    dsimp only [C0,C,P]
    rw [hS0]
    rfl
  rw [hC] at hfirst
  have hG0 : G 0=(oneGradientRun m (fun _ => cgOperator base) (g 0) n).gradient := by
    change (oneGradientRun m (op 0) (g 0) n).gradient=_
    rw [hAx]
  have hlaunch : R (G 0)=-(∑ i∈Finset.range n,
      (evaluatedTrialError trial base (g 0) i*Real.sqrt (cgEnergy base (g 0) i)) •
        canonicalCGUnitStep base (g 0) i) := by
    rw [hG0]
    exact evaluated_canonical_error trial base hb (g 0) hc ht
  have hresponse : -(C (R (G 0)))=evaluatedLaunchResponse trial base (g 0) E := by
    rw [hlaunch,map_neg,neg_neg]
    rfl
  rw [hresponse] at hfirst
  have hunit : ∀ᶠ t in 𝓝 (0 : ℝ),IsUnit (S t).det := by
    have hu0 : IsUnit (S 0) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
    exact (hdata.1.continuousAt.tendsto.eventually (Units.isOpen.mem_nhds hu0)).mono
      (fun t ht' => (Matrix.isUnit_iff_isUnit_det _).mp ht')
  have he : (fun t => R (m.outputGradient (op t n) (oneGradientRun m (op t) (g t) n)))=ᶠ[𝓝 0]
      (fun t => R (launchSemanticGradient (S t) (A t) (G t))) := by
    filter_upwards [hunit] with t ht'
    exact congrArg R (evaluatedLaunch_semantic_launch_dictionary trial (A t) (g t) ht')
  dsimp only
  exact hfirst.congr_of_eventuallyEq he



end
end krylov.Convergence
