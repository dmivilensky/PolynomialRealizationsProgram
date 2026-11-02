import krylov.OneGradient.XRFCStepVariation

/-!
Article: main_krylov, lem:cycle-transfer and thm:V.
Use: retain the actual varying initial gradient in the full XRFC operator
variation. Its derivative contributes no first-order launch term because
the true reference model-error factor vanishes.
Source: genuine full-model launch differentiation and actual query regularity.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
  krylov.OneGradient krylov.Correction
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The printed XRFC first variation remains exact for the genuinely
varying initial gradient supplied by a nonlinear scalar source.
Article: main_krylov, thm:V, initial-gradient drift cancellation. -/
theorem xrfc_step_output_first_jet_varying_gradient
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : ℝ → EuclideanSpace ℝ (Fin n)) (hg : ContDiffAt ℝ 1 g 0)
    (hc : referenceAtomCount base hb (g 0)=n) (hn : 0<n)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun t => A t k) 0)
    (hsym : ∀ t k,(A t k).IsSymm) (hA0 : ∀ k,A 0 k=base)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) (g 0) i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) (g 0) k)) :
    let m := xrfcMethod fullMemory trial
    let op := fun t k => cgOperator (A t k)
    let R := cgOperator (metricRoot base)⁻¹
    let E := fun l => R*(deriv (fun t => op t (l+1)) 0-deriv (fun t => op t l) 0)*R
    HasDerivAt (fun t => R (m.outputGradient (op t n) (oneGradientRun m (op t) (g t) n)))
      (xrfcStepResponse trial base (g 0) E) 0 := by
  let m := xrfcMethod fullMemory trial
  let op := fun t k => cgOperator (A t k)
  let S := fun t=>fullBasisMatrix (fun i : Fin n=>oneGradientStep m (op t) (g t) i.val)
  let G := fun t => oneGradientGradient m (op t) (g t) n
  let R := cgOperator (metricRoot base)⁻¹
  let E := fun l => R*(deriv (fun t => op t (l+1)) 0-deriv (fun t => op t l) 0)*R
  let P := fun l => transportedFlag (xrfcCanonicalColumns trial base (g 0)) l
  let C := ∑ l∈Finset.range n,cgOperator (P l)ᵀ*E l*cgOperator (P l)
  have hAx : op 0=(fun _=>cgOperator base) := funext (fun k=>by simp only [op,hA0])
  have hreg := quadraticXRFC_prefix_contDiffAt trial op g 0
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
  have hS0 : S 0=xrfcPhysicalColumns trial base (g 0) := by
    dsimp only [S]
    rw [hAx]
    rfl
  have hu : IsUnit (S 0).det := by
    rw [hS0]
    exact (xrfc_columns_nonsingular trial base hb (g 0) hc ht).1
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
  have hlaunch : R (G 0)=-(xrfcTrialCoefficient trial base (g 0) n (n-1) • canonicalCGUnitStep base (g 0) (n-1)) := by
    rw [hG0]
    exact xrfc_reference_launch_error trial base hb (g 0) hc hn ht
  have hresponse : -(C (R (G 0)))=xrfcStepResponse trial base (g 0) E := by
    rw [hlaunch,map_neg,neg_neg]
    simp only [C,_root_.sum_apply,mul_apply_eq_comp,xrfcStepResponse]
    apply Finset.sum_congr rfl
    intro l hl
    have h := xrfc_projector_last_amplitude trial base hb (g 0) hc ht l (Finset.mem_range.mp hl)
    change cgOperator (P l)ᵀ (E l (cgOperator (P l)
        (xrfcTrialCoefficient trial base (g 0) n (n-1) • canonicalCGUnitStep base (g 0) (n-1))))=_
    rw [h,map_smul,map_smul]
  rw [hresponse] at hfirst
  have hunit : ∀ᶠ t in 𝓝 (0 : ℝ),IsUnit (S t).det := by
    have hu0 : IsUnit (S 0) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
    exact (hdata.1.continuousAt.tendsto.eventually (Units.isOpen.mem_nhds hu0)).mono
      (fun t ht' => (Matrix.isUnit_iff_isUnit_det _).mp ht')
  have he : (fun t => R (m.outputGradient (op t n) (oneGradientRun m (op t) (g t) n)))=ᶠ[𝓝 0]
      (fun t => R (launchSemanticGradient (S t) (A t) (G t))) := by
    filter_upwards [hunit] with t ht'
    exact congrArg R (xrfc_semantic_launch_dictionary trial (A t) (g t) ht')
  dsimp only
  exact hfirst.congr_of_eventuallyEq he


end
end krylov.Convergence
