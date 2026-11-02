import krylov.OneGradient.CalibratedNativeRegularity
import krylov.OneGradient.CalibratedNativeImage
import krylov.OneGradient.NativeVirtualData
import krylov.Stability.ContDiffSolve
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine native virtual data.
Use: retain the true computed S/D virtual gradient and direction as named
observed quantities and derive their actual primitive regularity.
Source: genuine native finite solves, calibrated reference calibration and
primitive observed prefix calculus, with every inverse domain derived.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Both actual native virtual fields are C-one from primitive physical
operators and have their genuine calibrated CG reference values.
Use: the curvature jet requires no assumed smooth direction or trajectory.
Article: main_krylov, thm:local(a), actual virtual-field regularity.
Proof: primitive native prefix induction gives real old observations and
incoming gradients. The true reference solve domains give smooth finite
virtual solves; real projected CG orthogonality makes the reference
weights zero, and true native calibration identifies the direction. -/
theorem calibrated_native_virtual_data (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (hcal : CalibratedTrial trial (cgOperator base) g (N))
    (hT : ∀ (directions : Bool) (k : ℕ),k<(N) → ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g k))
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k≤N) :
      let gv := fun z => xrfcNativeVirtualGradient directions trial (A z) g k
    let d := fun z => xrfcNativeDirection directions trial (A z) g k
    ContDiffAt ℝ 1 gv 0 ∧ ContDiffAt ℝ 1 d 0 ∧
      gv 0=CG.gradient (cgOperator base) g k ∧ d 0=CG.direction (cgOperator base) g k := by
  let Q := cgOperator base
  let m := xrfcBasisMethod directions trial
  let s := fun z => xrfcNativeColumns directions trial (A z) g k
  let y := fun z => xrfcNativeImages directions trial (A z) g k
  let G := fun z => oneGradientGradient m (A z) g k
  let gv := fun z => xrfcNativeVirtualGradient directions trial (A z) g k
  let d := fun z => xrfcNativeDirection directions trial (A z) g k
  have hp := cgOperator_positive base hb
  have hreg := calibrated_native_prefix_contDiff directions trial base hb g N hpre hcal hT A hA hA0
  have hdom : (crossGram (y 0) (s 0)).det≠0 ∧ (pairModel (s 0) (y 0)).det≠0 := by
    dsimp only [s,y]
    rw [hA0]
    exact calibrated_native_reference_domains directions trial Q hp.1 hp.2 g N hpre hcal k hk
  have hblock := contDiff_virtualBlock s y G 0
    (fun i => (hreg.2.1 k hk i).1) (fun i => (hreg.2.1 k hk i).2)
    (hreg.1 k hk) hdom.2 hdom.1
  have horth : coordinates (s 0) (G 0)=0 := by
    dsimp only [s,G]
    rw [hA0]
    exact calibrated_native_reference_orthogonal directions trial Q hp.1 hp.2 g N hpre hcal k hk
  have hgv : gv 0=G 0 := by
    change G 0+combine (y 0) (modelCoefficients (s 0) (pairModel (s 0) (y 0)) (G 0))=G 0
    rw [modelCoefficients_zero _ _ _ horth]
    simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,add_zero]
  have hGref : G 0=CG.gradient Q g k := by
    dsimp only [G]
    rw [hA0]
    exact calibrated_native_reference_gradient directions trial Q hp.1 hp.2 g N hpre hcal k hk
  refine ⟨hblock.2.1,hblock.2.2,hgv.trans hGref,?_⟩
  change conjugacyDirection (s 0) (y 0) (gv 0)=_
  rw [hgv,hGref]
  dsimp only [s,y]
  rw [hA0]
  exact calibrated_native_reference_direction directions trial Q hp.1 hp.2 g N hpre hcal k hk

end
end krylov.OneGradient
