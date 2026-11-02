import krylov.OneGradient.InformedNativeRegularity
import krylov.OneGradient.InformedNativeCalibration
import krylov.Stability.ContDiffSolve
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine native virtual data.
Use: retain the true computed S/D virtual gradient and direction as named
observed quantities and derive their actual primitive regularity.
Source: genuine native finite solves, informed reference calibration and
primitive observed prefix calculus, with every inverse domain derived.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual virtual gradient computed from the native observed solve.
Use: the true relative last-pivot error uses the actual native virtual pair.
Article: main_krylov, thm:local(a), genuine native virtual gradient. -/
def xrfcNativeVirtualGradient (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  let s := xrfcNativeColumns directions trial A g k
  let y := xrfcNativeImages directions trial A g k
  let G := oneGradientGradient (xrfcBasisMethod directions trial) A g k
  G+combine y (modelCoefficients s (pairModel s y) G)

/-- The actual direction computed by the native conjugacy solve.
Use: S and D keep their genuine off-quadratic virtual directions.
Article: main_krylov, thm:local(a), genuine native direction. -/
def xrfcNativeDirection (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  conjugacyDirection (xrfcNativeColumns directions trial A g k)
    (xrfcNativeImages directions trial A g k) (xrfcNativeVirtualGradient directions trial A g k)

/-- Both actual native virtual fields are C-one from primitive physical
operators and have their genuine calibrated CG reference values.
Use: the curvature jet requires no assumed smooth direction or trajectory.
Article: main_krylov, thm:local(a), actual virtual-field regularity.
Proof: primitive native prefix induction gives real old observations and
incoming gradients. The true reference solve domains give smooth finite
virtual solves; real projected CG orthogonality makes the reference
weights zero, and true native calibration identifies the direction. -/
theorem informed_native_virtual_data (directions : Bool)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k≤N) :
    let trial := informedTrial (cgOperator base)
    let gv := fun z => xrfcNativeVirtualGradient directions trial (A z) g k
    let d := fun z => xrfcNativeDirection directions trial (A z) g k
    ContDiffAt ℝ 1 gv 0 ∧ ContDiffAt ℝ 1 d 0 ∧
      gv 0=CG.gradient (cgOperator base) g k ∧ d 0=CG.direction (cgOperator base) g k := by
  let Q := cgOperator base
  let trial := informedTrial Q
  let m := xrfcBasisMethod directions trial
  let s := fun z => xrfcNativeColumns directions trial (A z) g k
  let y := fun z => xrfcNativeImages directions trial (A z) g k
  let G := fun z => oneGradientGradient m (A z) g k
  let gv := fun z => xrfcNativeVirtualGradient directions trial (A z) g k
  let d := fun z => xrfcNativeDirection directions trial (A z) g k
  have hp := cgOperator_positive base hb
  have hreg := informed_native_prefix_contDiff directions base hb g N hpre A hA hA0
  have hdom : (crossGram (y 0) (s 0)).det≠0 ∧ (pairModel (s 0) (y 0)).det≠0 := by
    dsimp only [s,y]
    rw [hA0]
    exact informed_native_reference_domains directions Q hp.1 hp.2 g N hpre k hk
  have hblock := contDiff_virtualBlock s y G 0
    (fun i => (hreg.2.1 k hk i).1) (fun i => (hreg.2.1 k hk i).2)
    (hreg.1 k hk) hdom.2 hdom.1
  have horth : coordinates (s 0) (G 0)=0 := by
    dsimp only [s,G]
    rw [hA0]
    exact informed_native_reference_orthogonal directions Q hp.1 hp.2 g N hpre k hk
  have hgv : gv 0=G 0 := by
    change G 0+combine (y 0) (modelCoefficients (s 0) (pairModel (s 0) (y 0)) (G 0))=G 0
    rw [modelCoefficients_zero _ _ _ horth]
    simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,add_zero]
  have hGref : G 0=CG.gradient Q g k := by
    dsimp only [G]
    rw [hA0]
    exact informed_native_reference_gradient directions Q hp.1 hp.2 g N hpre k hk
  refine ⟨hblock.2.1,hblock.2.2,hgv.trans hGref,?_⟩
  change conjugacyDirection (s 0) (y 0) (gv 0)=_
  rw [hgv,hGref]
  dsimp only [s,y]
  rw [hA0]
  exact informed_native_reference_direction directions Q hp.1 hp.2 g N hpre k hk

end
end krylov.OneGradient
