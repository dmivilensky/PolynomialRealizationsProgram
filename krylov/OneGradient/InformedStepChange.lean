import krylov.Methods.DirectionStepChange
import krylov.OneGradient.InformedNativeRegularity
import krylov.OneGradient.InformedNativeReference
import krylov.Stability.ContDiffSpectralMatrix
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual informed D pair change.
Use: derive smoothness, the diagonal reference and invertibility of the
true recorded-step change from primitive operators and active CG geometry.
Source: the real native prefix induction and computed zero reference
virtual coefficients, with no assumed smooth or vanishing replay weights.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine observed step change on an actual informed D history
is C-one, is diagonal at the true reference and has a nonsingular reference.
Use: all basis-change hypotheses for the real latest-model comparison
are discharged from primitive physical operators and actual CG activity.
Article: main_krylov, thm:local(a), genuine native observed-change domains.
Proof: the actual native columns, images and incoming observations are
C-one with real nonsingular reference models. Their computed virtual
weights are therefore C-one and vanish by true CG orthogonality. The exact
finite step-change program is C-one and reduces to the actual positive
trial diagonal at reference, whose determinant is nonzero. -/
theorem informed_native_step_change_data
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k≤N) :
    let trial := informedTrial (cgOperator base)
    let tau := fun j : Fin k => trial (oneGradientRun (xrfcDMethod fullMemory trial) (A 0) g (k-1-j.val))
    ContDiffAt ℝ 1 (fun z => xrfcDObservedStepChange trial (A z) g k) 0 ∧
      xrfcDObservedStepChange trial (A 0) g k=diagonal tau ∧
      IsUnit (xrfcDObservedStepChange trial (A 0) g k).det := by
  dsimp only
  let Q := cgOperator base
  let trial := informedTrial Q
  let m := xrfcDMethod fullMemory trial
  let tau := fun z (j : Fin k) => trial (oneGradientRun m (A z) g (k-1-j.val))
  let w := fun z (j : Fin k) => xrfcDArrayCoefficients trial (A z) g (k-1-j.val)
  have hp := cgOperator_positive base hb
  have hreg := informed_native_prefix_contDiff true base hb g N hpre A hA hA0
  have hw (j : Fin k) (i : Fin (k-1-j.val)) : ContDiffAt ℝ 1 (fun z => w z j i) 0 := by
    let l := k-1-j.val
    have hd := informed_native_reference_domains true Q hp.1 hp.2 g N hpre l (by dsimp [l];omega)
    have hdom : (pairModel (xrfcNativeColumns true trial (A 0) g l)
        (xrfcNativeImages true trial (A 0) g l)).det≠0 := by rw [hA0];exact hd.2
    exact contDiff_modelCoefficients
      (fun z => xrfcNativeColumns true trial (A z) g l)
      (fun z => pairModel (xrfcNativeColumns true trial (A z) g l) (xrfcNativeImages true trial (A z) g l))
      (fun z => oneGradientGradient m (A z) g l) 0
      (fun r => (hreg.2.1 l (by dsimp [l];omega) r).1)
      (fun r s => ((hreg.2.1 l (by dsimp [l];omega) (max r s)).1).inner ℝ
        (hreg.2.1 l (by dsimp [l];omega) (min r s)).2)
      (hreg.1 l (by dsimp [l];omega)) hdom i
  have hw0 (j : Fin k) : w 0 j=0 := by
    have ho := informed_native_reference_orthogonal true Q hp.1 hp.2 g N hpre (k-1-j.val) (by omega)
    have ho' : coordinates (xrfcNativeColumns true trial (A 0) g (k-1-j.val))
        (oneGradientGradient m (A 0) g (k-1-j.val))=0 := by rw [hA0];exact ho
    exact modelCoefficients_zero _ _ _ ho'
  have he : xrfcDObservedStepChange trial (A 0) g k=diagonal (tau 0) :=
    observedStepChange_zero_weights (tau 0) (w 0) (fun j r => congrFun (hw0 j) r)
  refine ⟨?_,he,?_⟩
  · exact observedStepChange_contDiffAt tau w
      (fun j => hreg.2.2 _ (by omega)) hw
  · rw [he,Matrix.det_diagonal]
    rw [isUnit_iff_ne_zero,Finset.prod_ne_zero_iff]
    intro i _
    exact (informed_trial_positive Q _).ne'

end
end krylov.OneGradient
