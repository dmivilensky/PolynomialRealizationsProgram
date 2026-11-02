import krylov.Cancellation.DCObserved
import krylov.Methods.SmoothTrace
import Mathlib.Topology.Instances.Matrix
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), actual observed-window neighborhood domain.
Use: preserve the genuine retained inverse domain under real smooth observed
history perturbations with the actual finite query shape.
Source: genuine fixed-shape history reconstruction, actual native determinant
coordinate invariance and continuity of the finite determinant polynomial.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The true retained cross-Gram determinant stays nonsingular near an actual
smooth observed history with a fixed genuine query shape.
Use: exact cancellation identities apply on a real execution neighborhood,
without assuming the desired perturbed native solve domains.
Article: main_krylov, thm:dcs(c).
Proof: reconstruct the original actual history from its real finite smooth
observations. The fixed-array native determinant is continuous and exactly
the real list determinant by simultaneous coordinate reindexing, so its true
nonzero reference value persists on the actual history neighborhood. -/
theorem observed_window_domain_eventually (memory : ℕ → ℕ) (H : X → History E) (x : X)
    (htrace : SmoothListAt 1 (fun p => (H p).observationList) x)
    (hshape : ∀ᶠ p in 𝓝 x,(H p).queryShape=(H x).queryShape)
    (hC : (crossGram (windowImages (selectedWindow memory (H x)))
      (windowSteps (selectedWindow memory (H x)))).det≠0) :
    ∀ᶠ p in 𝓝 x,IsUnit (crossGram (windowImages (selectedWindow memory (H p)))
      (windowSteps (selectedWindow memory (H p)))).det := by
  obtain ⟨n,data,hd,he⟩ := htrace
  let shape := (H x).queryShape
  let W := fun p => chartWindow memory shape (data p)
  have hW : ∀ᶠ p in 𝓝 x,selectedWindow memory (H p)=W p := by
    filter_upwards [he,hshape] with p hp hs
    dsimp only [W,chartWindow,shape]
    rw [← hp,← hs,historyFromObservations_actual]
  let M := fun p => crossGram (chartImages memory shape (data p)) (chartSteps memory shape (data p))
  have hfields := chartSteps_regular memory shape data x hd
  have hm : ContinuousAt M x := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (hfields i).2.continuousAt.inner (hfields j).1.continuousAt
  have hdet : ContinuousAt (fun p => (M p).det) x := continuous_id.matrix_det.continuousAt.comp hm
  have hcoord (p : X) : (crossGram (windowImages (W p)) (windowSteps (W p))).det=(M p).det :=
    crossGram_getD_array_det _ _ (chartWindow_length memory shape (data p))
  have hzero : (M x).det≠0 := by
    rw [← hcoord x,← hW.self_of_nhds]
    exact hC
  filter_upwards [hW,hdet.eventually_ne hzero] with p hp hnonzero
  rw [hp,hcoord]
  exact isUnit_iff_ne_zero.mpr hnonzero

end
end krylov.Cancellation
