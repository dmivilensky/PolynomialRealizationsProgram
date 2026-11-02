import krylov.Stability.ContDiffVirtual
import krylov.Methods.HistoryWindowCharts
set_option autoImplicit false
/-!
Article: main_krylov, lem:U(d), fixed-length observed-window calculus.
Use: differentiate actual list-window solves without placing a topology on
variable-length histories or assuming smoothness of any executed solve.
Source: the existing finite-array virtual calculus and true getter reindexing.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Actual fixed-length list windows have smooth virtual corrections,
gradients and directions on their two genuine nonsingular model domains.
Use: finite replay rules can reuse the original observed-window calculus.
Article: main_krylov, lem:U(d).
Proof: transport actual getters to fixed arrays, apply the proved array
calculus and transport the computed physical vectors back exactly. -/
theorem contDiff_windowBlock {p : ℕ} {r : WithTop ℕ∞}
    (W : X → List (E × E)) (hlen : ∀ z,(W z).length=p) (g : X → E) (x : X)
    (hS : ∀ i : Fin p,ContDiffAt ℝ r (fun z => ((W z).getD i.val (0,0)).1) x)
    (hY : ∀ i : Fin p,ContDiffAt ℝ r (fun z => ((W z).getD i.val (0,0)).2) x)
    (hg : ContDiffAt ℝ r g x) (hM : (windowModel (W x)).det≠0)
    (hC : (crossGram (windowImages (W x)) (windowSteps (W x))).det≠0) :
    ContDiffAt ℝ r (fun z => virtualCorrection (W z) (g z)) x ∧
      ContDiffAt ℝ r (fun z => virtualGradient (W z) (g z)) x ∧
      ContDiffAt ℝ r (fun z => windowDirection (W z) (virtualGradient (W z) (g z))) x := by
  let S := fun z (i : Fin p) => ((W z).getD i.val (0,0)).1
  let Y := fun z (i : Fin p) => ((W z).getD i.val (0,0)).2
  have hcoords (z : X) := virtualWindow_coordinates (W z) (hlen z) (S z) (Y z)
    (windowSteps_getD_array _ _ (hlen z)) (windowImages_getD_array _ _ (hlen z)) (g z)
  have hm : (pairModel (S x) (Y x)).det≠0 := by
    have he := windowModel_of_coordinates (W x) (hlen x) (S x) (Y x)
      (windowSteps_getD_array _ _ (hlen x)) (windowImages_getD_array _ _ (hlen x))
    rw [he,Matrix.det_submatrix_equiv_self] at hM
    exact hM
  have hc : (crossGram (Y x) (S x)).det≠0 := by
    rwa [crossGram_getD_array_det (W x) p (hlen x)] at hC
  have h := contDiff_virtualBlock S Y g x hS hY hg hm hc
  refine ⟨?_,?_,?_⟩
  · exact h.1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => (hcoords z).1))
  · exact h.2.1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => (hcoords z).2))
  · apply h.2.2.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro z
    dsimp only
    rw [windowDirection_getD_array (W z) p (hlen z),(hcoords z).2]

end
end krylov.Stability
