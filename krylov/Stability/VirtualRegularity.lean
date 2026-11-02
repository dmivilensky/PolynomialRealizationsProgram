import krylov.Stability.ContDiffVirtual

/-!
Article: main_krylov, lem:U(d), genuine full-memory observed virtual regularity.
Use: apply finite C^r inverse calculus to the actual history, actual secants
and true virtual launch of any one-gradient executor.
Source: exact actual one-gradient window coordinates and primitive smooth solve calculus.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine full-memory virtual correction, extrapolated gradient and direction are C^r when the actual observed prefix is C^r and its two true finite solves are nonsingular.
Use: a real XRFC prefix gains smooth virtual outputs from actual already observed steps and gradients.
Article: main_krylov, alg:xrfc and lem:U(d).
Proof: true old secants are actual segment-operator images of the real
queried steps. Their fixed finite arrays satisfy the proved smooth block
calculus; the exact observed-window coordinate identities identify all three
actual policy computations with these genuine smooth finite solves. -/
theorem oneGradient_virtualBlock_contDiffAt {r : WithTop ℕ∞} (m : OneGradientMethod E)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (k : ℕ)
    (hA : ∀ i<k, ContDiffAt ℝ r (fun z => A z i) x)
    (hs : ∀ i<k, ContDiffAt ℝ r (fun z => oneGradientStep m (A z) (g z) i) x)
    (hG : ContDiffAt ℝ r (fun z => oneGradientGradient m (A z) (g z) k) x)
    (hM : (pairModel
      (fun i : Fin k => oneGradientStep m (A x) (g x) (k-1-i.val))
      (fun i : Fin k => A x (k-1-i.val) (oneGradientStep m (A x) (g x) (k-1-i.val)))).det≠0)
    (hC : (crossGram
      (fun i : Fin k => A x (k-1-i.val) (oneGradientStep m (A x) (g x) (k-1-i.val)))
      (fun i : Fin k => oneGradientStep m (A x) (g x) (k-1-i.val))).det≠0) :
    let H := fun z => oneGradientRun m (A z) (g z) k
    ContDiffAt ℝ r (fun z => virtualCorrection (selectedWindow fullMemory (H z)) (H z).gradient) x ∧
      ContDiffAt ℝ r (fun z => virtualGradient (selectedWindow fullMemory (H z)) (H z).gradient) x ∧
      ContDiffAt ℝ r (fun z => windowDirection (selectedWindow fullMemory (H z))
        (virtualGradient (selectedWindow fullMemory (H z)) (H z).gradient)) x := by
  -- Every input below is extracted from the actual recorded prefix; none is a hypothetical smooth trajectory.
  let S := fun z (i : Fin k) => oneGradientStep m (A z) (g z) (k-1-i.val)
  let Y := fun z (i : Fin k) => A z (k-1-i.val) (S z i)
  let G := fun z => oneGradientGradient m (A z) (g z) k
  have hS (i : Fin k) : ContDiffAt ℝ r (fun z => S z i) x := hs _ (by omega)
  have hY (i : Fin k) : ContDiffAt ℝ r (fun z => Y z i) x := (hA _ (by omega)).clm_apply (hS i)
  have ht := contDiff_virtualBlock S Y G x hS hY hG hM hC
  have hcorr : ContDiffAt ℝ r (fun z => virtualCorrection
      (selectedWindow fullMemory (oneGradientRun m (A z) (g z) k))
      (oneGradientRun m (A z) (g z) k).gradient) x :=
    ht.1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => (oneGradient_full_virtual_coordinates m (A z) (g z) k).1)
  have hgrad : ContDiffAt ℝ r (fun z => virtualGradient
      (selectedWindow fullMemory (oneGradientRun m (A z) (g z) k))
      (oneGradientRun m (A z) (g z) k).gradient) x :=
    ht.2.1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => (oneGradient_full_virtual_coordinates m (A z) (g z) k).2)
  refine ⟨hcorr,hgrad,?_⟩
  apply (contDiff_conjugacyDirection S Y _ x hS hY hgrad hC).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro z
  exact oneGradient_full_direction_coordinates m (A z) (g z) _ k

end
end krylov.Stability
