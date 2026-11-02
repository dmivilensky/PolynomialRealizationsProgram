import krylov.Stability.ContDiffXRFC

/-!
Article: main_krylov, lem:xr-local, actual joint trial/operator calculus.
Use: propagate genuine C^r regularity through the real XRFC execution
when the primitive trial policy itself depends on external parameters.
This is used with literal prescribed finite trial vectors; regularity
of those evaluated scalars is then proved from their coordinate projections.
Source: exact genuine observed coordinates and real finite inverse solves.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Parametric policies have the same genuine finite observed block
calculus: the actual vector inputs determine both true inverse solves. -/
theorem parametric_oneGradient_virtual_contDiffAt {r : WithTop ℕ∞}
    (m : X → OneGradientMethod E) (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (k : ℕ)
    (hA : ∀ i < k, ContDiffAt ℝ r (fun z => A z i) x)
    (hs : ∀ i < k, ContDiffAt ℝ r (fun z => oneGradientStep (m z) (A z) (g z) i) x)
    (hg : ContDiffAt ℝ r (fun z => oneGradientGradient (m z) (A z) (g z) k) x)
    (hM : (pairModel
      (fun i : Fin k => oneGradientStep (m x) (A x) (g x) (k - 1 - i.val))
      (fun i : Fin k => A x (k - 1 - i.val) (oneGradientStep (m x) (A x) (g x) (k - 1 - i.val)))).det ≠ 0)
    (hY : (crossGram
      (fun i : Fin k => A x (k - 1 - i.val) (oneGradientStep (m x) (A x) (g x) (k - 1 - i.val)))
      (fun i : Fin k => oneGradientStep (m x) (A x) (g x) (k - 1 - i.val))).det ≠ 0) :
    let H := fun z => oneGradientRun (m z) (A z) (g z) k
    ContDiffAt ℝ r (fun z => virtualCorrection (selectedWindow fullMemory (H z)) (H z).gradient) x ∧
      ContDiffAt ℝ r (fun z => virtualGradient (selectedWindow fullMemory (H z)) (H z).gradient) x ∧
      ContDiffAt ℝ r (fun z => windowDirection (selectedWindow fullMemory (H z))
        (virtualGradient (selectedWindow fullMemory (H z)) (H z).gradient)) x := by
  let S := fun z (i : Fin k) => oneGradientStep (m z) (A z) (g z) (k - 1 - i.val)
  let Y := fun z (i : Fin k) => A z (k - 1 - i.val) (S z i)
  let G := fun z => oneGradientGradient (m z) (A z) (g z) k
  have hS (i : Fin k) : ContDiffAt ℝ r (fun z => S z i) x := hs _ (by omega)
  have hImages (i : Fin k) : ContDiffAt ℝ r (fun z => Y z i) x :=
    (hA _ (by omega)).clm_apply (hS i)
  have hv := contDiff_virtualBlock S Y G x hS hImages hg hM hY
  refine ⟨?_, ?_, ?_⟩
  · exact hv.1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z =>
      (oneGradient_full_virtual_coordinates (m z) (A z) (g z) k).1)
  · exact hv.2.1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z =>
      (oneGradient_full_virtual_coordinates (m z) (A z) (g z) k).2)
  · apply (contDiff_conjugacyDirection S Y _ x hS hImages hv.2.1 hY).congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro z
    dsimp only
    rw [(oneGradient_full_virtual_coordinates (m z) (A z) (g z) k).2]
    exact oneGradient_full_direction_coordinates (m z) (A z) (g z) _ k

/-- Genuine parametric XRFC prefix regularity. In the prescribed-trial
application the scalar premise is a literal coordinate projection, not
an assumed smooth trajectory or desired output response. -/
theorem parametric_xrfc_prefix_contDiffAt {r : WithTop ℕ∞}
    (trial : X → History E → ℝ) (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ)
    (hA : ∀ i < N, ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (hM : ∀ k < N, (pairModel
      (fun i : Fin k => oneGradientStep (xrfcMethod fullMemory (trial x)) (A x) (g x) (k - 1 - i.val))
      (fun i : Fin k => A x (k - 1 - i.val)
        (oneGradientStep (xrfcMethod fullMemory (trial x)) (A x) (g x) (k - 1 - i.val)))).det ≠ 0)
    (hY : ∀ k < N, (crossGram
      (fun i : Fin k => A x (k - 1 - i.val)
        (oneGradientStep (xrfcMethod fullMemory (trial x)) (A x) (g x) (k - 1 - i.val)))
      (fun i : Fin k => oneGradientStep (xrfcMethod fullMemory (trial x)) (A x) (g x) (k - 1 - i.val))).det ≠ 0)
    (htrial : ∀ k < N, ContDiffAt ℝ r
      (fun z => trial z (oneGradientRun (xrfcMethod fullMemory (trial z)) (A z) (g z) k)) x) :
    (∀ k ≤ N, ContDiffAt ℝ r (fun z =>
      oneGradientGradient (xrfcMethod fullMemory (trial z)) (A z) (g z) k) x) ∧
      ∀ i < N, ContDiffAt ℝ r (fun z =>
        oneGradientStep (xrfcMethod fullMemory (trial z)) (A z) (g z) i) x := by
  induction N with
  | zero =>
    refine ⟨?_, fun i hi => by omega⟩
    intro k hk
    have he : k = 0 := by omega
    subst k
    exact hg
  | succ k ih =>
    obtain ⟨hG, hs⟩ := ih (fun i hi => hA i (by omega))
      (fun j hj => hM j (by omega)) (fun j hj => hY j (by omega)) (fun j hj => htrial j (by omega))
    have hv := parametric_oneGradient_virtual_contDiffAt
      (fun z => xrfcMethod fullMemory (trial z)) A g x k (fun i hi => hA i (by omega)) hs
      (hG k le_rfl) (hM k (by omega)) (hY k (by omega))
    have hstep : ContDiffAt ℝ r (fun z =>
        oneGradientStep (xrfcMethod fullMemory (trial z)) (A z) (g z) k) x :=
      hv.1.add ((htrial k (by omega)).smul hv.2.2)
    have hnext : ContDiffAt ℝ r (fun z =>
        oneGradientGradient (xrfcMethod fullMemory (trial z)) (A z) (g z) (k + 1)) x := by
      simp only [oneGradientGradient_succ]
      exact (hG k le_rfl).add ((hA k (by omega)).clm_apply hstep)
    constructor
    · intro j hj
      by_cases he : j = k + 1
      · subst j
        exact hnext
      · exact hG j (by omega)
    · intro i hi
      by_cases he : i = k
      · subst i
        exact hstep
      · exact hs i (by omega)

end
end krylov.XR
