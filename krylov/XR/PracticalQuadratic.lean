import krylov.XR.Practical
import krylov.XR.QuadraticObservedFlag

/-!

Article: Proposition 7.5 [prop:practical-trial] of krylov.tex.
Practical XR on exact quadratics: the unchanged virtual CG reference.

Source: the established faithful-quadratic retention and Galerkin identities
in `QuadraticObservedFlag`. The fresh-secant policy changes the scalar used
in the new direction, not the virtual projection. These statements concern
the raw exact-real model. They assert neither a floating-point trajectory nor
that the safeguard is inactive or that a zero trial extends the Krylov flag.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference
open scoped InnerProductSpace

/-- The genuine nonempty partial-window practical branch is the block
model step with its computed fresh scalar, including a zero new direction. -/
theorem practicalModel_partial {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hp : (practicalModel P S).pairs.length ≠ 0)
    (hfull : (practicalModel P S).pairs.length ≠ n) :
    let M := practicalModel P S
    let s := storedSteps M.pairs
    let y := storedImages M.pairs
    let T := selectedModel P M.pairs
    M.direction = modelTrialStep s y T S.gradient
      (M.fallbackCurvature * ‖modelDirection s y T S.gradient‖ ^ 2) := by
  unfold practicalModel at hp hfull ⊢
  dsimp only at hp hfull ⊢
  rw [ite_eq_right hp, ite_eq_right hfull]

/-- A faithful independent quadratic window fitting the capacity is retained
by the practical policy, with its actual deletion counts. -/
theorem practical_quadratic_model_retains {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g₀ : EuclideanSpace ℝ (Fin n))
    (constant : ℝ) (S : State (EuclideanSpace ℝ (Fin n)))
    (hfaithful : ∀ a ∈ S.pairs,
      PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S.point a)
    (hs : LinearIndependent ℝ (storedSteps S.pairs))
    (hcap : S.pairs.length ≤ min S.capacity n) :
    (practicalModel P S).pairs = S.pairs ∧
      (practicalModel P S).pairsBeforeTest = S.pairs.length ∧
      (practicalModel P S).deletedByTest = 0 := by
  rcases practicalModel_window P S with ⟨hp, hb, hd⟩
  rw [hp, hb, hd]
  exact quadratic_model_retains P Q hQ hpos g₀ constant S hfaithful hs hcap

/-- The practical model's actual selected arrays give the same genuine
virtual CG point, gradient and direction. This includes XR-F: its value
correction vanishes on faithful quadratic observations, rather than being
assumed inactive. Rejected observations may leave the anchor unchanged. -/
theorem practical_quadratic_virtual_reference {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g₀ : EuclideanSpace ℝ (Fin n))
    (constant : ℝ) (S : State (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (hg : ∀ i < k, CG.gradient Q g₀ i ≠ 0)
    (hcache : S.gradient = quadraticGradient Q g₀ S.point)
    (hfaithful : ∀ a ∈ S.pairs,
      PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S.point a)
    (hs : LinearIndependent ℝ (storedSteps S.pairs))
    (hspan : Submodule.span ℝ (range (storedSteps S.pairs)) = directionFlag Q g₀ k)
    (hx : S.point ∈ Submodule.span ℝ (range (storedSteps S.pairs)))
    (hcap : S.pairs.length ≤ min S.capacity n) :
    let W := (practicalModel P S).pairs
    let s := storedSteps W
    let y := storedImages W
    let T := selectedModel P W
    S.point + modelVirtualCorrection s T S.gradient = CG.displacement Q g₀ k ∧
      modelVirtualGradient s y T S.gradient = CG.gradient Q g₀ k ∧
      modelDirection s y T S.gradient = CG.direction Q g₀ k := by
  dsimp only
  rw [(practical_quadratic_model_retains P Q hQ hpos g₀ constant S hfaithful hs hcap).1,
    selectedModel_quadratic P Q hQ g₀ constant S.point S.pairs hfaithful]
  exact quadratic_observed_reference Q hQ hpos g₀ constant S k hg hcache hfaithful hs hspan hx

/-- Any supplied missing-direction curvature has the same quadratic CG
decomposition. No exact line minimization or correct curvature estimate is
required for this algebraic identity; a nonzero scalar is needed separately
when applying the existing observed-flag extension theorem. -/
theorem practical_quadratic_trial_reference {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g₀ : EuclideanSpace ℝ (Fin n))
    (constant : ℝ) (S : State (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (hg : ∀ i < k, CG.gradient Q g₀ i ≠ 0)
    (hcache : S.gradient = quadraticGradient Q g₀ S.point)
    (hfaithful : ∀ a ∈ S.pairs,
      PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S.point a)
    (hs : LinearIndependent ℝ (storedSteps S.pairs))
    (hspan : Submodule.span ℝ (range (storedSteps S.pairs)) = directionFlag Q g₀ k)
    (hx : S.point ∈ Submodule.span ℝ (range (storedSteps S.pairs)))
    (hcap : S.pairs.length ≤ min S.capacity n) (curvature : ℝ) :
    let W := (practicalModel P S).pairs
    let s := storedSteps W
    let y := storedImages W
    let T := selectedModel P W
    S.point + modelTrialStep s y T S.gradient curvature =
      CG.displacement Q g₀ k +
        modelTrialLength s y T S.gradient curvature • CG.direction Q g₀ k := by
  have hv := practical_quadratic_virtual_reference P Q hQ hpos g₀ constant S k
    hg hcache hfaithful hs hspan hx hcap
  dsimp only at hv ⊢
  rw [modelTrialStep, ← add_assoc, hv.1, hv.2.2]

/-- The actual full-memory raw practical branch reaches the genuine CG
reference point, independently of the cached scalar or the F switch. The
executor may still apply its safeguard; this theorem does not bypass it. -/
theorem practical_quadratic_full_reference {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g₀ : EuclideanSpace ℝ (Fin n))
    (constant : ℝ) (S : State (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (hg : ∀ i < k, CG.gradient Q g₀ i ≠ 0)
    (hcache : S.gradient = quadraticGradient Q g₀ S.point)
    (hfaithful : ∀ a ∈ S.pairs,
      PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S.point a)
    (hs : LinearIndependent ℝ (storedSteps S.pairs))
    (hspan : Submodule.span ℝ (range (storedSteps S.pairs)) = directionFlag Q g₀ k)
    (hx : S.point ∈ Submodule.span ℝ (range (storedSteps S.pairs)))
    (hcap : S.pairs.length ≤ min S.capacity n) (hn : 0 < n)
    (hfull : (practicalModel P S).pairs.length = n) :
    S.point + (practicalModel P S).direction = CG.displacement Q g₀ k := by
  rw [practicalModel_full P S hn hfull]
  exact (practical_quadratic_virtual_reference P Q hQ hpos g₀ constant S k
    hg hcache hfaithful hs hspan hx hcap).1

end
end krylov.XR
