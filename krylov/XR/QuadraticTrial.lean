import krylov.XR.QuadraticObservedFlag

/-!
Article: main_krylov, thm:XR, literal computed quadratic trials.
Use: identify the actual data-only ModelStep displacement with its true
CG flag decomposition. The only nondegeneracy condition on a trial is the
printed nonzero scalar; it is not an assumed flag-growth condition.
Source: the original XR branch definitions and proved Galerkin identities.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference
open scoped InnerProductSpace

/-- The actual scalar multiplying the new direction in the computed raw
ModelStep. The full/zero-direction branch has no new trial component. -/
def algorithmTrialParameter {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) : ℝ := by
  classical
  let M := algorithmModel P S
  let W := M.pairs
  let s := storedSteps W
  let y := storedImages W
  let T := selectedModel P W
  let d := modelDirection s y T S.gradient
  exact if W.length = 0 then
      match M.bounds with | none => S.initialStep | some b => 2 / (b.1 + b.2)
    else if W.length = n ∨ d = 0 then 0
    else modelTrialLength s y T S.gradient
      (observedTrialCurvature P W (storedModel W) d
        (M.bounds.getD (M.fallbackCurvature, M.fallbackCurvature)))

/-- Any nonempty actually retained model is exactly its computed block
trial, including the full and zero-direction window-only cases. -/
theorem algorithmModel_direction_decomposition {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    let M := algorithmModel P S
    M.pairs.length ≠ 0 → M.direction =
      modelVirtualCorrection (storedSteps M.pairs) (selectedModel P M.pairs) S.gradient +
        algorithmTrialParameter P S • modelDirection (storedSteps M.pairs)
          (storedImages M.pairs) (selectedModel P M.pairs) S.gradient := by
  classical
  dsimp only
  intro hp
  unfold algorithmTrialParameter algorithmModel at *
  dsimp only at *
  rw [ite_eq_right hp]
  simp only [modelDirection, modelVirtualGradient, modelVirtualCorrection, modelTrialLength]
  split <;> simp_all only [zero_smul, add_zero]

/-- The genuine empty-window branch has precisely its computed scalar
times the negative cached gradient. -/
theorem algorithmModel_empty_direction {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hp : (algorithmModel P S).pairs.length = 0) :
    (algorithmModel P S).direction = algorithmTrialParameter P S • (-S.gradient) := by
  classical
  unfold algorithmTrialParameter algorithmModel at *
  dsimp only at *
  simp only [hp, ite_true, smul_neg, neg_smul]
  rfl

/-- The actual raw ModelStep, rather than an assumed trial vector, has
the true CG decomposition on every retained nonstagnating quadratic flag. -/
theorem quadratic_actual_trial {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ) (S : State (EuclideanSpace ℝ (Fin n)))
    (k : ℕ) (hg : ∀ i < k, CG.gradient Q g₀ i ≠ 0)
    (hcache : S.gradient = quadraticGradient Q g₀ S.point)
    (hfaithful : ∀ a ∈ S.pairs,
      PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S.point a)
    (hs : LinearIndependent ℝ (storedSteps S.pairs))
    (hspan : Submodule.span ℝ (range (storedSteps S.pairs)) = directionFlag Q g₀ k)
    (hx : S.point ∈ Submodule.span ℝ (range (storedSteps S.pairs)))
    (hcount : S.pairs.length = k) (hcap : S.pairs.length ≤ min S.capacity n) :
    (algorithmModel P S).direction = (CG.displacement Q g₀ k - S.point) +
      algorithmTrialParameter P S • CG.direction Q g₀ k := by
  have hret := quadratic_model_retains P Q hQ hpos g₀ constant S hfaithful hs hcap
  by_cases hp : S.pairs.length = 0
  · have hk : k = 0 := hcount.symm.trans hp
    have hx0 : S.point = 0 := by
      rw [hspan, hk, directionFlag_zero] at hx
      simpa using hx
    have hp' : (algorithmModel P S).pairs.length = 0 := by rw [hret.1, hp]
    rw [algorithmModel_empty_direction P S hp', hcache, hx0]
    simp [hk, quadraticGradient, CG.displacement, CG.direction, cgRun]
  · have hp' : (algorithmModel P S).pairs.length ≠ 0 := by rw [hret.1]; exact hp
    have hd := algorithmModel_direction_decomposition P S hp'
    rw [hret.1, selectedModel_quadratic P Q hQ g₀ constant S.point S.pairs hfaithful] at hd
    have hv := quadratic_observed_reference Q hQ hpos g₀ constant S k hg hcache hfaithful hs hspan hx
    have hc : modelVirtualCorrection (storedSteps S.pairs) (storedModel S.pairs) S.gradient =
        CG.displacement Q g₀ k - S.point := by
      rw [← hv.1]
      abel
    rw [hc, hv.2.2] at hd
    exact hd

end
end krylov.XR
