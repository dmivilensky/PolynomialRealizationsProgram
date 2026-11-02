import krylov.XR.PracticalQuadratic
import krylov.XR.PracticalGrowthDictionary
import krylov.XR.QuadraticAlgorithm

/-!
# Computed fresh-secant quadratic trials

Theorem 7.1 (`thm:XR`): the practical policy changes only the actual scalar
multiplying the new conjugate direction. This module exposes that scalar
and proves the literal ModelStep decomposition, including the empty and
full-window branches. No curvature bound or spectral accumulator is used.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference
open scoped InnerProductSpace

/-- The scalar of the new direction in the actual fresh-secant policy. -/
def practicalTrialParameter {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) : ℝ := by
  classical
  let M := practicalModel P S
  let W := M.pairs
  let s := storedSteps W
  let y := storedImages W
  let T := selectedModel P W
  let d := modelDirection s y T S.gradient
  exact if W.length = 0 then M.fallbackCurvature⁻¹
    else if W.length = n then 0
    else modelTrialLength s y T S.gradient (M.fallbackCurvature * ‖d‖ ^ 2)

/-- Every nonempty practical model decomposes into its virtual correction
and the computed scalar times its new direction, without nondegeneracy assumptions. -/
theorem practicalModel_direction_decomposition {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    let M := practicalModel P S
    M.pairs.length ≠ 0 → M.direction =
      modelVirtualCorrection (storedSteps M.pairs) (selectedModel P M.pairs) S.gradient +
        practicalTrialParameter P S • modelDirection (storedSteps M.pairs)
          (storedImages M.pairs) (selectedModel P M.pairs) S.gradient := by
  classical
  dsimp only
  intro hp
  unfold practicalTrialParameter practicalModel at *
  dsimp only at *
  rw [ite_eq_right hp]
  split <;> simp_all only [modelTrialStep, zero_smul, add_zero]

/-- The empty-window practical branch uses its actual inverse fresh scale. -/
theorem practicalModel_empty_direction {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hp : (practicalModel P S).pairs.length = 0) :
    (practicalModel P S).direction = practicalTrialParameter P S • (-S.gradient) := by
  classical
  unfold practicalTrialParameter practicalModel at *
  dsimp only at *
  simp only [hp, ite_true, smul_neg, neg_smul]

/-- Full memory has no new-direction component in the practical policy. -/
theorem practicalTrialParameter_full {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hp : (practicalModel P S).pairs.length = n) : practicalTrialParameter P S = 0 := by
  classical
  unfold practicalTrialParameter
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_left hp]

/-- The actual raw ModelStep, rather than an assumed trial vector, has
the true CG decomposition on every retained nonstagnating quadratic flag. -/
theorem practical_quadratic_actual_trial {n : ℕ} (P : Parameters)
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
    (practicalModel P S).direction = (CG.displacement Q g₀ k - S.point) +
      practicalTrialParameter P S • CG.direction Q g₀ k := by
  have hret := practical_quadratic_model_retains P Q hQ hpos g₀ constant S hfaithful hs hcap
  by_cases hp : S.pairs.length = 0
  · have hk : k = 0 := hcount.symm.trans hp
    have hx0 : S.point = 0 := by
      rw [hspan, hk, directionFlag_zero] at hx
      simpa using hx
    have hp' : (practicalModel P S).pairs.length = 0 := by rw [hret.1, hp]
    rw [practicalModel_empty_direction P S hp', hcache, hx0]
    simp [hk, quadraticGradient, CG.displacement, CG.direction, cgRun]
  · have hp' : (practicalModel P S).pairs.length ≠ 0 := by rw [hret.1]; exact hp
    have hd := practicalModel_direction_decomposition P S hp'
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
