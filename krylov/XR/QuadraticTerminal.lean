import krylov.XR.QuadraticEventRun
import krylov.Reference.Stopping

/-!
Article: main_krylov, thm:XR, actual full-window terminating evaluation.
Use: show that the next computed unit query after n independent stored
pairs reaches the genuine quadratic critical point, and actual Armijo
accepts it. Source: the true full Galerkin solve, genuine scalar quadratic
trapezoid cancellation and positive curvature.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine nonstationary quadratic step to its true critical point has
actual quotient exactly one, with no acceptance assumption. -/
theorem quadratic_critical_quotient (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g₀ : E) (constant : ℝ)
    (S : State E) (hf : S.value = quadraticObjective Q g₀ constant S.point)
    (hg : S.gradient = quadraticGradient Q g₀ S.point) (hne : S.gradient ≠ 0)
    (u : E) (hcritical : quadraticGradient Q g₀ (S.point + u) = 0) :
    trialQuotient (quadraticObjective Q g₀ constant) S.point S.gradient u 1 = 1 := by
  have hb : S.gradient + Q u = 0 := by
    simpa only [hg, quadraticGradient, map_add, add_assoc] using hcritical
  have hu : u ≠ 0 := by
    intro hz
    rw [hz, map_zero, add_zero] at hb
    exact hne hb
  have hQu : Q u = -S.gradient := eq_neg_of_add_eq_zero_right hb
  have hslope : 0 < -inner ℝ S.gradient u := by
    simpa only [hQu, inner_neg_right, real_inner_comm] using hpos u hu
  have hd := faithful_quadratic_defect Q hQ g₀ constant S.point
    (observedTrialPair (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S u)
    (observedTrialPair_faithful _ _ S hf hg u)
  change quadraticObjective Q g₀ constant (S.point + u) - S.value - inner ℝ S.gradient u -
    inner ℝ u (quadraticGradient Q g₀ (S.point + u) - S.gradient) / 2 = 0 at hd
  rw [hf, hcritical, zero_sub, inner_neg_right, real_inner_comm u S.gradient] at hd
  have hcomm : inner ℝ u S.gradient = inner ℝ S.gradient u := real_inner_comm _ _
  simp only [hcomm] at hd
  unfold trialQuotient
  simp only [one_smul, one_mul, neg_mul]
  have hnum : 2 * (quadraticObjective Q g₀ constant (S.point + u) -
      quadraticObjective Q g₀ constant S.point - inner ℝ S.gradient u) =
        -inner ℝ S.gradient u := by linarith
  rw [hnum, div_self hslope.ne']

/-- Full observed memory removes the new-direction component in the
literal ModelStep, rather than assuming an exact Newton output. -/
theorem algorithmTrialParameter_full {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hp : (algorithmModel P S).pairs.length = n) : algorithmTrialParameter P S = 0 := by
  classical
  unfold algorithmTrialParameter
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_left (Or.inl hp)]

/-- At the full actual quadratic flag the next computed unit evaluation
is the true terminal CG point. The current anchor may be unchanged after
a rejected probe; no sum-of-stored-steps representation is used. -/
theorem quadratic_full_query {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hS : QuadraticEventInvariant Q g₀ constant S n) (hcap : n ≤ S.capacity) :
    S.point + (algorithmModel P S).direction = CG.displacement Q g₀ n ∧
      quadraticGradient Q g₀ (S.point + (algorithmModel P S).direction) = 0 := by
  have hcapacity : S.pairs.length ≤ min S.capacity n := by rw [hS.count]; omega
  have hret := quadratic_model_retains P Q hQ hpos g₀ constant S hS.faithful hS.independent hcapacity
  have hp : (algorithmModel P S).pairs.length = n := by rw [hret.1, hS.count]
  have hu := quadratic_actual_trial P Q hQ hpos g₀ constant S n hg hS.gradient hS.faithful
    hS.independent hS.flag hS.point_mem hS.count hcapacity
  rw [algorithmTrialParameter_full P S hn hp, zero_smul, add_zero] at hu
  have hpoint : S.point + (algorithmModel P S).direction = CG.displacement Q g₀ n := by rw [hu]; abel
  refine ⟨hpoint, ?_⟩
  rw [hpoint]
  change g₀ + Q (CG.displacement Q g₀ n) = 0
  rw [← CG.gradient_displacement, hterminal]

/-- The terminating unit evaluation is actually accepted by the printed
Armijo test whenever sigma<1/2; safeguard and acceptance are not hypotheses. -/
theorem quadratic_full_query_accepted {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hS : QuadraticEventInvariant Q g₀ constant S n) (hcap : n ≤ S.capacity)
    (hne : S.gradient ≠ 0) (hsigma : P.armijo < 1 / 2) :
    Accepted (quadraticObjective Q g₀ constant) P.armijo S.point S.gradient
      (algorithmModel P S).direction 1 := by
  unfold Accepted
  rw [quadratic_critical_quotient Q hQ hpos g₀ constant S hS.value hS.gradient hne _
    (quadratic_full_query P Q hQ hpos g₀ constant S hn hg hterminal hS hcap).2]
  linarith

end
end krylov.XR
