import krylov.XR.QuadraticOuterEvents
import krylov.XR.QuadraticTerminal

/-!
Article: main_krylov, thm:XR, genuine raw outer-iteration invariant.
Use: transport the proved stored-event invariant through the literal
one-probe/backtracking outer step, including a rejected n-th pair followed
by the actual full-model terminating query. Source: exact executor
decomposition, positive quadratic secants and the true full Galerkin solve.
-/

namespace krylov.XR
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Outer counter bookkeeping changes none of the genuine quadratic flag
certificate: the proof does not identify counters with oracle data. -/
theorem QuadraticEventInvariant.applyOuterCounters (P : Parameters) (dimension : ℕ)
    (S : State E) (p o j : ℕ) (Q : E →L[ℝ] E) (g₀ : E) (constant : ℝ)
    (result : State E) (k : ℕ) (h : QuadraticEventInvariant Q g₀ constant result k) :
    QuadraticEventInvariant Q g₀ constant (applyOuterCounters P dimension S p o j result) k :=
  ⟨h.value, h.gradient, h.faithful, h.independent, h.flag, h.point_mem, h.count⟩

/-- Full configured memory stays full on the literal raw outer executor. -/
theorem rawOuterAdvance_capacity_full (P : Parameters) (n : ℕ)
    (hinitial : P.initialCapacity = n) (hmaximum : P.maximumCapacity = n)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (S : State E) (hcap : S.capacity = n) :
    (rawOuterAdvance P n model f G S).capacity = n := by
  classical
  unfold rawOuterAdvance
  split
  · exact hcap
  · dsimp only
    rw [hcap]
    exact updateCapacity_full P n _ _ _ _ hinitial hmaximum

/-- Every actual nonstopped raw outer iteration either reaches the true
critical point or strictly increases the genuine observed Krylov dimension.
The nonzero scalar assumptions are precisely the printed trial restriction,
including the recomputed trial after a rejected probe. -/
theorem quadratic_rawOuterAdvance_progress {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (S : State (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : k ≤ n) (hn : 0 < n)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hS : QuadraticEventInvariant Q g₀ constant S k) (hcap : S.capacity = n)
    (hne : S.gradient ≠ 0) (hsigma : P.armijo < 1 / 2)
    (htrial₀ : k < n → algorithmTrialParameter P S ≠ 0)
    (htrial₁ : k + 1 < n → algorithmTrialParameter P
      (rawObservationEvent (algorithmModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) 1 false S) ≠ 0) :
    let result := rawOuterAdvance P n (algorithmModel P)
      (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S
    result.gradient = 0 ∨ ∃ j, k < j ∧ j ≤ n ∧ QuadraticEventInvariant Q g₀ constant result j := by
  classical
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  let probe := rawObservationEvent (algorithmModel P) f G 1 false S
  rw [rawOuterAdvance_event_decomposition, ite_eq_right hne]
  dsimp only
  by_cases hfull : k = n
  · subst k
    have ha := quadratic_full_query_accepted P Q hQ hpos g₀ constant S hn hg hterminal hS hcap.ge hne hsigma
    rw [ite_eq_left ha]
    left
    change quadraticGradient Q g₀ (S.point + 1 • (algorithmModel P S).direction) = 0
    simpa only [one_smul] using
      (quadratic_full_query P Q hQ hpos g₀ constant S hn hg hterminal hS hcap.ge).2
  · have hkn : k < n := by omega
    have hfirstTrue := quadraticEventInvariant_step P Q hQ hpos g₀ constant S k hkn
      (fun i hi => hg i (by omega)) hS (by rw [hcap]; omega) 1 one_ne_zero true (htrial₀ hkn)
    have hfirstFalse := quadraticEventInvariant_step P Q hQ hpos g₀ constant S k hkn
      (fun i hi => hg i (by omega)) hS (by rw [hcap]; omega) 1 one_ne_zero false (htrial₀ hkn)
    split
    · right
      exact ⟨k + 1, by omega, by omega,
        hfirstTrue.applyOuterCounters P n S _ _ _ Q g₀ constant _ _⟩
    · have hprobeCap : probe.capacity = n := hcap
      by_cases hlast : k + 1 = n
      · have hfullInv : QuadraticEventInvariant Q g₀ constant probe n :=
          (congrArg (fun j => QuadraticEventInvariant Q g₀ constant probe j) hlast).mp hfirstFalse
        have hpoint := quadratic_full_query P Q hQ hpos g₀ constant probe hn hg hterminal hfullInv hprobeCap.ge
        by_cases hprobeZero : probe.gradient = 0
        · exact False.elim (hne hprobeZero)
        · have ha := quadratic_full_query_accepted P Q hQ hpos g₀ constant probe hn hg hterminal
            hfullInv hprobeCap.ge hprobeZero hsigma
          have hj : backtrackingIndex f P.armijo S.point S.gradient (algorithmModel P probe).direction = 0 := by
            unfold backtrackingIndex
            have hex : ∃ j, Accepted f P.armijo S.point S.gradient (algorithmModel P probe).direction
                (backtrackingSteps f S.point S.gradient (algorithmModel P probe).direction j) := ⟨0, ha⟩
            rw [dite_eq_left hex]
            exact Nat.eq_zero_of_le_zero (Nat.find_min' hex ha)
          rw [hj]
          left
          change G (probe.point + 1 • (algorithmModel P probe).direction) = 0
          simpa only [one_smul] using hpoint.2
      · have hk₁ : k + 1 < n := by omega
        have hjpos := (backtrackingSteps_bounds f S.point S.gradient
          (algorithmModel P probe).direction
          (backtrackingIndex f P.armijo S.point S.gradient (algorithmModel P probe).direction)).1
        have hsecond := quadraticEventInvariant_step P Q hQ hpos g₀ constant probe (k + 1) hk₁
          (fun i hi => hg i (by omega)) hfirstFalse (by rw [hprobeCap]; omega) _ hjpos.ne' true (htrial₁ hk₁)
        right
        exact ⟨k + 2, by omega, by omega,
          hsecond.applyOuterCounters P n S _ _ _ Q g₀ constant _ _⟩

end
end krylov.XR
