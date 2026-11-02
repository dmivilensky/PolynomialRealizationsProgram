import krylov.XR.PracticalQuadraticTerminal

/-!
# Fresh-secant quadratic execution

Theorem 7.1 (`thm:XR`): the actual fresh-secant ModelStep inherits the
proved Krylov induction for nonzero computed trial scalars. Accepted and
rejected oracle observations retain their genuine caches and transported
secants. The full-window query is proved separately from its Armijo
acceptance. Raw outer recursion below uses the executor's totalized search
index; its algebraic identities do not assert search existence for an
arbitrary trial policy. Source: the generic quadratic event/flag argument.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference
open scoped InnerProductSpace
/-- Every actual nonstopped raw outer iteration either reaches the true
critical point or strictly increases the genuine observed Krylov dimension.
The nonzero scalar assumptions are precisely the printed trial restriction,
including the recomputed trial after a rejected probe. -/
theorem practical_quadratic_rawOuterAdvance_progress {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (S : State (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : k ≤ n) (hn : 0 < n)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hS : QuadraticEventInvariant Q g₀ constant S k) (hcap : S.capacity = n)
    (hne : S.gradient ≠ 0) (hsigma : P.armijo < 1 / 2)
    (htrial₀ : k < n → practicalTrialParameter P S ≠ 0)
    (htrial₁ : k + 1 < n → practicalTrialParameter P
      (rawObservationEvent (practicalModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) 1 false S) ≠ 0) :
    let result := rawOuterAdvance P n (practicalModel P)
      (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S
    result.gradient = 0 ∨ ∃ j, k < j ∧ j ≤ n ∧ QuadraticEventInvariant Q g₀ constant result j := by
  classical
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  let probe := rawObservationEvent (practicalModel P) f G 1 false S
  rw [rawOuterAdvance_event_decomposition, ite_eq_right hne]
  dsimp only
  by_cases hfull : k = n
  · subst k
    have ha := practical_quadratic_full_query_accepted P Q hQ hpos g₀ constant S hn hg hterminal hS hcap.ge hne hsigma
    rw [ite_eq_left ha]
    left
    change quadraticGradient Q g₀ (S.point + 1 • (practicalModel P S).direction) = 0
    simpa only [one_smul] using
      (practical_quadratic_full_query P Q hQ hpos g₀ constant S hn hg hterminal hS hcap.ge).2
  · have hkn : k < n := by omega
    have hfirstTrue := practicalQuadraticEventInvariant_step P Q hQ hpos g₀ constant S k hkn
      (fun i hi => hg i (by omega)) hS (by rw [hcap]; omega) 1 one_ne_zero true (htrial₀ hkn)
    have hfirstFalse := practicalQuadraticEventInvariant_step P Q hQ hpos g₀ constant S k hkn
      (fun i hi => hg i (by omega)) hS (by rw [hcap]; omega) 1 one_ne_zero false (htrial₀ hkn)
    split
    · right
      exact ⟨k + 1, by omega, by omega,
        hfirstTrue.applyOuterCounters P n S _ _ _ Q g₀ constant _ _⟩
    · have hprobeCap : probe.capacity = n := hcap
      by_cases hlast : k + 1 = n
      · have hfullInv : QuadraticEventInvariant Q g₀ constant probe n :=
          (congrArg (fun j => QuadraticEventInvariant Q g₀ constant probe j) hlast).mp hfirstFalse
        have hpoint := practical_quadratic_full_query P Q hQ hpos g₀ constant probe hn hg hterminal hfullInv hprobeCap.ge
        by_cases hprobeZero : probe.gradient = 0
        · exact False.elim (hne hprobeZero)
        · have ha := practical_quadratic_full_query_accepted P Q hQ hpos g₀ constant probe hn hg hterminal
            hfullInv hprobeCap.ge hprobeZero hsigma
          have hj : backtrackingIndex f P.armijo S.point S.gradient (practicalModel P probe).direction = 0 := by
            unfold backtrackingIndex
            have hex : ∃ j, Accepted f P.armijo S.point S.gradient (practicalModel P probe).direction
                (backtrackingSteps f S.point S.gradient (practicalModel P probe).direction j) := ⟨0, ha⟩
            rw [dite_eq_left hex]
            exact Nat.eq_zero_of_le_zero (Nat.find_min' hex ha)
          rw [hj]
          left
          change G (probe.point + 1 • (practicalModel P probe).direction) = 0
          simpa only [one_smul] using hpoint.2
      · have hk₁ : k + 1 < n := by omega
        have hjpos := (backtrackingSteps_bounds f S.point S.gradient
          (practicalModel P probe).direction
          (backtrackingIndex f P.armijo S.point S.gradient (practicalModel P probe).direction)).1
        have hsecond := practicalQuadraticEventInvariant_step P Q hQ hpos g₀ constant probe (k + 1) hk₁
          (fun i hi => hg i (by omega)) hfirstFalse (by rw [hprobeCap]; omega) _ hjpos.ne' true (htrial₁ hk₁)
        right
        exact ⟨k + 2, by omega, by omega,
          hsecond.applyOuterCounters P n S _ _ _ Q g₀ constant _ _⟩

end
end krylov.XR
