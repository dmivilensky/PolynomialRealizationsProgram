import krylov.XR.PracticalQuadraticEventRun

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
/-- At the full actual quadratic flag the next computed unit evaluation
is the true terminal CG point. The current anchor may be unchanged after
a rejected probe; no sum-of-stored-steps representation is used. -/
theorem practical_quadratic_full_query {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hS : QuadraticEventInvariant Q g₀ constant S n) (hcap : n ≤ S.capacity) :
    S.point + (practicalModel P S).direction = CG.displacement Q g₀ n ∧
      quadraticGradient Q g₀ (S.point + (practicalModel P S).direction) = 0 := by
  have hcapacity : S.pairs.length ≤ min S.capacity n := by rw [hS.count]; omega
  have hret := practical_quadratic_model_retains P Q hQ hpos g₀ constant S hS.faithful hS.independent hcapacity
  have hp : (practicalModel P S).pairs.length = n := by rw [hret.1, hS.count]
  have hu := practical_quadratic_actual_trial P Q hQ hpos g₀ constant S n hg hS.gradient hS.faithful
    hS.independent hS.flag hS.point_mem hS.count hcapacity
  rw [practicalTrialParameter_full P S hn hp, zero_smul, add_zero] at hu
  have hpoint : S.point + (practicalModel P S).direction = CG.displacement Q g₀ n := by rw [hu]; abel
  refine ⟨hpoint, ?_⟩
  rw [hpoint]
  change g₀ + Q (CG.displacement Q g₀ n) = 0
  rw [← CG.gradient_displacement, hterminal]

/-- The terminating unit evaluation is actually accepted by the printed
Armijo test whenever sigma<1/2; safeguard and acceptance are not hypotheses. -/
theorem practical_quadratic_full_query_accepted {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hS : QuadraticEventInvariant Q g₀ constant S n) (hcap : n ≤ S.capacity)
    (hne : S.gradient ≠ 0) (hsigma : P.armijo < 1 / 2) :
    Accepted (quadraticObjective Q g₀ constant) P.armijo S.point S.gradient
      (practicalModel P S).direction 1 := by
  unfold Accepted
  rw [quadratic_critical_quotient Q hQ hpos g₀ constant S hS.value hS.gradient hne _
    (practical_quadratic_full_query P Q hQ hpos g₀ constant S hn hg hterminal hS hcap).2]
  linarith

/-- Theorem 7.1 (`thm:XR`), the full literal practical event trajectory.
For any acceptance decisions and nonzero observation lengths, the first
`n` nonzero computed trials build the actual full faithful Krylov window.
The next raw unit query is the true minimizer. Acceptance of that query
is a separate conclusion of the Armijo parameter restriction. -/
theorem practical_quadratic_observation_run_terminal {n : ℕ} (P : Parameters)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant initialStep : ℝ) (bounds : SpectralBounds)
    (hinitial : P.initialCapacity = n) (hn : 0 < n)
    (hatoms : referenceAtomCount base hb g₀ = n)
    (length : ℕ → ℝ) (move : ℕ → Bool)
    (hlength : ∀ i < n, length i ≠ 0)
    (htrial : ∀ i < n, practicalTrialParameter P
      (rawObservationRun (practicalModel P) (quadraticObjective (cgOperator base) g₀ constant)
        (quadraticGradient (cgOperator base) g₀) length move
        (initialState P (quadraticObjective (cgOperator base) g₀ constant)
          (quadraticGradient (cgOperator base) g₀) 0 initialStep bounds) i) ≠ 0) :
    let Q := cgOperator base
    let f := quadraticObjective Q g₀ constant
    let G := quadraticGradient Q g₀
    let S := rawObservationRun (practicalModel P) f G length move
      (initialState P f G 0 initialStep bounds) n
    S.pairs.length = n ∧ (practicalModel P S).pairs = S.pairs ∧
      (practicalModel P S).deletedByTest = 0 ∧
      S.point + (practicalModel P S).direction = CG.displacement Q g₀ n ∧
      G (S.point + (practicalModel P S).direction) = 0 ∧
      (S.gradient ≠ 0 → P.armijo < 1 / 2 →
        Accepted f P.armijo S.point S.gradient (practicalModel P S).direction 1) := by
  let Q := cgOperator base
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  let S := rawObservationRun (practicalModel P) f G length move
    (initialState P f G 0 initialStep bounds) n
  have hQ := cgOperator_positive base hb
  have hg : ∀ k < n, CG.gradient Q g₀ k ≠ 0 := by
    simpa only [hatoms] using cg_nonstagnation base hb g₀
  have ht : CG.gradient Q g₀ n = 0 := by
    simpa only [hatoms] using cg_terminates base hb g₀
  have hS : QuadraticEventInvariant Q g₀ constant S n :=
    practical_quadratic_observation_run_invariant P Q hQ.1 hQ.2 g₀ constant initialStep bounds
      hinitial hg length move hlength htrial n le_rfl
  have hc : S.capacity = n := (rawObservationRun_capacity (practicalModel P) f G length move
    (initialState P f G 0 initialStep bounds) n).trans hinitial
  have hr := practical_quadratic_model_retains P Q hQ.1 hQ.2 g₀ constant S
    hS.faithful hS.independent (by rw [hS.count, hc]; omega)
  have hq := practical_quadratic_full_query P Q hQ.1 hQ.2 g₀ constant S hn hg ht hS hc.ge
  exact ⟨hS.count, hr.1, hr.2.2, hq.1, hq.2, fun hne hsigma =>
    practical_quadratic_full_query_accepted P Q hQ.1 hQ.2 g₀ constant S hn hg ht hS hc.ge hne hsigma⟩

end
end krylov.XR
