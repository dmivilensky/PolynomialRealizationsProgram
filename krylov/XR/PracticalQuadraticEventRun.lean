import krylov.XR.PracticalQuadraticEvent

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
/-- The full Krylov basis is proved for the actual event recursion,
including arbitrary rejected probes and arbitrary nonzero outer lengths. -/
theorem practical_quadratic_observation_run_invariant {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant initialStep : ℝ) (bounds : SpectralBounds)
    (hinitial : P.initialCapacity = n) (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0)
    (length : ℕ → ℝ) (move : ℕ → Bool)
    (hlength : ∀ i < n, length i ≠ 0)
    (htrial : ∀ i < n, practicalTrialParameter P
      (rawObservationRun (practicalModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) length move
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i) ≠ 0)
    (k : ℕ) (hk : k ≤ n) :
    QuadraticEventInvariant Q g₀ constant
      (rawObservationRun (practicalModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) length move
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) k) k := by
  induction k with
  | zero => exact quadraticEventInvariant_initial P Q g₀ constant initialStep bounds
  | succ k ih =>
    have hkn : k < n := by omega
    have hcap := rawObservationRun_capacity (practicalModel P)
      (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) length move
      (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) k
    change _ = P.initialCapacity at hcap
    rw [hinitial] at hcap
    exact practicalQuadraticEventInvariant_step P Q hQ hpos g₀ constant _ k hkn
      (fun i hi => hg i (by omega)) (ih (by omega)) (by rw [hcap]; omega)
      (length k) (hlength k hkn) (move k) (htrial k hkn)

/-- All three true CG identities and the equality TF=Tbar hold on the
actually computed full stored-event prefix. This statement includes the
state immediately after a rejected probe. -/
theorem practical_quadratic_observation_run_reference {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant initialStep : ℝ) (bounds : SpectralBounds)
    (hinitial : P.initialCapacity = n) (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0)
    (length : ℕ → ℝ) (move : ℕ → Bool)
    (hlength : ∀ i < n, length i ≠ 0)
    (htrial : ∀ i < n, practicalTrialParameter P
      (rawObservationRun (practicalModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) length move
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i) ≠ 0)
    (k : ℕ) (hk : k ≤ n) :
    let S := rawObservationRun (practicalModel P) (quadraticObjective Q g₀ constant)
      (quadraticGradient Q g₀) length move
      (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) k
    S.point + modelVirtualCorrection (storedSteps S.pairs) (storedModel S.pairs) S.gradient =
        CG.displacement Q g₀ k ∧
      modelVirtualGradient (storedSteps S.pairs) (storedImages S.pairs) (storedModel S.pairs) S.gradient =
        CG.gradient Q g₀ k ∧
      modelDirection (storedSteps S.pairs) (storedImages S.pairs) (storedModel S.pairs) S.gradient =
        CG.direction Q g₀ k ∧ storedValueModel S.pairs = storedModel S.pairs := by
  let S := rawObservationRun (practicalModel P) (quadraticObjective Q g₀ constant)
    (quadraticGradient Q g₀) length move
    (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) k
  have hS := practical_quadratic_observation_run_invariant P Q hQ hpos g₀ constant initialStep bounds
    hinitial hg length move hlength htrial k hk
  have hv := quadratic_observed_reference Q hQ hpos g₀ constant S k
    (fun i hi => hg i (hi.trans_le hk)) hS.gradient hS.faithful hS.independent hS.flag hS.point_mem
  exact ⟨hv.1, hv.2.1, hv.2.2, storedValueModel_quadratic Q hQ g₀ constant S.point S.pairs hS.faithful⟩

end
end krylov.XR
