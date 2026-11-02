import krylov.XR.QuadraticEventRun

/-!
Article: main_krylov, thm:XR, arbitrary acceptance and smaller memory.
Use: execute genuine stored observation events with any accepted/rejected
decisions and any capacity schedule. Before the first capacity deletion,
each observed event adds exactly one true Krylov direction and all three
virtual CG identities hold. The schedule includes the actual numeric outer
capacity updates; no Krylov trajectory or successful matrix test is supplied.
Source: the real stored-event induction, which needs only count≤capacity.
-/
namespace krylov.XR
noncomputable section
open Set krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {n : ℕ}

/-- Actual stored-event execution with the capacities chosen after each
event. Unstored later backtracking evaluations leave this data unchanged. -/
def capacityObservationRun (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (length : ℕ → ℝ) (move : ℕ → Bool) (capacity : ℕ → ℕ)
    (S₀ : State (EuclideanSpace ℝ (Fin n))) : ℕ → State (EuclideanSpace ℝ (Fin n))
  | 0 => { S₀ with capacity := capacity 0 }
  | k+1 => { rawObservationEvent (algorithmModel P) f G (length k) (move k)
      (capacityObservationRun P f G length move capacity S₀ k) with capacity := capacity (k+1) }

theorem capacityObservationRun_capacity (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (length : ℕ → ℝ) (move : ℕ → Bool) (capacity : ℕ → ℕ)
    (S₀ : State (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    (capacityObservationRun P f G length move capacity S₀ k).capacity = capacity k := by
  cases k <;> rfl

theorem QuadraticEventInvariant.set_capacity
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (S : State (EuclideanSpace ℝ (Fin n))) (k c : ℕ)
    (hS : QuadraticEventInvariant Q g₀ constant S k) :
    QuadraticEventInvariant Q g₀ constant { S with capacity := c } k :=
  ⟨hS.value, hS.gradient, hS.faithful, hS.independent, hS.flag, hS.point_mem, hS.count⟩

/-- Genuine quadratic induction for any acceptance rule and smaller memory
up to its first capacity deletion. Rank and refutation tests are proved to
retain the window; only the literal pre-deletion count bound is assumed. -/
theorem quadratic_capacity_prefix_invariant (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant initialStep : ℝ) (bounds : SpectralBounds)
    (length : ℕ → ℝ) (move : ℕ → Bool) (capacity : ℕ → ℕ) (N : ℕ) (hN : N ≤ n)
    (hg : ∀ i < N, CG.gradient Q g₀ i ≠ 0)
    (hcapacity : ∀ i < N, i ≤ capacity i)
    (hlength : ∀ i < N, length i ≠ 0)
    (htrial : ∀ i < N, algorithmTrialParameter P
      (capacityObservationRun P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀)
        length move capacity
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i) ≠ 0)
    (k : ℕ) (hk : k ≤ N) :
    QuadraticEventInvariant Q g₀ constant
      (capacityObservationRun P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀)
        length move capacity
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) k) k := by
  induction k with
  | zero =>
    exact (quadraticEventInvariant_initial P Q g₀ constant initialStep bounds).set_capacity
      _ _ _ _ _ (capacity 0)
  | succ k ih =>
    have hkn : k < N := by omega
    have hS := ih (by omega)
    have hs := quadraticEventInvariant_step P Q hQ hpos g₀ constant _ k (by omega)
      (fun i hi => hg i (by omega)) hS
      (by rw [capacityObservationRun_capacity]; exact hcapacity k hkn)
      (length k) (hlength k hkn) (move k) (htrial k hkn)
    exact hs.set_capacity _ _ _ _ _ (capacity (k+1))

/-- All three literal virtual CG identities, exact F-model equality and
actual rank retention hold before the first smaller-memory deletion. -/
theorem quadratic_capacity_prefix_reference (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant initialStep : ℝ) (bounds : SpectralBounds)
    (length : ℕ → ℝ) (move : ℕ → Bool) (capacity : ℕ → ℕ) (N : ℕ) (hN : N ≤ n)
    (hg : ∀ i < N, CG.gradient Q g₀ i ≠ 0)
    (hcapacity : ∀ i ≤ N, i ≤ capacity i)
    (hlength : ∀ i < N, length i ≠ 0)
    (htrial : ∀ i < N, algorithmTrialParameter P
      (capacityObservationRun P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀)
        length move capacity
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i) ≠ 0)
    (k : ℕ) (hk : k ≤ N) :
    let S := capacityObservationRun P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀)
      length move capacity
      (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) k
    (algorithmModel P S).pairs = S.pairs ∧
      S.point + modelVirtualCorrection (storedSteps S.pairs) (storedModel S.pairs) S.gradient =
        CG.displacement Q g₀ k ∧
      modelVirtualGradient (storedSteps S.pairs) (storedImages S.pairs) (storedModel S.pairs) S.gradient =
        CG.gradient Q g₀ k ∧
      modelDirection (storedSteps S.pairs) (storedImages S.pairs) (storedModel S.pairs) S.gradient =
        CG.direction Q g₀ k ∧ storedValueModel S.pairs = storedModel S.pairs := by
  let S := capacityObservationRun P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀)
    length move capacity
    (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) k
  have hS := quadratic_capacity_prefix_invariant P Q hQ hpos g₀ constant initialStep bounds
    length move capacity N hN hg (fun i hi => hcapacity i hi.le) hlength htrial k hk
  have hret := quadratic_model_retains P Q hQ hpos g₀ constant S hS.faithful hS.independent (by
    rw [hS.count, capacityObservationRun_capacity]
    exact le_min (hcapacity k hk) (hk.trans hN))
  have hv := quadratic_observed_reference Q hQ hpos g₀ constant S k
    (fun i hi => hg i (hi.trans_le hk)) hS.gradient hS.faithful hS.independent hS.flag hS.point_mem
  exact ⟨hret.1, hv.1, hv.2.1, hv.2.2,
    storedValueModel_quadratic Q hQ g₀ constant S.point S.pairs hS.faithful⟩

end
end krylov.XR
