import krylov.XR.LocalNativeChart
import krylov.XR.QuadraticOuterInvariant

/-!
Article: main_krylov, lem:xr-local, genuine quadratic reference domains.
Use: derive the full observed Krylov invariant of the actual full-memory
virtual executor, before continuity is applied. Nonzero primitive trials
are the source restriction; no rank, gate success or CG trajectory is an
executor assumption. Source: proved genuine stored-event flag extension.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {n : ℕ}

/-- The literal full virtual executor keeps its configured full capacity,
independently of any oracle or acceptance theorem. -/
theorem fullVirtualRun_capacity_full (P : Parameters)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (trial : State (EuclideanSpace ℝ (Fin n)) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (k : ℕ) :
    (fullVirtualRun P trial f G x₀ bounds k).capacity = n := by
  induction k with
  | zero => exact hinit
  | succ k ih =>
    change (updateCapacity P n (fullVirtualRun P trial f G x₀ bounds k).capacity
      (fullVirtualRun P trial f G x₀ bounds k).cleanCount
      (fullVirtualRun P trial f G x₀ bounds k).pairs.length 0 1).1 = n
    rw [ih]
    exact updateCapacity_full P n _ _ _ _ hinit hmax

/-- Every exact endpoint-value virtual model of a true quadratic is the
ordinary observed model, for either value flag. -/
theorem fullVirtualSelectedModel_quadratic (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (W : List (PairObservation (EuclideanSpace ℝ (Fin n))))
    (hW : ∀ a ∈ W, PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) x a) :
    fullVirtualSelectedModel P W = storedModel W := by
  have hd (i : Fin W.length) : (W.get i).valueDefect = 0 :=
    faithful_quadratic_defect Q hQ g₀ constant x _ (hW _ (List.get_mem W i))
  unfold fullVirtualSelectedModel storedExactValueModel
  simp only [hd, mul_zero, diagonal_zero, sub_zero, ite_self]

/-- A full virtual quadratic update is one genuine accepted stored event
with only the prescribed outer counters applied afterward. This equality
is algebraic and makes no Armijo or safeguard hypothesis. -/
theorem fullVirtualAdvance_quadratic_event (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (S : State (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : k < n)
    (hg : ∀ i ≤ k, CG.gradient Q g₀ i ≠ 0)
    (hS : QuadraticEventInvariant Q g₀ constant S k) (hcap : k ≤ S.capacity)
    (htrial : algorithmTrialParameter P S ≠ 0) :
    fullVirtualAdvance P (algorithmTrialParameter P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) S =
      applyOuterCounters P n S S.pairs.length 0 1
        (rawObservationEvent (algorithmModel P) (quadraticObjective Q g₀ constant)
          (quadraticGradient Q g₀) 1 true S) := by
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  have hcapacity : S.pairs.length ≤ min S.capacity n := by rw [hS.count]; omega
  have hret := quadratic_model_retains P Q hQ hpos g₀ constant S hS.faithful hS.independent hcapacity
  have hd : (algorithmModel P S).direction = fullVirtualStep P (algorithmTrialParameter P) S :=
    algorithmModel_direction_eq_fullVirtual_of_model P S hret.1 (by
      rw [selectedModel_quadratic P Q hQ g₀ constant S.point S.pairs hS.faithful,
        fullVirtualSelectedModel_quadratic P Q hQ g₀ constant S.point S.pairs hS.faithful])
  have hu := quadratic_actual_trial P Q hQ hpos g₀ constant S k
    (fun i hi => hg i hi.le) hS.gradient hS.faithful hS.independent hS.flag hS.point_mem hS.count hcapacity
  have hnew : (algorithmModel P S).direction ∉ directionFlag Q g₀ k := by
    have hh := quadratic_observed_step_new Q hQ hpos g₀ k (fun i hi => hg i hi.le) (hg k le_rfl)
      S.point (hS.flag ▸ hS.point_mem) (algorithmTrialParameter P S) 1 htrial one_ne_zero
    simpa only [one_smul, ← hu] using hh
  have hne : (algorithmModel P S).direction ≠ 0 := by
    intro hz
    exact hnew (hz ▸ (directionFlag Q g₀ k).zero_mem)
  have happend : appendPositive (algorithmModel P S).pairs
      (observedTrialPair f G S (algorithmModel P S).direction) =
      S.pairs ++ [observedTrialPair f G S (algorithmModel P S).direction] := by
    rw [hret.1]
    exact appendPositive_quadratic Q hpos g₀ f S hS.gradient S.pairs _ hne
  have hb : (algorithmModel P S).bounds = fullVirtualBounds P S := by
    rw [algorithmModel_bounds, hret.1]
    rfl
  simp only [fullVirtualAdvance, applyOuterCounters, rawObservationEvent, one_smul, ite_true,
    ModelResult.updateState]
  rw [happend, hb, hd]

/-- The full actual virtual quadratic trajectory has the genuine Krylov
flag and both observed inverse domains through every preterminal query.
No successful test, independence or desired trajectory is assumed. -/
theorem fullVirtualRun_quadratic_invariant (P : Parameters)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ) (bounds : SpectralBounds)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0)
    (htrial : ∀ k < n, algorithmTrialParameter P
      (fullVirtualRun P (algorithmTrialParameter P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) 0 bounds k) ≠ 0)
    (k : ℕ) (hk : k ≤ n) :
    QuadraticEventInvariant Q g₀ constant
      (fullVirtualRun P (algorithmTrialParameter P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) 0 bounds k) k := by
  induction k with
  | zero =>
    exact quadraticEventInvariant_initial P Q g₀ constant _ bounds
  | succ k ih =>
    have hkn : k < n := by omega
    let S := fullVirtualRun P (algorithmTrialParameter P) (quadraticObjective Q g₀ constant)
      (quadraticGradient Q g₀) 0 bounds k
    have hS := ih (by omega)
    have hcap : k ≤ S.capacity := by
      rw [fullVirtualRun_capacity_full P hinit hmax]
      omega
    have hraw := quadraticEventInvariant_step P Q hQ hpos g₀ constant S k hkn
      (fun i hi => hg i (by omega)) hS hcap 1 one_ne_zero true (htrial k hkn)
    rw [fullVirtualRun, fullVirtualAdvance_quadratic_event P Q hQ hpos g₀ constant S k hkn
      (fun i hi => hg i (by omega)) hS hcap (htrial k hkn)]
    exact hraw.applyOuterCounters P n S S.pairs.length 0 1 Q g₀ constant _ _

end
end krylov.XR
