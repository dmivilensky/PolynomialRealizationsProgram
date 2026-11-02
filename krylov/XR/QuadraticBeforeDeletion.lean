import krylov.XR.QuadraticRun

/-!
Article: main_krylov, thm:XR, literal smaller-memory prefix.
Use: run the real raw outer executor until its first capacity deletion.
Both the first ModelStep and a genuinely reached rejected-probe ModelStep
are covered. Before deletion the only extra condition is the observable
pair-count≤capacity test; real rank/refutation retention and all Krylov
identities are derived from the actual true quadratic observations.
-/
namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference
open scoped InnerProductSpace

/-- The literal outer progress theorem before the first memory deletion;
no full-capacity configuration is required. -/
theorem quadratic_rawOuterAdvance_progress_before_deletion {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (S : State (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : k ≤ n) (hn : 0 < n)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hS : QuadraticEventInvariant Q g₀ constant S k) (hcap : k ≤ S.capacity)
    (hprobeCapacity : k < n → ¬Accepted (quadraticObjective Q g₀ constant) P.armijo S.point S.gradient
      (algorithmModel P S).direction 1 → k+1 ≤ S.capacity)
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
    have ha := quadratic_full_query_accepted P Q hQ hpos g₀ constant S hn hg hterminal hS hcap hne hsigma
    rw [ite_eq_left ha]
    left
    change quadraticGradient Q g₀ (S.point + 1 • (algorithmModel P S).direction) = 0
    simpa only [one_smul] using
      (quadratic_full_query P Q hQ hpos g₀ constant S hn hg hterminal hS hcap).2
  · have hkn : k < n := by omega
    have hfirstTrue := quadraticEventInvariant_step P Q hQ hpos g₀ constant S k hkn
      (fun i hi => hg i (by omega)) hS hcap 1 one_ne_zero true (htrial₀ hkn)
    have hfirstFalse := quadraticEventInvariant_step P Q hQ hpos g₀ constant S k hkn
      (fun i hi => hg i (by omega)) hS hcap 1 one_ne_zero false (htrial₀ hkn)
    split
    · right
      exact ⟨k + 1, by omega, by omega,
        hfirstTrue.applyOuterCounters P n S _ _ _ Q g₀ constant _ _⟩
    · rename_i hreject
      have hprobeCap : k+1 ≤ probe.capacity := hprobeCapacity hkn hreject
      by_cases hlast : k + 1 = n
      · have hfullInv : QuadraticEventInvariant Q g₀ constant probe n :=
          (congrArg (fun j => QuadraticEventInvariant Q g₀ constant probe j) hlast).mp hfirstFalse
        have hpoint := quadratic_full_query P Q hQ hpos g₀ constant probe hn hg hterminal hfullInv (by omega)
        by_cases hprobeZero : probe.gradient = 0
        · exact False.elim (hne hprobeZero)
        · have ha := quadratic_full_query_accepted P Q hQ hpos g₀ constant probe hn hg hterminal
            hfullInv (by omega) hprobeZero hsigma
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
          (fun i hi => hg i (by omega)) hfirstFalse hprobeCap _ hjpos.ne' true (htrial₁ hk₁)
        right
        exact ⟨k + 2, by omega, by omega,
          hsecond.applyOuterCounters P n S _ _ _ Q g₀ constant _ _⟩

/-- Every literal actual outer state before its first capacity deletion
has the genuine quadratic Krylov invariant, with arbitrary smaller memory. -/
theorem quadratic_rawRun_before_first_deletion {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant initialStep : ℝ) (bounds : SpectralBounds)
    (hn : 0 < n) (N : ℕ)
    (hg : ∀ k < n, CG.gradient Q g₀ k ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hsigma : P.armijo < 1 / 2)
    (hnoDeletion : ∀ i < N,
      let S := rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀)
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i
      S.pairs.length ≤ S.capacity ∧
        (¬Accepted (quadraticObjective Q g₀ constant) P.armijo S.point S.gradient
          (algorithmModel P S).direction 1 →
          (rawObservationEvent (algorithmModel P) (quadraticObjective Q g₀ constant)
            (quadraticGradient Q g₀) 1 false S).pairs.length ≤ S.capacity))
    (htrials : ∀ i,
      let S := rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀)
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i
      S.gradient ≠ 0 →
        (S.pairs.length < n → algorithmTrialParameter P S ≠ 0) ∧
        (let probe := rawObservationEvent (algorithmModel P) (quadraticObjective Q g₀ constant)
          (quadraticGradient Q g₀) 1 false S
         probe.pairs.length < n → algorithmTrialParameter P probe ≠ 0)) (i : ℕ) (hi : i ≤ N) :
    let S := rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant)
      (quadraticGradient Q g₀)
      (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i
    S.gradient = 0 ∨ ∃ k, i ≤ k ∧ k ≤ n ∧ QuadraticEventInvariant Q g₀ constant S k := by
  classical
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  let S₀ := initialState P f G 0 initialStep bounds
  let states := rawRun P n (algorithmModel P) f G S₀
  induction i with
  | zero =>
    exact Or.inr ⟨0, le_rfl, Nat.zero_le _, quadraticEventInvariant_initial P Q g₀ constant initialStep bounds⟩
  | succ i ih =>
    have hcount := hnoDeletion i (by omega)
    change (states i).pairs.length ≤ (states i).capacity ∧ _ at hcount
    change (states (i + 1)).gradient = 0 ∨ _
    rcases ih (by omega) with hz | ⟨k, hik, hkn, hS⟩
    · left
      change (states i).gradient = 0 at hz
      change (rawOuterAdvance P n (algorithmModel P) f G (states i)).gradient = 0
      simp only [rawOuterAdvance, ite_eq_left hz]
      exact hz
    · by_cases hz : (states i).gradient = 0
      · left
        change (rawOuterAdvance P n (algorithmModel P) f G (states i)).gradient = 0
        simp only [rawOuterAdvance, ite_eq_left hz]
        exact hz
      · have hc : (states i).pairs.length = k := hS.count
        have hcap_i : k ≤ (states i).capacity := by rw [←hc]; exact hcount.1
        have ht := htrials i hz
        have ht₀ : k < n → algorithmTrialParameter P (states i) ≠ 0 := by
          intro hk
          exact ht.1 (by rw [hS.count]; exact hk)
        have ht₁ : k + 1 < n → algorithmTrialParameter P
            (rawObservationEvent (algorithmModel P) f G 1 false (states i)) ≠ 0 := by
          intro hk
          have hp := quadraticEventInvariant_step P Q hQ hpos g₀ constant (states i) k (by omega)
            (fun j hj => hg j (by omega)) hS hcap_i 1 one_ne_zero false (ht₀ (by omega))
          exact ht.2 (by rw [hp.count]; exact hk)
        have hprobeCapacity (hk : k < n) (hreject : ¬Accepted f P.armijo (states i).point (states i).gradient
            (algorithmModel P (states i)).direction 1) : k+1 ≤ (states i).capacity := by
          have hp := quadraticEventInvariant_step P Q hQ hpos g₀ constant (states i) k hk
            (fun j hj => hg j (by omega)) hS hcap_i 1 one_ne_zero false (ht₀ hk)
          have hh := hcount.2 hreject
          rw [hp.count] at hh
          exact hh
        have hnext := quadratic_rawOuterAdvance_progress_before_deletion P Q hQ hpos g₀ constant
          (states i) k hkn hn hg hterminal hS hcap_i hprobeCapacity hz hsigma ht₀ ht₁
        rcases hnext with hz' | ⟨j, hkj, hjn, hj⟩
        · exact Or.inl hz'
        · exact Or.inr ⟨j, by omega, hjn, hj⟩

/-- Literal smaller-memory XR has all printed quadratic virtual CG
identities until its first actual capacity deletion, including probes. -/
theorem quadratic_rawRun_before_first_deletion_reference {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant initialStep : ℝ) (bounds : SpectralBounds)
    (hn : 0 < n) (N : ℕ)
    (hg : ∀ k < n, CG.gradient Q g₀ k ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hsigma : P.armijo < 1 / 2)
    (hnoDeletion : ∀ i ≤ N,
      let S := rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀)
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i
      S.pairs.length ≤ S.capacity ∧
        (¬Accepted (quadraticObjective Q g₀ constant) P.armijo S.point S.gradient
          (algorithmModel P S).direction 1 →
          (rawObservationEvent (algorithmModel P) (quadraticObjective Q g₀ constant)
            (quadraticGradient Q g₀) 1 false S).pairs.length ≤ S.capacity))
    (htrials : ∀ i,
      let S := rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀)
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i
      S.gradient ≠ 0 →
        (S.pairs.length < n → algorithmTrialParameter P S ≠ 0) ∧
        (let probe := rawObservationEvent (algorithmModel P) (quadraticObjective Q g₀ constant)
          (quadraticGradient Q g₀) 1 false S
         probe.pairs.length < n → algorithmTrialParameter P probe ≠ 0)) (i : ℕ) (hi : i ≤ N) :
    let S := rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant)
      (quadraticGradient Q g₀)
      (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i
    S.gradient = 0 ∨ ∃ k, i ≤ k ∧ k ≤ n ∧ (algorithmModel P S).pairs = S.pairs ∧
      S.point + modelVirtualCorrection (storedSteps S.pairs) (storedModel S.pairs) S.gradient =
        CG.displacement Q g₀ k ∧
      modelVirtualGradient (storedSteps S.pairs) (storedImages S.pairs) (storedModel S.pairs) S.gradient =
        CG.gradient Q g₀ k ∧
      modelDirection (storedSteps S.pairs) (storedImages S.pairs) (storedModel S.pairs) S.gradient =
        CG.direction Q g₀ k ∧ storedValueModel S.pairs = storedModel S.pairs := by
  let S := rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant)
    (quadraticGradient Q g₀)
    (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i
  have hinv := quadratic_rawRun_before_first_deletion P Q hQ hpos g₀ constant initialStep bounds
    hn N hg hterminal hsigma (fun j hj => hnoDeletion j hj.le) htrials i hi
  rcases hinv with hz | ⟨k, hik, hkn, hS⟩
  · exact Or.inl hz
  · have hcap : S.pairs.length ≤ min S.capacity n := by
      exact le_min (hnoDeletion i hi).1 (by rw [hS.count]; exact hkn)
    have hret := quadratic_model_retains P Q hQ hpos g₀ constant S hS.faithful hS.independent hcap
    have hv := quadratic_observed_reference Q hQ hpos g₀ constant S k
      (fun j hj => hg j (hj.trans_le hkn)) hS.gradient hS.faithful hS.independent hS.flag hS.point_mem
    exact Or.inr ⟨k, hik, hkn, hret.1, hv.1, hv.2.1, hv.2.2,
      storedValueModel_quadratic Q hQ g₀ constant S.point S.pairs hS.faithful⟩

end
end krylov.XR
