import krylov.XR.QuadraticOuterInvariant

/-!
Article: main_krylov, thm:XR, complete literal raw quadratic execution.
Use: derive the actual full Krylov invariant and finite terminating query
for rawRun, including stored rejected probes. Nonzero computed trial
scalars are the theorem's original restriction; no retention, acceptance,
CG trajectory or desired output is assumed. Source: genuine event/outer
executor identities and the proved quadratic progress alternative.
-/

namespace krylov.XR
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The full-memory configuration retains its literal capacity throughout
actual raw execution, including rejected-probe and stopped branches. -/
theorem rawRun_capacity_full (P : Parameters) (n : ℕ)
    (hinitial : P.initialCapacity = n) (hmaximum : P.maximumCapacity = n)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (S₀ : State E) (hcap : S₀.capacity = n) (i : ℕ) :
    (rawRun P n model f G S₀ i).capacity = n := by
  induction i with
  | zero => exact hcap
  | succ i ih => exact rawOuterAdvance_capacity_full P n hinitial hmaximum model f G _ ih

/-- Every actual nonterminated raw outer state has an independent faithful
Krylov basis. Its count grows at least once per nonterminated outer step;
a rejected probe can grow it twice. -/
theorem quadratic_rawRun_invariant {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant initialStep : ℝ) (bounds : SpectralBounds)
    (hinitial : P.initialCapacity = n) (hmaximum : P.maximumCapacity = n) (hn : 0 < n)
    (hg : ∀ k < n, CG.gradient Q g₀ k ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hsigma : P.armijo < 1 / 2)
    (htrials : ∀ i,
      let S := rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀)
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i
      S.gradient ≠ 0 →
        (S.pairs.length < n → algorithmTrialParameter P S ≠ 0) ∧
        (let probe := rawObservationEvent (algorithmModel P) (quadraticObjective Q g₀ constant)
          (quadraticGradient Q g₀) 1 false S
         probe.pairs.length < n → algorithmTrialParameter P probe ≠ 0)) (i : ℕ) :
    let S := rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant)
      (quadraticGradient Q g₀)
      (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i
    S.gradient = 0 ∨ ∃ k, i ≤ k ∧ k ≤ n ∧ QuadraticEventInvariant Q g₀ constant S k := by
  classical
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  let S₀ := initialState P f G 0 initialStep bounds
  let states := rawRun P n (algorithmModel P) f G S₀
  have hcap j : (states j).capacity = n :=
    rawRun_capacity_full P n hinitial hmaximum _ f G S₀ hinitial j
  induction i with
  | zero =>
    exact Or.inr ⟨0, le_rfl, Nat.zero_le _, quadraticEventInvariant_initial P Q g₀ constant initialStep bounds⟩
  | succ i ih =>
    change (states (i + 1)).gradient = 0 ∨ _
    rcases ih with hz | ⟨k, hik, hkn, hS⟩
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
      · have ht := htrials i hz
        have ht₀ : k < n → algorithmTrialParameter P (states i) ≠ 0 := by
          intro hk
          exact ht.1 (by rw [hS.count]; exact hk)
        have ht₁ : k + 1 < n → algorithmTrialParameter P
            (rawObservationEvent (algorithmModel P) f G 1 false (states i)) ≠ 0 := by
          intro hk
          have hp := quadraticEventInvariant_step P Q hQ hpos g₀ constant (states i) k (by omega)
            (fun j hj => hg j (by omega)) hS (by rw [hcap]; omega) 1 one_ne_zero false (ht₀ (by omega))
          exact ht.2 (by rw [hp.count]; exact hk)
        have hnext := quadratic_rawOuterAdvance_progress P Q hQ hpos g₀ constant (states i) k hkn hn
          hg hterminal hS (hcap i) hz hsigma ht₀ ht₁
        rcases hnext with hz' | ⟨j, hkj, hjn, hj⟩
        · exact Or.inl hz'
        · exact Or.inr ⟨j, by omega, hjn, hj⟩

/-- The literal raw algorithm reaches the actual true critical point in
at most n+1 outer iterations; the n-th stored pair may have been a rejected
probe. The stronger per-stored-event identities are proved separately. -/
theorem quadratic_rawRun_terminates {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant initialStep : ℝ) (bounds : SpectralBounds)
    (hinitial : P.initialCapacity = n) (hmaximum : P.maximumCapacity = n) (hn : 0 < n)
    (hg : ∀ k < n, CG.gradient Q g₀ k ≠ 0) (hterminal : CG.gradient Q g₀ n = 0)
    (hsigma : P.armijo < 1 / 2)
    (htrials : ∀ i,
      let S := rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀)
        (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) i
      S.gradient ≠ 0 →
        (S.pairs.length < n → algorithmTrialParameter P S ≠ 0) ∧
        (let probe := rawObservationEvent (algorithmModel P) (quadraticObjective Q g₀ constant)
          (quadraticGradient Q g₀) 1 false S
         probe.pairs.length < n → algorithmTrialParameter P probe ≠ 0)) :
    (rawRun P n (algorithmModel P) (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀)
      (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds)
      (n + 1)).gradient = 0 := by
  rcases quadratic_rawRun_invariant P Q hQ hpos g₀ constant initialStep bounds hinitial hmaximum hn
    hg hterminal hsigma htrials (n + 1) with h | ⟨k, hk, hkn, _⟩
  · exact h
  · omega

end
end krylov.XR
