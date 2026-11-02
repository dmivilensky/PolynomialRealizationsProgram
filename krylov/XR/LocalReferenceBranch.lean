import krylov.XR.LocalReferenceChart
import krylov.XR.LocalNativeReplay

/-!
Article: main_krylov, lem:xr-local, derived strict reference branch.
Use: the actual full-atom quadratic program and original strict reference
safeguard/Armijo inequalities provide the finite open branch required by
the scalar-source perturbation theorem. All model tests, rank, secant
positivity and inverse domains are derived from genuine quadratic data.
Source: the proved executed Krylov invariant and endpoint-source calculus.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference Filter Topology
open scoped InnerProductSpace
variable {n : ℕ}

/-- A true positive quadratic and the original strict scalar reference
decisions satisfy the complete finite actual branch. -/
theorem quadratic_endpointFiniteBranch (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0) (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 k
      0 < endpointComputedTrial P bounds k C)
    (hstrict : ∀ k < n, EndpointTransitionCoreStrict P.armijo c₁ c₂
      (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 (k + 1))) :
    ∀ N ≤ n, EndpointFiniteBranch P.valuesEnabled (endpointComputedTrial P bounds)
      P.windowThreshold P.armijo c₁ c₂ 0 constant g₀ N
      (adaptiveTranscript
        (endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀)
        (fun x => (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) N) := by
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  let query := endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀
  let oracle := fun x => (f x, G x)
  have hf₀ : f 0 = constant := by simp [f, quadraticObjective, krylov.Functions.quadraticPotential]
  have hg₀ : G 0 = g₀ := by simp [G, quadraticGradient]
  have hchart (k : ℕ) : endpointProgramChart P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀ k
      (adaptiveTranscript query oracle k) = endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k := by
    have hh := endpointFunctionRun_eq_program P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
    rw [hf₀, hg₀] at hh
    exact hh.symm
  have hnonzero (k : ℕ) (hk : k < n) : algorithmTrialParameter P
      (fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds k) ≠ 0 := by
    rw [fullVirtualRun_trial_endpoint P bounds hinit hmax f G 0 k hk.le]
    exact (htrial k hk).ne'
  intro N hN
  induction N with
  | zero => trivial
  | succ k ih =>
    have hk : k < n := by omega
    have hd := fullVirtualRun_quadratic_endpoint_domains P hinit hmax Q hQ hpos g₀ constant bounds
      hg hnonzero k hk.le
    have hdnext := fullVirtualRun_quadratic_endpoint_domains P hinit hmax Q hQ hpos g₀ constant bounds
      hg hnonzero (k + 1) hN
    have ht := endpointTransitionStrict_of_core P.armijo c₁ c₂ hc₁ _ (hstrict k hk)
      (hdnext.2.1 (Fin.last k))
    change EndpointFiniteBranch _ _ _ _ _ _ _ _ _ (k + 1) (adaptiveTranscript query oracle (k + 1))
    dsimp only [EndpointFiniteBranch]
    have hi : Fin.init (adaptiveTranscript query oracle (k + 1)) = adaptiveTranscript query oracle k := by
      rw [adaptiveTranscript, Fin.init_snoc]
    rw [hi]
    refine ⟨ih hk.le, ?_⟩
    rw [hchart k, hchart (k + 1)]
    exact ⟨hd.1, hd.2.2.2.2.1 false, hd.2.2.2.2.1 true, hd.2.2.2.2.2, ht⟩

/-- The complete finite native reference branch is a neighbourhood in
the true endpoint-response data space. Only the source's primitive trial
C² assumption is needed; executed-query smoothness is derived. -/
theorem quadratic_endpointFiniteBranch_mem_nhds (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n + 1) (hmax : P.maximumCapacity = n + 1)
    (Q : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin (n + 1))) (constant : ℝ)
    (hg : ∀ i < n + 1, CG.gradient Q g₀ i ≠ 0) (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁)
    (htrial : ∀ k < n + 1,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C)
    (hstrict : ∀ k < n + 1, EndpointTransitionCoreStrict P.armijo c₁ c₂
      (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 (k + 1))) :
    {data | EndpointFiniteBranch P.valuesEnabled (endpointComputedTrial P bounds)
      P.windowThreshold P.armijo c₁ c₂ 0 constant g₀ (n + 1) data} ∈
      𝓝 (adaptiveTranscript
        (endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀)
        (fun x => (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) (n + 1)) := by
  have hd := quadratic_endpointProgram_domains P bounds hinit hmax Q hQ hpos g₀ constant hg htrial
  have hb := quadratic_endpointFiniteBranch P bounds hinit hmax Q hQ hpos g₀ constant hg c₁ c₂ hc₁
    (fun k hk => (htrial k hk).1) hstrict (n + 1) le_rfl
  apply endpointFiniteBranch_mem_nhds _ _ _ _ _ _ _ _ _ _ _ hb
  apply Or.inr
  refine ⟨n, rfl, ?_⟩
  simpa only [adaptiveTranscript, Fin.init_snoc] using hd n (by omega)

end
end krylov.XR
