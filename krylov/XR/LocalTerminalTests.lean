import krylov.XR.LocalEquivalence

/-!
Article: main_krylov, lem:xr-local, the unevaluated final correction.
Use: preserve actual model tests at the full terminal window as well as
at each queried prefix. This requires no extra trial smoothness at the
terminal full window: its endpoint chart uses only the preceding trials.
Source: genuine finite endpoint-query regularity and open strict matrix tests.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace ComplexOrder
variable {n : ℕ}

/-- Actual terminal endpoint decisions, with no acceptance or rate field. -/
def EndpointModelTests {k : ℕ} (P : Parameters)
    (C : EndpointChart (EuclideanSpace ℝ (Fin (n+1))) k) : Prop :=
  LinearIndependent ℝ (endpointStep C) ∧
    (endpointHermitianTest P.windowThreshold false C).PosDef ∧
    (endpointHermitianTest P.windowThreshold true C).PosDef ∧
    ∀ i, |12*endpointSplit C i*endpointDefect C i| <
      inner ℝ (endpointStep C i) (endpointImage C i)/2

/-- The actual internal virtual point of the retained, selected ModelStep. -/
def algorithmVirtualPoint (P : Parameters) (S : State (EuclideanSpace ℝ (Fin (n+1)))) :
    EuclideanSpace ℝ (Fin (n+1)) :=
  let M := algorithmModel P S
  S.point + modelVirtualCorrection (storedSteps M.pairs) (selectedModel P M.pairs) S.gradient

/-- Every queried prefix of a real finite branch has the actual endpoint
model tests used by that ModelStep. This extracts proved branch facts;
it does not impose success as a new executor or source field. -/
theorem endpointFunctionRun_tests_of_finiteBranch (P : Parameters) (bounds : SpectralBounds)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (x₀ : EuclideanSpace ℝ (Fin (n+1))) (c₁ c₂ : ℝ) (N : ℕ)
    (hbranch : EndpointFiniteBranch P.valuesEnabled (endpointComputedTrial P bounds)
      P.windowThreshold P.armijo c₁ c₂ x₀ (f x₀) (G x₀) N
      (adaptiveTranscript
        (endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) x₀ (f x₀) (G x₀))
        (fun x => (f x, G x)) N)) :
    ∀ k < N, EndpointModelTests P
      (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ k) := by
  induction N with
  | zero => intro k hk; omega
  | succ N ih =>
    let query := endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) x₀ (f x₀) (G x₀)
    let oracle := fun x => (f x, G x)
    change EndpointFiniteBranch _ _ _ _ _ _ _ _ _ (N+1) (adaptiveTranscript query oracle (N+1)) at hbranch
    dsimp only [EndpointFiniteBranch] at hbranch
    have hi : Fin.init (adaptiveTranscript query oracle (N+1)) = adaptiveTranscript query oracle N := by
      rw [adaptiveTranscript, Fin.init_snoc]
    rw [hi] at hbranch
    intro k hk
    by_cases he : k = N
    · subst k
      have hc := hbranch.2
      have hchart := endpointFunctionRun_eq_program P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ N
      rw [←hchart] at hc
      exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
    · exact ih hbranch.1 k (by omega)

/-- On the actual retained value/model branch the internal virtual point
is exactly the genuine full-memory virtual correction. -/
theorem algorithmVirtualPoint_eq_full_of_endpoint_tests (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n+1) (hmax : P.maximumCapacity = n+1)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (x₀ : EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (hk : k ≤ n+1)
    (htests : EndpointModelTests P
      (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ k)) :
    algorithmVirtualPoint P (fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k) =
      fullVirtualOutput P (algorithmTrialParameter P) f G x₀ bounds k := by
  let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ k
  have ht := endpointObservations_tests P C htests.1 htests.2.1 htests.2.2.1
    (fun i => (htests.2.2.2 i).le)
  rw [fullVirtualRun_eq_endpointNativeState P bounds hinit hmax _ _ x₀ k hk]
  let S := endpointNativeState P bounds C
  have hret := algorithmModel_retains_of_window P S ht.1 (by
    simp only [S, endpointNativeState, endpointObservations_length, hinit, min_self]
    exact hk) ht.2.1
  have hmodel := selectedModel_eq_fullVirtual P S.pairs (fun _ => ht.2.2)
  change S.point + modelVirtualCorrection (storedSteps (algorithmModel P S).pairs)
      (selectedModel P (algorithmModel P S).pairs) S.gradient = _
  rw [hret.1, hmodel]
  unfold fullVirtualOutput
  rw [fullVirtualRun_eq_endpointNativeState P bounds hinit hmax _ _ x₀ k hk]
  rfl

/-- All strict model decisions at the genuine terminal full window form
a neighbourhood in the actual response data, with no terminal trial premise. -/
theorem quadratic_endpoint_terminal_tests_mem_nhds (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n+1) (hmax : P.maximumCapacity = n+1)
    (Q : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin (n+1))) (constant : ℝ)
    (hg : ∀ i < n+1, CG.gradient Q g₀ i ≠ 0)
    (htrial : ∀ k < n+1,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C) :
    {data | EndpointModelTests P
      (endpointProgramChart P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀ (n+1) data)} ∈
      𝓝 (adaptiveTranscript
        (endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀)
        (fun x => (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) (n+1)) := by
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  let query := endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀
  let data := adaptiveTranscript query (fun x => (f x, G x)) (n+1)
  let C := endpointProgramChart P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀ (n+1)
  have hd := quadratic_endpointProgram_domains P bounds hinit hmax Q hQ hpos g₀ constant hg htrial
  have hc : ContDiffAt ℝ 2 C data := by
    apply endpointProgramChart_succ_contDiff
    simpa only [data, adaptiveTranscript, Fin.init_snoc] using hd n (by omega)
  have hf₀ : f 0 = constant := by simp [f, quadraticObjective, krylov.Functions.quadraticPotential]
  have hg₀ : G 0 = g₀ := by simp [G, quadraticGradient]
  have hchart : C data = endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 (n+1) := by
    have hh := endpointFunctionRun_eq_program P.valuesEnabled (endpointComputedTrial P bounds) f G 0 (n+1)
    rw [hf₀, hg₀] at hh
    exact hh.symm
  have hnonzero (k : ℕ) (hk : k < n+1) : algorithmTrialParameter P
      (fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds k) ≠ 0 := by
    rw [fullVirtualRun_trial_endpoint P bounds hinit hmax f G 0 k hk.le]
    exact (htrial k hk).1.ne'
  have htests := fullVirtualRun_quadratic_endpoint_domains P hinit hmax Q hQ hpos g₀ constant bounds
    hg hnonzero (n+1) le_rfl
  rw [←hchart] at htests
  exact endpoint_model_tests_eventually P.windowThreshold C data hc
    (fun i => (htests.2.1 i).ne') htests.1 (htests.2.2.2.2.1 false)
    (htests.2.2.2.2.1 true) htests.2.2.2.2.2

end
end krylov.XR
