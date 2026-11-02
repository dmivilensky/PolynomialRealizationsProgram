import krylov.XR.LocalStrictBranch

/-!
Article: main_krylov, lem:xr-local, literal finite accepted-branch replay.
Use: a computed actual endpoint transcript on the proved strict branch
forces the genuine XR executor to perform exactly the full-memory virtual
queries, including cached observations, anchors, Ritz bounds and counters.
The source theorem obtains this branch from a genuine Hessian perturbation.
Source: the proved endpoint-state identity and actual one-step executor.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual scalar full-memory executor preserves the original
safeguard constants, irrespective of its queried source. -/
theorem fullVirtualRun_constants (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (k : ℕ) :
    let S := fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k
    S.descentConstant = P.safeguardMargin * ‖WithLp.ofLp (G x₀)‖⁻¹ ∧
      S.normConstant = ‖WithLp.ofLp (G x₀)‖⁻¹ / P.safeguardMargin := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih => exact ih

/-- On genuine endpoint data, the strict transition predicate is exactly
the real candidate slope/length/Armijo/positive-secant inequalities. -/
theorem fullVirtualRun_strict_transition (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k < n)
    (h : EndpointTransitionStrict P.armijo
      (P.safeguardMargin * ‖WithLp.ofLp (G x₀)‖⁻¹)
      (‖WithLp.ofLp (G x₀)‖⁻¹ / P.safeguardMargin)
      (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ (k + 1))) :
    let S := fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k
    let u := fullVirtualStep P (algorithmTrialParameter P) S
    inner ℝ S.gradient u < 0 ∧ GradientRelated S.descentConstant S.normConstant S.gradient u ∧
      Accepted f P.armijo S.point S.gradient u 1 ∧ positivePair (observedTrialPair f G S u) := by
  let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ k
  let S := fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k
  let u := fullVirtualStep P (algorithmTrialParameter P) S
  let x := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C
  have hS : S = endpointNativeState P bounds C :=
    fullVirtualRun_eq_endpointNativeState P bounds hinit hmax f G x₀ k hk.le
  have hq : S.point + u = x := by
    dsimp only [u]
    rw [hS]
    exact fullVirtualStep_endpoint P C _ (algorithmTrialParameter P)
      (endpointComputedTrial P bounds k) rfl rfl rfl rfl
  have hs : endpointStep
      (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ (k + 1)) (Fin.last k) = u := by
    simp only [endpointFunctionRun, endpointStep, extendEndpointChart, Fin.succ_last,
      Fin.snoc_last, Fin.snoc_castSucc]
    change x - C.1 (Fin.last k) = u
    have hp : C.1 (Fin.last k) = S.point := congrArg State.point hS.symm
    rw [hp, ← hq]
    abel
  have hg : (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ (k + 1)).2.2
      (Fin.last k).castSucc = S.gradient := by
    simp only [endpointFunctionRun, extendEndpointChart, Fin.snoc_castSucc]
    change C.2.2 (Fin.last k) = S.gradient
    exact congrArg State.gradient hS.symm
  have hv : (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ (k + 1)).2.1
      (Fin.last k).castSucc = S.value := by
    simp only [endpointFunctionRun, extendEndpointChart, Fin.snoc_castSucc]
    change C.2.1 (Fin.last k) = S.value
    exact congrArg State.value hS.symm
  have hy : endpointImage
      (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ (k + 1)) (Fin.last k) =
      G (S.point + u) - S.gradient := by
    simp only [endpointFunctionRun, endpointImage, extendEndpointChart, Fin.succ_last,
      Fin.snoc_last, Fin.snoc_castSucc]
    change G x - C.2.2 (Fin.last k) = _
    rw [hq, congrArg State.gradient hS]
    rfl
  dsimp only [EndpointTransitionStrict] at h
  rw [hs, hg, hv, hy] at h
  have hcache := fullVirtualRun_cache P (algorithmTrialParameter P) f G x₀ bounds k
  change S.value = f S.point ∧ S.gradient = G S.point at hcache
  have hc := fullVirtualRun_constants P f G x₀ bounds k
  refine ⟨h.1, ⟨?_, ?_⟩, ?_, ?_⟩
  · change inner ℝ S.gradient u ≤ -S.descentConstant * ‖S.gradient‖ ^ 2
    rw [hc.1]
    exact h.2.1.le
  · change ‖u‖ ≤ S.normConstant * ‖S.gradient‖
    rw [hc.2]
    exact h.2.2.1.le
  · apply (accepted_iff_armijo f P.armijo S.point S.gradient u 1 (by norm_num) h.1).mpr
    have hh := h.2.2.2.1.le
    simp only [endpointFunctionRun, extendEndpointChart, Fin.snoc_last] at hh
    change f x ≤ S.value + P.armijo * inner ℝ S.gradient u at hh
    rw [hcache.1] at hh
    simpa only [one_smul, mul_one, hq] using hh
  · exact h.2.2.2.2

/-- A real strict endpoint transcript forces exact native XR=XRFC/F
execution through that whole finite prefix. Successful decisions are
derived from the observed branch predicate, including true Armijo values. -/
theorem algorithmRun_eq_fullVirtualRun_of_finiteBranch (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : N ≤ n)
    (hbranch : EndpointFiniteBranch P.valuesEnabled (endpointComputedTrial P bounds)
      P.windowThreshold P.armijo (P.safeguardMargin * ‖WithLp.ofLp (G x₀)‖⁻¹)
      (‖WithLp.ofLp (G x₀)‖⁻¹ / P.safeguardMargin) x₀ (f x₀) (G x₀) N
      (adaptiveTranscript
        (endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) x₀ (f x₀) (G x₀))
        (fun x => (f x, G x)) N)) :
    algorithmRun P f G x₀ bounds N =
      fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds N := by
  induction N with
  | zero => rfl
  | succ k ih =>
    let query := endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) x₀ (f x₀) (G x₀)
    let oracle := fun x => (f x, G x)
    let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ k
    let S := fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k
    have hchart (j : ℕ) : endpointProgramChart P.valuesEnabled (endpointComputedTrial P bounds) x₀ (f x₀) (G x₀) j
        (adaptiveTranscript query oracle j) =
        endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ j :=
      (endpointFunctionRun_eq_program P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ j).symm
    change EndpointFiniteBranch _ _ _ _ _ _ _ _ _ (k + 1) (adaptiveTranscript query oracle (k + 1)) at hbranch
    dsimp only [EndpointFiniteBranch] at hbranch
    have hinitData : Fin.init (adaptiveTranscript query oracle (k + 1)) =
        adaptiveTranscript query oracle k := by rw [adaptiveTranscript, Fin.init_snoc]
    rw [hinitData] at hbranch
    have hprev := hbranch.1
    have hprevious := ih (by omega) hprev
    have hlocal := hbranch.2
    rw [hchart k, hchart (k + 1)] at hlocal
    obtain ⟨hLI, ho, hc, hs, ht⟩ := hlocal
    have htests := endpointObservations_tests P C hLI ho hc (fun i => (hs i).le)
    have hS : S = endpointNativeState P bounds C :=
      fullVirtualRun_eq_endpointNativeState P bounds hinit hmax f G x₀ k (by omega)
    have hpairs : S.pairs = endpointObservations C := congrArg State.pairs hS
    have hcap : S.pairs.length ≤ min S.capacity n := by
      have hcapacity : S.capacity = n := by rw [hS]; exact hinit
      rw [hpairs, endpointObservations_length, hcapacity, min_self]
      omega
    have hret := algorithmModel_retains_of_window P S
      (hpairs.symm ▸ htests.1) hcap (hpairs.symm ▸ htests.2.1)
    have hvalues : P.valuesEnabled = true →
        (∀ i : Fin S.pairs.length, |12 * storedSplit S.pairs i * (S.pairs.get i).valueDefect| ≤
          storedPairing S.pairs i i / 2) ∧ correctedWindowPasses P.windowThreshold S.pairs := by
      intro _
      rw [hpairs]
      exact htests.2.2
    have hdir := algorithmModel_direction_eq_fullVirtual P S hret.1 hvalues
    have htrue := fullVirtualRun_strict_transition P bounds hinit hmax f G x₀ k (by omega) ht
    have hnonzero : S.gradient ≠ 0 := by
      intro hz
      have hh := htrue.1
      change inner ℝ S.gradient _ < 0 at hh
      rw [hz, inner_zero_left] at hh
      exact (lt_irrefl (0 : ℝ)) hh
    have hinactive : (algorithmModel P S).safeDirection S = (algorithmModel P S).direction := by
      apply safeguard_eq_of_gradientRelated
      rw [hdir]
      exact htrue.2.1
    have hnext := outerAdvance_eq_fullVirtualAdvance P f G S hnonzero hret.1 hret.2.1 hret.2.2
      hvalues hinactive (by rw [hinactive, hdir]; exact htrue.2.2.1)
      (by rw [hinactive, hdir]; exact htrue.2.2.2)
    change outerAdvance P n (algorithmModel P) f G (algorithmRun P f G x₀ bounds k) =
      fullVirtualAdvance P (algorithmTrialParameter P) f G S
    rw [hprevious]
    exact hnext

/-- Exact replay holds at every actual prefix of the finite strict branch,
not merely at its final observed point. -/
theorem algorithmRun_eq_fullVirtualRun_prefixes_of_finiteBranch (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : N ≤ n)
    (hbranch : EndpointFiniteBranch P.valuesEnabled (endpointComputedTrial P bounds)
      P.windowThreshold P.armijo (P.safeguardMargin * ‖WithLp.ofLp (G x₀)‖⁻¹)
      (‖WithLp.ofLp (G x₀)‖⁻¹ / P.safeguardMargin) x₀ (f x₀) (G x₀) N
      (adaptiveTranscript
        (endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) x₀ (f x₀) (G x₀))
        (fun x => (f x, G x)) N)) :
    ∀ k ≤ N, algorithmRun P f G x₀ bounds k =
      fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k := by
  induction N with
  | zero =>
    intro k hk
    have he : k = 0 := by omega
    subst k
    rfl
  | succ N ih =>
    have hlast := algorithmRun_eq_fullVirtualRun_of_finiteBranch P bounds hinit hmax f G x₀ (N + 1) hN hbranch
    have hprev := hbranch.1
    simp only [adaptiveTranscript, Fin.init_snoc] at hprev
    have hp := ih (by omega) hprev
    intro k hk
    by_cases he : k = N + 1
    · subst k
      exact hlast
    · exact hp k (by omega)

/-- Full virtual execution stores its literal complete chronological
history. Combined with source-driven replay this is actual full memory. -/
theorem fullVirtualRun_pairs_length (P : Parameters)
    (trial : State (EuclideanSpace ℝ (Fin n)) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (k : ℕ) :
    (fullVirtualRun P trial f G x₀ bounds k).pairs.length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [fullVirtualRun, fullVirtualAdvance, List.length_map, List.length_append,
      List.length_singleton, ih]

end
end krylov.XR
