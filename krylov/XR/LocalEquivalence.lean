import krylov.XR.LocalReferenceBranch

/-!
Article: main_krylov, lem:xr-local, genuine native finite source equivalence.
Use: one Hessian-perturbation threshold, chosen before the source function,
forces literal XR to execute the entire full-memory XRFC/F cycle with the
same actual computed trial. All observed inverse domains, window/value
tests, query locality and strict scalar decisions are derived internally.
Source: actual finite endpoint-oracle continuity and the genuine executed
quadratic Krylov invariant. The primitive reference assumptions are exactly
positive C² trials and strict safeguard/Armijo inequalities.
-/

namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace BigOperators
variable {n : ℕ}

/-- Every actual finite reference query set lies in one genuine source
ball, chosen before any perturbed function is considered. -/
theorem finite_adaptive_reference_ball {E D : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup D]
    (query : (k : ℕ) → (Fin k → D) → E) (oracle : E → D) (N : ℕ) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ k < N, adaptivePoint query oracle k ∈ ball 0 radius := by
  let radius := (∑ i ∈ Finset.range N, ‖adaptivePoint query oracle i‖) + 1
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, ‖adaptivePoint query oracle i‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨radius, by dsimp only [radius]; linarith, ?_⟩
  intro k hk
  have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range N) =>
    norm_nonneg (adaptivePoint query oracle i)) (Finset.mem_range.mpr hk)
  change dist (adaptivePoint query oracle k) 0 < radius
  rw [dist_zero_right]
  dsimp only [radius]
  linarith

/-- Original full-atom strict-reference hypotheses force exact literal
XR=XRFC/F execution, with full memory, for every sufficiently small genuine
Hessian perturbation with matched initial value and gradient. The source
ball and threshold precede all source functions; no successful perturbed
decision, query bound or output expansion is assumed.

The endpoint trial function in the premise is literally the computed XR
trial with its real running Ritz estimates. Thus the source's C² assumption
is imposed only on that primitive observable rule, never on its output. -/
theorem native_XR_local_equivalence (P : Parameters) (hP : P.Valid (n + 1))
    (bounds : SpectralBounds) (hinit : P.initialCapacity = n + 1) (hmax : P.maximumCapacity = n + 1)
    (base : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hb : base.PosDef)
    (g₀ : EuclideanSpace ℝ (Fin (n + 1))) (constant : ℝ)
    (hatoms : referenceAtomCount base hb g₀ = n + 1)
    (htrial : ∀ k < n + 1,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective (cgOperator base) g₀ constant) (quadraticGradient (cgOperator base) g₀) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C)
    (hstrict : ∀ k < n + 1, EndpointTransitionCoreStrict P.armijo
      (P.safeguardMargin * ‖WithLp.ofLp g₀‖⁻¹) (‖WithLp.ofLp g₀‖⁻¹ / P.safeguardMargin)
      (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective (cgOperator base) g₀ constant) (quadraticGradient (cgOperator base) g₀) 0 (k + 1))) :
    ∃ radius epsilon : ℝ, 0 < radius ∧ 0 < epsilon ∧
      ∀ (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
        (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        (H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (n + 1))),
        f 0 = constant → G 0 = g₀ →
        (∀ z ∈ ball 0 radius, HasFDerivAt f (innerSL ℝ (G z)) z) →
        (∀ z ∈ ball 0 radius, HasFDerivAt G (H z) z) →
        (∀ z ∈ ball 0 radius, ‖H z - cgOperator base‖ ≤ epsilon) →
        ∀ k ≤ n + 1,
          algorithmRun P f G 0 bounds k = fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds k ∧
            (algorithmRun P f G 0 bounds k).pairs.length = k := by
  let Q := cgOperator base
  let reference := fun x => (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)
  let query := endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀
  let c₁ := P.safeguardMargin * ‖WithLp.ofLp g₀‖⁻¹
  let c₂ := ‖WithLp.ofLp g₀‖⁻¹ / P.safeguardMargin
  let V := {data | EndpointFiniteBranch P.valuesEnabled (endpointComputedTrial P bounds)
    P.windowThreshold P.armijo c₁ c₂ 0 constant g₀ (n + 1) data}
  have hQ := cgOperator_positive base hb
  have hg : ∀ i < n + 1, CG.gradient Q g₀ i ≠ 0 := by
    simpa only [hatoms] using cg_nonstagnation base hb g₀
  have hmargin : 0 < P.safeguardMargin := by
    rcases hP with ⟨_, _, _, _, _, _, _, _, hm, _⟩
    exact hm
  have hc₁ : 0 ≤ c₁ := mul_nonneg hmargin.le (inv_nonneg.mpr (norm_nonneg _))
  have hdomains := quadratic_endpointProgram_domains P bounds hinit hmax Q hQ.1 hQ.2 g₀ constant hg htrial
  have hV : V ∈ 𝓝 (adaptiveTranscript query reference (n + 1)) :=
    quadratic_endpointFiniteBranch_mem_nhds P bounds hinit hmax Q hQ.1 hQ.2 g₀ constant hg c₁ c₂ hc₁ htrial hstrict
  obtain ⟨radius, hradius, hpoints⟩ := finite_adaptive_reference_ball query reference (n + 1)
  obtain ⟨epsilon, hepsilon, hsource⟩ := finite_scalar_source_open_branch Q hQ.1 g₀ constant query (n + 1)
    radius hradius (fun k hk => (endpointProgram_contDiff P.valuesEnabled (endpointComputedTrial P bounds)
      0 constant g₀ 2 k _ (hdomains k hk)).2.continuousAt) hpoints V hV
  refine ⟨radius, epsilon, hradius, hepsilon, ?_⟩
  intro f G H hf₀ hg₀ hF hG hH
  have hfmatch : f 0 = quadraticObjective Q g₀ constant 0 := by
    simpa [quadraticObjective, krylov.Functions.quadraticPotential] using hf₀
  obtain ⟨_hqueries, hdata⟩ := hsource f G H hfmatch hg₀ hF hG hH
  have hbranch : EndpointFiniteBranch P.valuesEnabled (endpointComputedTrial P bounds)
      P.windowThreshold P.armijo (P.safeguardMargin * ‖WithLp.ofLp (G 0)‖⁻¹)
      (‖WithLp.ofLp (G 0)‖⁻¹ / P.safeguardMargin) 0 (f 0) (G 0) (n + 1)
      (adaptiveTranscript
        (endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) 0 (f 0) (G 0))
        (fun x => (f x, G x)) (n + 1)) := by
    rw [hf₀, hg₀]
    exact hdata
  have heq := algorithmRun_eq_fullVirtualRun_prefixes_of_finiteBranch P bounds hinit hmax f G 0 (n + 1)
    le_rfl hbranch
  intro k hk
  refine ⟨heq k hk, ?_⟩
  rw [heq k hk]
  exact fullVirtualRun_pairs_length P (algorithmTrialParameter P) f G 0 bounds k

end
end krylov.XR
