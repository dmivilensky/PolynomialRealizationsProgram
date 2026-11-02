import krylov.XR.LocalTerminalEquivalence
import krylov.XR.XRFCScalarDictionary

/-!
Article: main_krylov, lem:xr-local, faithful terminal virtual output.
Use: extend the exact finite native equivalence to the literal next
ModelStep at the complete window. Every terminal rank/value/Hermitian gate
is derived from true endpoint continuity; no extra trial or successful
terminal decision is assumed. The final correction is unevaluated here.
-/

/-!
Article: krylov, Lemma F.11 [lem:xr-local].

Strict finite quadratic decisions persist for actual nearby scalar objectives; literal full-
memory XR/XR-F outputs agree with the corresponding scalar virtual executors. Actual operator
trial vectors give the first variation and quadratic trial-rule comparison.
The positive C2 policy chart is an explicit hypothesis. Simple extreme Ritz values are needed
only for the spectral chart; primitive smooth trial policies, including the secant scale, use
the general prescribed-trial transfer.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace BigOperators
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Genuine native strict-reference execution identifies every actual internal
virtual point with the corresponding unevaluated full-memory correction.
Both value flags are included. All rank, refutation and value gates are
proved from primitive endpoint regularity and the actual finite oracle. -/
theorem native_XR_local_virtual_outputs (P : Parameters) (hP : P.Valid (n + 1))
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
          algorithmVirtualPoint P (algorithmRun P f G 0 bounds k) =
            fullVirtualOutput P (algorithmTrialParameter P) f G 0 bounds k := by
  let Q := cgOperator base
  let reference := fun x => (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)
  let query := endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀
  let c₁ := P.safeguardMargin * ‖WithLp.ofLp g₀‖⁻¹
  let c₂ := ‖WithLp.ofLp g₀‖⁻¹ / P.safeguardMargin
  let V := {data | EndpointFiniteBranch P.valuesEnabled (endpointComputedTrial P bounds)
    P.windowThreshold P.armijo c₁ c₂ 0 constant g₀ (n + 1) data ∧
    EndpointModelTests P (endpointProgramChart P.valuesEnabled (endpointComputedTrial P bounds)
      0 constant g₀ (n+1) data)}
  have hQ := cgOperator_positive base hb
  have hg : ∀ i < n + 1, CG.gradient Q g₀ i ≠ 0 := by
    simpa only [hatoms] using cg_nonstagnation base hb g₀
  have hmargin : 0 < P.safeguardMargin := by
    rcases hP with ⟨_, _, _, _, _, _, _, _, hm, _⟩
    exact hm
  have hc₁ : 0 ≤ c₁ := mul_nonneg hmargin.le (inv_nonneg.mpr (norm_nonneg _))
  have hdomains := quadratic_endpointProgram_domains P bounds hinit hmax Q hQ.1 hQ.2 g₀ constant hg htrial
  have hV : V ∈ 𝓝 (adaptiveTranscript query reference (n + 1)) :=
    Filter.inter_mem
      (quadratic_endpointFiniteBranch_mem_nhds P bounds hinit hmax Q hQ.1 hQ.2 g₀ constant hg c₁ c₂ hc₁ htrial hstrict)
      (quadratic_endpoint_terminal_tests_mem_nhds P bounds hinit hmax Q hQ.1 hQ.2 g₀ constant hg htrial)
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
    exact hdata.1
  have heq := algorithmRun_eq_fullVirtualRun_prefixes_of_finiteBranch P bounds hinit hmax f G 0 (n + 1)
    le_rfl hbranch
  intro k hk
  rw [heq k hk]
  apply algorithmVirtualPoint_eq_full_of_endpoint_tests P bounds hinit hmax f G 0 k hk
  by_cases hlast : k = n+1
  · subst k
    have hchart := endpointFunctionRun_eq_program P.valuesEnabled (endpointComputedTrial P bounds) f G 0 (n+1)
    rw [hf₀, hg₀] at hchart
    rw [hchart]
    exact hdata.2
  · exact endpointFunctionRun_tests_of_finiteBranch P bounds f G 0
      (P.safeguardMargin * ‖WithLp.ofLp (G 0)‖⁻¹)
      (‖WithLp.ofLp (G 0)‖⁻¹ / P.safeguardMargin) (n+1) hbranch k (by omega)

/-- In the ordinary branch every actual internal virtual output is exactly
the genuine scalar XRFC output with the native rule's own computed trial
vector. This is a native source corollary, not an execution assumption. -/
theorem native_XR_local_XRFC_outputs (P : Parameters) (hP : P.Valid (n + 1)) (hoff : P.valuesEnabled = false)
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
          algorithmVirtualPoint P (algorithmRun P f G 0 bounds k) =
            krylov.Convergence.oneGradientFunctionOutput (xrfcMethod fullMemory
              (prescribedTrial (fullVirtualTrialVector P f G 0 bounds k))) G 0 k := by
  obtain ⟨radius, epsilon, hr, he, h⟩ := native_XR_local_virtual_outputs P hP bounds hinit hmax
    base hb g₀ constant hatoms htrial hstrict
  refine ⟨radius, epsilon, hr, he, ?_⟩
  intro f G H hf hg hF hG hH k hk
  exact (h f G H hf hg hF hG hH k hk).trans
    (fullVirtualOutput_oneGradient_dictionary P hoff f G 0 bounds k)

end
end krylov.XR
