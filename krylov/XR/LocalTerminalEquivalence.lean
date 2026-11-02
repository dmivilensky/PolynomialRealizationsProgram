import krylov.XR.LocalTerminalTests

/-!
Article: main_krylov, lem:xr-local, faithful terminal virtual output.
Use: extend the exact finite native equivalence to the literal next
ModelStep at the complete window. Every terminal rank/value/Hermitian gate
is derived from true endpoint continuity; no extra trial or successful
terminal decision is assumed. The final correction is unevaluated here.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace BigOperators
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Original strict-reference hypotheses also identify the actual terminal
full-window ModelStep with the real unevaluated XRFC/F output. -/
theorem native_XR_local_terminal_correction (P : Parameters) (hP : P.Valid (n + 1))
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
        (∀ k ≤ n + 1,
          algorithmRun P f G 0 bounds k = fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds k ∧
            (algorithmRun P f G 0 bounds k).pairs.length = k) ∧
        let S := algorithmRun P f G 0 bounds (n+1)
        (algorithmModel P S).pairs = S.pairs ∧
          S.point + (algorithmModel P S).direction =
            fullVirtualOutput P (algorithmTrialParameter P) f G 0 bounds (n+1) := by
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
  refine ⟨?_, ?_⟩
  · intro k hk
    refine ⟨heq k hk, ?_⟩
    rw [heq k hk]
    exact fullVirtualRun_pairs_length P (algorithmTrialParameter P) f G 0 bounds k
  · let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 (n+1)
    let S := endpointNativeState P bounds C
    have hstate : algorithmRun P f G 0 bounds (n+1) = S := by
      rw [heq (n+1) le_rfl, fullVirtualRun_eq_endpointNativeState P bounds hinit hmax]
      exact le_rfl
    have hchart := endpointFunctionRun_eq_program P.valuesEnabled (endpointComputedTrial P bounds) f G 0 (n+1)
    rw [hf₀, hg₀] at hchart
    have ht : EndpointModelTests P C := by
      change EndpointModelTests P (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 (n+1))
      rw [hchart]
      exact hdata.2
    have hlist := endpointObservations_tests P C ht.1 ht.2.1 ht.2.2.1 (fun i => (ht.2.2.2 i).le)
    have hret := algorithmModel_retains_of_window P S hlist.1 (by
      simp only [S, endpointNativeState, endpointObservations_length, hinit, min_self, le_refl]) hlist.2.1
    have hpairs : S.pairs.length = n+1 := endpointObservations_length C
    have hvalues : P.valuesEnabled = true →
        (∀ i : Fin S.pairs.length, |12*storedSplit S.pairs i*(S.pairs.get i).valueDefect| ≤
          storedPairing S.pairs i i/2) ∧ correctedWindowPasses P.windowThreshold S.pairs := by
      intro _
      exact ⟨hlist.2.2.1, hlist.2.2.2⟩
    have hu := algorithmModel_direction_eq_fullVirtual P S hret.1 hvalues
    have hfull : (algorithmModel P S).pairs.length = n+1 := by rw [hret.1]; exact hpairs
    have hnonemptyModel : (algorithmModel P S).pairs.length ≠ 0 := by rw [hfull]; omega
    have htrialZero : algorithmTrialParameter P S = 0 := by
      unfold algorithmTrialParameter
      dsimp only
      rw [ite_eq_right hnonemptyModel, ite_eq_left (Or.inl hfull)]
    have hnonempty : S.pairs.length ≠ 0 := by rw [hpairs]; omega
    rw [fullVirtualStep, ite_eq_right hnonempty, htrialZero, zero_smul, add_zero] at hu
    dsimp only
    rw [hstate]
    refine ⟨hret.1, ?_⟩
    rw [hu]
    unfold fullVirtualOutput
    rw [fullVirtualRun_eq_endpointNativeState P bounds hinit hmax _ _ 0 (n+1) le_rfl]

end
end krylov.XR
