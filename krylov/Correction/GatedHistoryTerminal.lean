import krylov.Correction.GatedFinalPrefix
import krylov.Correction.GatedWindowPhase

/-!
Article: main_krylov, thm:UCg, original-history terminal and cutoff bounds.
Use: Apply the genuine uniform two-case cycle argument to the real measured
history, actual returned gradient, true searched line and performed queries.
Source: proved actual observed-window execution and canonical dictionaries,
true full terminal model estimates and scale-uniform restart geometry.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine original full-window gated history with the proved prefix property performs its actual last correction and has the refined true terminal metric-gradient bound.
Use: Finish the original uniform spectral-gated RFC finite-cycle theorem.
Article: main_krylov, thm:UCg, genuine original-history cycle bounds.
Proof: Use the original observed-window executor to identify its actual real correction phase. Genuine canonical phase and query-trace covariance transport the proved full last-prefix model bound back to the original physical returned gradient and true searched line.
-/
theorem gated_history_full_prefix_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (H : History (EuclideanSpace ℝ (Fin n)))
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hn : 2≤n) (hdim : (selectedWindow fullMemory H).length+1=n)
    {γ a C ε K : ℝ} (hγ : 0≤γ) (hγ1 : γ<1) (ha : 0≤a) (hε : 0≤ε) (hK : 0≤K)
    (hC : IsUnit (crossGram (windowImages (selectedWindow fullMemory H)) (windowSteps (selectedWindow fullMemory H))).det)
    (hc : inner ℝ (windowDirection (selectedWindow fullMemory H) H.gradient)
      (A (windowDirection (selectedWindow fullMemory H) H.gradient))≠0)
    (hprefix : recordedPrefixBound a C ε (primalWindow base (windowSteps (selectedWindow fullMemory H)))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ H.gradient))
    (hA : ‖canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hB : ‖canonicalOperator base B-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hy : ∀ i, ‖dualWindow base (windowImages (selectedWindow fullMemory H)) i-
      primalWindow base (windowSteps (selectedWindow fullMemory H)) i‖≤((1+K)*ε)*
        ‖primalWindow base (windowSteps (selectedWindow fullMemory H)) i‖)
    (hangle : (n : ℝ)*a≤(1-γ)/8) (hpair : (1+K)*ε≤a/2) :
    let W := selectedWindow fullMemory H
    let d := windowDirection W H.gradient
    let F := runCorrections (gatedCorrection fullMemory γ H (A d)) B (searchedGradient H.gradient d (A d))
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    F.trace≠[] ∧ ‖J F.gradient‖≤4*(n : ℝ)*(2+K)*ε*
      (C*ε^2+Real.sqrt n*(((2+K)*ε)*‖R (lineLength H.gradient d (A d) • d)‖)) := by
  let W := selectedWindow fullMemory H
  let d := windowDirection W H.gradient
  let F := runCorrections (gatedCorrection fullMemory γ H (A d)) B (searchedGradient H.gradient d (A d))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  have hp : 0<W.length := by change (selectedWindow fullMemory H).length>0; omega
  have hcurv : inner ℝ (R d) (canonicalOperator base A (R d))≠0 := by
    rw [canonicalOperator_primal base hb,← canonical_search_pairing base hb]
    exact hc
  have ho i : inner ℝ (dualWindow base (windowImages W) i) (R d)=0 :=
    canonical_window_image_conjugacy base hb W H.gradient hC i
  have hbound := gated_full_step_prefix_bound (primalWindow base (windowSteps W)) (dualWindow base (windowImages W))
    (J H.gradient) (R d) (canonicalOperator base A) (canonicalOperator base B) hdim hp hγ hγ1 ha hε hK
    hprefix hA hB hy ho hcurv hangle hpair
  have hphysical := gatedCorrection_window_phase fullMemory γ H (A d) B
  have hcanon := gatedArrayPhase_canonical base hb γ (windowSteps W) (windowImages W) H.gradient d (A d) B
  have htrace := gatedArrayPhase_canonical_trace_nonempty base hb γ (windowSteps W) (windowImages W) H.gradient d (A d) B
  rw [← hphysical] at hcanon htrace
  rw [canonicalOperator_primal base hb] at hbound
  dsimp only
  refine ⟨htrace.mp hbound.1,?_⟩
  have hb' := hbound.2
  rw [hcanon.2,canonical_lineLength base hb] at hb'
  simpa only [map_smul] using hb'

/-- Every actually executed final full-window gated correction has the genuine metric-gradient contraction directly in its original physical history.
Use: Finish the original uniform spectral-gated RFC finite-cycle theorem.
Article: main_krylov, thm:UCg, genuine original-history cycle bounds.
Proof: The original observed-window dictionary reads the real correction trace. Exact canonical covariance preserves genuine query presence and its returned gradient, so the proved measured full-model contraction applies without an assumed model or Gram domain.
-/
theorem gated_history_full_correction_contraction (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (H : History (EuclideanSpace ℝ (Fin n)))
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hdim : (selectedWindow fullMemory H).length+1=n) {γ ε η : ℝ}
    (hγ : 0<γ) (hε : 0≤ε) (hη : 0≤η) (hεη : ε≤η) (hhalf : η≤1/2) (hsmall : (n : ℝ)*η≤γ/4)
    (hy : ∀ i, ‖dualWindow base (windowImages (selectedWindow fullMemory H)) i-
      primalWindow base (windowSteps (selectedWindow fullMemory H)) i‖≤η*
        ‖primalWindow base (windowSteps (selectedWindow fullMemory H)) i‖)
    (hA : ‖canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hB : ‖canonicalOperator base B-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) :
    let W := selectedWindow fullMemory H
    let d := windowDirection W H.gradient
    let F := runCorrections (gatedCorrection fullMemory γ H (A d)) B (searchedGradient H.gradient d (A d))
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    F.trace≠[] → ‖J F.gradient‖≤
      (5*((Real.sqrt (γ/4))⁻¹*(n : ℝ)*(γ/2)⁻¹*Real.sqrt n))*(ε+η)*‖J H.gradient‖ := by
  let W := selectedWindow fullMemory H
  let d := windowDirection W H.gradient
  let F := runCorrections (gatedCorrection fullMemory γ H (A d)) B (searchedGradient H.gradient d (A d))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  dsimp only
  intro hnonempty
  have hphysical := gatedCorrection_window_phase fullMemory γ H (A d) B
  have hcanon := gatedArrayPhase_canonical base hb γ (windowSteps W) (windowImages W) H.gradient d (A d) B
  have htrace := gatedArrayPhase_canonical_trace_nonempty base hb γ (windowSteps W) (windowImages W) H.gradient d (A d) B
  rw [← hphysical] at hcanon htrace
  have htr : (gatedArrayPhase γ (primalWindow base (windowSteps W)) (dualWindow base (windowImages W))
      (J H.gradient) (R d) (canonicalOperator base A (R d)) (canonicalOperator base B)).trace≠[] := by
    rw [canonicalOperator_primal base hb]
    exact htrace.mpr hnonempty
  have hbound := gatedArrayPhase_full_correction_contraction
    (primalWindow base (windowSteps W)) (dualWindow base (windowImages W)) (J H.gradient) (R d)
    (canonicalOperator base A) (canonicalOperator base B) hdim hγ hε hη hεη hhalf hsmall hy hA hB htr
  rw [canonicalOperator_primal base hb,hcanon.2] at hbound
  exact hbound

end
end krylov.Correction
