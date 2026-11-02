import krylov.Correction.UniformModelBounds
import krylov.Correction.NearIdentityGate

/-!
Article: main_krylov, thm:UCg(iii), original arbitrary-threshold model transfer.
Use: Upgrade proved actual ordinary-model conditioning to any requested
measured spectral threshold while keeping its original uniform constants.
Source: genuine near-identity measured spectral criterion, actual observed
inverse nonzero columns and exact positive column-congruence invariance.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The same genuine active observed-model bounds hold at any new spectral threshold satisfying the actual common linear model margin.
Use: Shrink only the allowed source radius in gated part (iii), preserving its ordinary nonstagnation constant.
Article: main_krylov, thm:UCg(iii).
Proof: The true observed inverse forces every old physical query column nonzero, and the current actual direction is nonzero by the active-iteration premise. Their genuine metric norms give positive diagonal scales. Apply the proved real near-identity spectral test to the same actual normalized model and transfer that decision back by exact positive congruence invariance. All real inverse, defect and model bounds remain proved on the original executor.
-/
theorem activeObservedModelBounds_threshold (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) {γ₀ γ C ε : ℝ}
    (hmodels : activeObservedModelBounds base m A B g N γ₀ C ε)
    (hδ : 0≤C*ε) (hδ1 : C*ε<1) (hmargin : C*ε+γ*(C*ε)≤1-γ) :
    activeObservedModelBounds base m A B g N γ C ε := by
  dsimp only [activeObservedModelBounds]
  intro k hk hd
  let H := methodRun m A B g k
  let W := selectedWindow fullMemory H
  let d := m.direction H
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let U := (d,A k d)::W
  have ht := hmodels k hk hd
  have hMc : (canonicalObservedModel base U).IsHermitian := by
    change (rescaleModel (pairModel (windowSteps U) (windowImages U))
      (fun i => ‖primalWindow base (windowSteps U) i‖⁻¹)).IsHermitian
    exact rescale_pairModel_isHermitian _ _ _
  have htest := near_identity_matrix_spectral_gate (canonicalObservedModel base U) hMc hδ hδ1 ht.2.2.2 hmargin
  have hprimal (v : EuclideanSpace ℝ (Fin n)) (hv : v≠0) : R v≠0 := by
    intro hz
    have he := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹) hz
    rw [canonical_primal_dual_cancel base hb,map_zero] at he
    exact hv he
  have hpos (i : Fin U.length) : 0<‖primalWindow base (windowSteps U) i‖⁻¹ := by
    apply inv_pos.mpr
    apply norm_pos_iff.mpr
    dsimp only [U]
    rw [windowSteps_cons]
    change R ((Fin.cons d (windowSteps W) : Fin (W.length+1) → EuclideanSpace ℝ (Fin n)) i)≠0
    refine Fin.cases (hprimal d hd) (fun j => ?_) i
    exact hprimal _ (crossGram_right_ne_zero _ _ ht.1 j)
  have hgate : spectralGate γ U := by
    apply (matrixSpectralGate_window γ U).mp
    exact (matrixSpectralGate_congruence γ (windowModel U) _ hpos).mp htest
  exact ⟨ht.1,hgate,ht.2.2.1,ht.2.2.2⟩

end
end krylov.Correction
