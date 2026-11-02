import krylov.Correction.GatedCutoffInvariant

/-!
Article: main_krylov, thm:UCg, genuine empty-prefix cutoff initialization.
Use: Start the actual recorded-angle and residual induction without inventing
an initial correction query or assuming a positive old coefficient dimension.
Source: the actual gated executor, genuine exact-search orthogonality and
true normalization of the real newly recorded line step.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine empty-window gated phase has zero correction and the real searched gradient, independently of the spectral test.
Use: Initialize the genuine finite-cycle uniform gated-RFC induction.
Article: main_krylov, thm:UCg, actual empty-prefix initialization.
Proof: An accepted spectral branch still reaches the actual empty-window RFC fallback; spectral rejection gives the same real zero-query result.
-/
theorem gatedArrayPhase_empty (γ : ℝ) (s y : Fin 0 → E) (g d z : E) (B : E →L[ℝ] E) :
    (gatedArrayPhase γ s y g d z B).movement=0 ∧
      (gatedArrayPhase γ s y g d z B).gradient=searchedGradient g d z := by
  unfold gatedArrayPhase
  split
  · simp only [rfcArrayPhase,lt_self_iff_false,false_and,ite_false,and_self]
  · exact ⟨rfl,rfl⟩

/-- The genuine first recorded gated step starts the common prefix-angle and quadratic-residual invariant whenever its actual line is nonzero.
Use: Initialize the genuine finite-cycle uniform gated-RFC induction.
Article: main_krylov, thm:UCg, actual empty-prefix initialization.
Proof: The true empty phase records only the real line displacement. Exact search makes its actual new projected residual zero; normalization preserves that zero, and the genuine old-angle conditions are empty.
-/
theorem recordedPrefixBound_empty_step (a C ε γ : ℝ) (hC : 0≤C) (s y : Fin 0 → E)
    (A B : E →L[ℝ] E) (g d : E) (hc : inner ℝ d (A d)≠0)
    (hline : 0<‖lineLength g d (A d) • d‖) :
    let P := gatedArrayPhase γ s y g d (A d) B
    let step := lineLength g d (A d) • d+P.movement
    recordedPrefixBound a C ε (Fin.cons step s) P.gradient := by
  have hp := gatedArrayPhase_empty γ s y g d (A d) B
  dsimp only
  rw [hp.1,hp.2,add_zero]
  let line := lineLength g d (A d) • d
  have hres : projectedResidual (unitWindow (Fin.cons line s)) (searchedGradient g d (A d))=0 := by
    ext i
    have hi : i=0 := Fin.eq_zero i
    subst i
    change inner ℝ (‖line‖⁻¹ • line) (searchedGradient g d (A d))=0
    rw [real_inner_smul_left]
    change _*inner ℝ (lineLength g d (A d) • d) (searchedGradient g d (A d))=0
    rw [real_inner_smul_left,searchedGradient_inner_zero _ _ _ hc,mul_zero,mul_zero]
  apply recordedPrefixBound_cons a C ε s line (searchedGradient g d (A d))
    (fun i => Fin.elim0 i) (norm_pos_iff.mp hline) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  rw [hres,norm_zero]
  positivity

end
end krylov.Correction
