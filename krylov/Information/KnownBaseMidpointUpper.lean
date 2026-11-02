import krylov.Information.SourceMidpointBound

/-!
Article: main_krylov, thm:C2(c), actual informed sharp upper bound.
Use: the genuine finite-history midpoint policy obeys the sharp quadratic
coefficient with one common cubic loss before every primitive source scenario.
Source: actual observed-hyperplane reconstruction, derived moving-normal
tube and the genuine joint source/model-change terminal expansion.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- Every genuine admissible known-base single-increment physical source scenario satisfies the sharp actual informed normalized upper estimate.
Use: the true source supremum is bounded without an assumed canonical trajectory or access to the unknown full increment matrix.
Article: main_krylov, thm:C2(c), actual all-physical-scenario informed upper bound.
Proof: original independent zero budgets force every later canonical
increment and the genuine terminal defect to vanish. The primitive first
budget bounds the true symmetric first increment and the complete finite
source norm. Apply the actual canonical informed tube, then reconstruct
the original physical oracles and divide by its true positive final
preterminal CG error, equal to the genuine last CG step norm. -/
theorem admissible_midpoint_sharp_upper (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount base hb g=N+1) (hN : 0<N) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ (ω : ℝ), 0≤ω → ω≤δ →
      ∀ S : Scenario (N+1), S.Admissible N base 0 (firstBudget ω) 0 0 → S.base=base →
        S.outputRatio (knownBaseMidpointMethod base g ω) g N≤(2/(3*Real.sqrt 3))*ω^2+C*ω^3 := by
  obtain ⟨δ,C,hδ,hC,hupper⟩ := source_midpoint_cubic_upper base hb g hcount hN
  refine ⟨δ,C,hδ,hC,?_⟩
  intro ω hω hωδ S hS hbase
  -- Derive the original canonical one-increment model directly from the actual physical budgets.
  let Θ := S.symmetricParameters N (fun i hi => (hS.2.2.1 i hi).1) hS.2.2.2.1
    (fun i hi => (hS.2.2.2.2.2 i hi).1)
  let M := relativeOperator S.base (S.increment 0)
  have hM : M.IsSymm := relativeOperator_isSymm _ _ (hS.2.2.1 0 hN).1
  have hMω : ‖M‖≤ω := by simpa only [M,firstBudget,ite_true,relativeBudget,chebyshev1.opNorm] using (hS.2.2.1 0 hN).2
  have hE : matrixSequenceExtension N Θ.val.1=firstIncrement M := by
    funext i
    by_cases hi : i<N
    · change matrixSequenceExtension N (S.canonicalParameters N).1 i=_
      rw [S.canonicalParameters_increment N hi]
      by_cases hz : i=0
      · subst i
        rfl
      · rw [firstIncrement,ite_eq_right hz]
        apply norm_eq_zero.mp
        apply le_antisymm _ (norm_nonneg _)
        simpa only [firstBudget,ite_eq_right hz,relativeBudget,chebyshev1.opNorm] using (hS.2.2.1 i hi).2
    · have hz : i≠0 := by omega
      simp only [matrixSequenceExtension,dite_eq_right hi,firstIncrement,ite_eq_right hz]
  have hF : matrixSequenceExtension (N+1) Θ.val.2 N=0 := by
    change matrixSequenceExtension (N+1) (S.canonicalParameters N).2 N=0
    rw [S.canonicalParameters_correction N le_rfl,ite_eq_right (by omega : ¬ N<N)]
    exact norm_eq_zero.mp (le_antisymm hS.2.2.2.2.1 (norm_nonneg _))
  have hΘ : ‖Θ‖≤ω := S.symmetricParameters_norm_le N base 0 (firstBudget ω) 0 0 hS hω
    (fun i _ => by
      by_cases hi : i=0
      · simp only [firstBudget,ite_eq_left hi,le_refl]
      · simpa only [firstBudget,ite_eq_right hi] using hω) hω hω
  have ht := hupper ω hω hωδ Θ hΘ M hM hMω hE hF
  -- Preserve the original physical method execution and its exact true CG normalization.
  have hcanA : scenarioProbe base Θ.val=scenarioProbe S.base (S.canonicalParameters N) := by rw [hbase]; rfl
  have hcanB : scenarioCorrection base Θ.val=scenarioCorrection S.base (S.canonicalParameters N) := by rw [hbase]; rfl
  rw [hcanA,hcanB,S.canonicalParameters_output N hS.1] at ht
  have hφ : 0<‖cgCanonicalError S.base g N‖ := by
    rw [hbase]
    exact krylov.Stability.canonical_error_pos base hb _ (cg_nonstagnation base hb g N (by omega))
  change _/‖cgCanonicalError S.base g N‖≤_
  apply (div_le_iff₀ hφ).mpr
  have hroot : metricRoot base=metricRoot S.base := congrArg metricRoot hbase.symm
  have hstep : ‖canonicalCGStep base g N‖=‖cgCanonicalError S.base g N‖ := by
    rw [hbase,terminal_step_error_norm base hb g (le_of_eq hcount.symm)]
  rw [hroot,hstep] at ht
  exact ht.trans_eq (mul_comm _ _)

end
end krylov.Information
