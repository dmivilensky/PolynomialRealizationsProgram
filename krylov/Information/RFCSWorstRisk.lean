import krylov.Information.RFCSSourceBounds

/-!
Article: main_krylov, thm:RFCS, sharp actual finite-source probe bound.
Use: one real quadratic remainder tube covers every original finite
increment and independent probe-defect scenario; actual final isotropic
probe witnesses attain the sharp first-order coefficient.
Source: genuine independent-probe execution and full terminal expansion,
actual finite symmetric source coordinates and original spectral budgets.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Envelope krylov.Variation krylov.Correction krylov.Secant
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {k : ℕ}

/-- The actual RFC-S source supremum has sharp coefficient equal to the original final-probe budget and one common quadratic bracket over all admissible profiles.
Use: exact final probes give a true quadratic source bound, and no earlier probe contributes a first-order worst-case term.
Article: main_krylov, thm:RFCS, genuine sharp physical-source risk.
Proof: every actual source obeys the genuine common upper bound. The real last-isotropic-probe witness satisfies both original budgets and gives the common lower endpoint inside the true source supremum. -/

theorem rfcs_worst_quadratic_bracket (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ μ p : ℝ, 0≤p → p≤μ → μ≤δ →
      ENNReal.ofReal (p-C*μ^2)≤rfcsWorstOutputRatio base g μ p ∧
        rfcsWorstOutputRatio base g μ p≤ENNReal.ofReal (p+C*μ^2) := by
  -- Compare the true source supremum with its actual common finite-budget endpoints.
  obtain ⟨δ,C,hδ,hC,hbound⟩ := rfcs_source_sharp_bounds base hb g hN hk
  refine ⟨δ,C,hδ,hC,?_⟩
  intro μ p hp hpμ hμδ
  obtain ⟨hu,hl⟩ := hbound μ p hp hpμ hμδ
  constructor
  · apply (ENNReal.ofReal_le_ofReal hl).trans
    unfold rfcsWorstOutputRatio
    have hΘ : ‖rfcsLastProbeScenario k p‖≤μ :=
      (rfcsLastProbeScenario_spec k p).1.trans (by simpa only [abs_of_nonneg hp] using hpμ)
    have hlast : ‖matrixSequenceExtension (k+1) (rfcsLastProbeScenario k p).val.2 k‖≤p := by
      rw [(rfcsLastProbeScenario_spec k p).2]
      simp only [norm_smul,Real.norm_of_nonneg hp,norm_one,mul_one,le_refl]
    exact le_iSup_of_le (⟨rfcsLastProbeScenario k p,hΘ,hlast⟩ :
      {Θ : symmetricScenarios (k+1) (k+1) // ‖Θ‖≤μ ∧ ‖matrixSequenceExtension (k+1) Θ.val.2 k‖≤p}) le_rfl
  · exact iSup_le fun Θ => ENNReal.ofReal_le_ofReal (hu Θ.val Θ.property.1 Θ.property.2)


/-- The genuine RFC-S source supremum is finite and its real value differs from the original final-probe budget by at most one uniform quadratic amount.
Use: the sharp coefficient describes a true finite real worst physical risk, including zero final-probe and zero total budgets.
Article: main_krylov, thm:RFCS, genuine sharp physical-source risk.
Proof: the genuine common bracket supplies a finite upper endpoint. The proved real-risk conversion gives finiteness and the sharp-coefficient absolute-error bound. -/
theorem rfcs_worst_quadratic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ μ p : ℝ, 0≤p → p≤μ → μ≤δ →
      rfcsWorstOutputRatio base g μ p≠⊤ ∧ |(rfcsWorstOutputRatio base g μ p).toReal-p|≤C*μ^2 := by
  -- Compare the true source supremum with its actual common finite-budget endpoints.
  obtain ⟨δ,C,hδ,hC,hbound⟩ := rfcs_worst_quadratic_bracket base hb g hN hk
  refine ⟨δ,C,hδ,hC,?_⟩
  intro μ p hp hpμ hμδ
  obtain ⟨hl,hu⟩ := hbound μ p hp hpμ hμδ
  exact realRisk_bracket hp (mul_nonneg hC.le (sq_nonneg μ)) hl hu


/-- The genuine RFC-S worst-source risk has exactly the original last-probe leading coefficient and literal quadratic remainder along every shrinking admissible budget family.
Use: complete the source operator-model sharpness statement for the real finite-history executor.
Article: main_krylov, thm:RFCS, genuine sharp physical-source risk.
Proof: every shrinking largest budget eventually enters the actual common tube. Its genuine finite source supremum obeys the proved quadratic absolute-error estimate, which is exactly the Big-O claim. -/
theorem rfcs_worst_asymptotic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (T : Type*) (l : Filter T) (μ p : T → ℝ) (htend : Tendsto μ l (𝓝 0))
    (hprofile : ∀ᶠ t in l, 0≤p t ∧ p t≤μ t) :
    (fun t => (rfcsWorstOutputRatio base g (μ t) (p t)).toReal-p t)=O[l] (fun t => (μ t)^2) := by
  -- Compare the true source supremum with its actual common finite-budget endpoints.
  obtain ⟨δ,C,hδ,_,hbound⟩ := rfcs_worst_quadratic base hb g hN hk
  have hsmall : ∀ᶠ t in l, μ t≤δ := ((tendsto_order.mp htend).2 δ hδ).mono fun _ ht => ht.le
  apply isBigO_iff.mpr ⟨C,?_⟩
  filter_upwards [hsmall,hprofile] with t ht hp
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (μ t))] using (hbound (μ t) (p t) hp.1 hp.2 ht).2

end
end krylov.Information
