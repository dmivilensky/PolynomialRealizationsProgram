import krylov.Nonlinear.RFCSNonlinearSource
import krylov.Nonlinear.RFCSFunctionFields
import krylov.Correction.RFCSDomainScaling

/-!
Article: main_krylov, thm:RFCS, actual uniform nonlinear inverse/gate domains.
Use: Prove the genuine physical observed solves and branches of every small
nonlinear cycle from its real gradient and local Lipschitz Hessian.
Source: actual query localization and averaged-Hessian source realization,
compact reference domains and proved nonzero-scale domain covariance.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Correction
open scoped NNReal InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}

/-- Every sufficiently small actual nonlinear RFC-S cycle has genuine nonsingular old and augmented observed solves, positive measured probe curvature and accepted nonempty defect gate, uniformly before the compact reference and bounded finite probes.
Use: Discharge actual physical well-definedness from local function hypotheses without assuming a trajectory domain or a gate conclusion.
Article: main_krylov, thm:RFCS, actual uniform nonlinear inverse/gate domains.
Proof: The genuine nonlinear source has size at most Cε in one compact reference tube. The source domains therefore apply uniformly. Exact nonzero gradient scaling transfers both inverse domains, curvature and gate to the physical cycle, and the complete real prefix dictionary identifies its actual observed list matrices and true measured probe.
-/
theorem compact_rfcs_nonlinear_domains (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (r B T : ℝ) (hr : 0<r) (hB : 0<B) (hT : 0≤T)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0}
    (hH : LipschitzOnWith L H (ball 0 r)) (hG : ∀ x∈ball 0 r, HasFDerivAt G (H x) x) :
    ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) → (∀ i<k+1, |h i|≤T) → ∀ i<k+1,
      let H := rfcSFunctionRun fullMemory G (ε • u) h i
      let R := rfcSFunctionRecord fullMemory G (ε • u) (h i) H
      observedCorrectionDomain (selectedWindow fullMemory H) R.direction R.probe := by
  obtain ⟨ε₁,D,C,hε₁,_hD,hC,hsource⟩ := compact_rfcs_nonlinear_source base hb K hK hN
    G H r B T hr hB hT hG₀ hH₀ hH hG
  obtain ⟨δ,hδ,hdomains⟩ := compact_rfcs_direct_domains base hb K hK hN
  refine ⟨min ε₁ (δ/(C+1)),lt_min hε₁ (div_pos hδ (by positivity)),?_⟩
  intro ε hε he u hu hKu h hh hTbound i hi
  dsimp only
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu hKu h hh hTbound
  let Θ := rfcSFunctionSource base G H (ε • u) h
  let z := (ε⁻¹ • G (ε • u),Θ)
  have heδ : C*ε≤δ := by
    have he' := (lt_div_iff₀ (by positivity : 0<C+1)).mp (he.trans_le (min_le_right _ _))
    nlinarith
  have hnorm : ‖(ε⁻¹ • G (ε • u)-cgOperator base u,Θ)‖≤δ := hs.1.trans heδ
  have hdn : rfcsDirectIterationDomain base i z := by
    have ht := hdomains (cgOperator base u) hKu (ε⁻¹ • G (ε • u)-cgOperator base u) Θ hnorm i hi
    have hc : cgOperator base u+(ε⁻¹ • G (ε • u)-cgOperator base u)=ε⁻¹ • G (ε • u) := by abel
    rw [hc] at ht
    exact ht
  have hdp := rfcs_direct_domain_scalar base z.1 Θ ε hε.ne' i hdn
  have hcancel : ε • z.1=G (ε • u) := by
    change ε • (ε⁻¹ • G (ε • u))=_
    rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  rw [hcancel] at hdp
  have hobs := rfcs_direct_domain_observed base i (G (ε • u),Θ) hdp
  have hpre := (hs.2.1 i hi.le).1
  have hnext := (hs.2.1 (i+1) (by omega)).1
  have hfields := rfcSFunctionRecord_operator_fields fullMemory G (ε • u) h
    (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) (G (ε • u)) i hpre hnext
  rw [hfields.1,hfields.2.1,hpre]
  exact hobs

end
end krylov.Nonlinear
