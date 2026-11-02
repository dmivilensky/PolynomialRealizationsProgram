import krylov.Nonlinear.RFCSNonlinearSource
import krylov.Nonlinear.RFCSFunctionFields
import krylov.Correction.RFCSAlphaBounds

/-!
Article: main_krylov, thm:RFCS, genuine uniform nonlinear search geometry.
Use: Derive actual positive search lengths and quadratic physical line-step
and correction changes for real nonlinear RFC-S cycles from their original
local Hessian data, uniformly over compact full-active references and all
bounded nonzero finite probes.
Source: the genuine shared nonlinear source profile, exact actual scaled
search-field dictionary and proved compact source length/field estimates.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Correction
open scoped NNReal
variable {k : ℕ}

/-- Actual nonlinear RFC-S search lengths remain positive and within a uniform first-order change of their true CG values, while their genuine line steps and physical corrections have uniform quadratic changes at the original cycle scale.
Use: Bound the true last probe/full-step mismatch with its actual line-search error and correction, preserving the sharp self-concordant leading coefficient.
Article: main_krylov, thm:RFCS, actual nonlinear line and correction estimates.
Proof: The shared genuine nonlinear source theorem bounds the actual joint initial-gradient/operator drift and identifies every true recorded prefix. The exact scaled field dictionary transfers the compact source length and line/correction estimates to the real nonlinear executor. Positive source lengths give the actual search domain; true line and correction homogeneity supplies the extra cycle-scale factor.
-/
theorem compact_rfcs_nonlinear_search_geometry (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (r B T : ℝ) (hr : 0<r) (hB : 0<B) (hT : 0≤T)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0}
    (hH : LipschitzOnWith L H (ball 0 r)) (hG : ∀ x∈ball 0 r, HasFDerivAt G (H x) x) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) → (∀ i<k+1, |h i|≤T) → ∀ i<k+1,
      0<rfcSFunctionAlpha fullMemory G (ε • u) h i ∧
      CG.length (cgOperator base) (cgOperator base u) i/2≤rfcSFunctionAlpha fullMemory G (ε • u) h i ∧
      |rfcSFunctionAlpha fullMemory G (ε • u) h i-CG.length (cgOperator base) (cgOperator base u) i|≤C*ε ∧
      ‖rfcSFunctionLineStep fullMemory G (ε • u) h i-ε • referenceStep (cgOperator base) (cgOperator base u) i‖≤C*ε^2 ∧
      ‖rfcSFunctionCorrection fullMemory G (ε • u) h i‖≤C*ε^2 := by
  obtain ⟨ε₁,_,Cs,hε₁,_,hCs,hprofile⟩ := compact_rfcs_nonlinear_source base hb K hK hN G H r B T hr hB hT hG₀ hH₀ hH hG
  obtain ⟨δ₀,C,hδ₀,hC,hchanges⟩ := compact_rfcs_search_field_changes base hb K hK hN
  obtain ⟨δ₁,hδ₁,hlength⟩ := compact_rfcs_relative_length_bounds base hb K hK hN
  let δ := min δ₀ δ₁
  have hδ : 0<δ := lt_min hδ₀ hδ₁
  refine ⟨min ε₁ (δ/(Cs+1)),C*Cs+1,lt_min hε₁ (div_pos hδ (by positivity)),by positivity,?_⟩
  intro ε hε he u hu hKu h hh hTbound i hi
  have hs := hprofile ε hε (he.trans_le (min_le_left _ _)) u hu hKu h hh hTbound
  let Θ := rfcSFunctionSource base G H (ε • u) h
  let g := cgOperator base u
  let v := ε⁻¹ • G (ε • u)-g
  let z := (g+v,Θ)
  have hnorm : ‖(v,Θ)‖≤Cs*ε := hs.1
  have hsmall : Cs*ε≤δ := by
    have he' := (lt_div_iff₀ (by positivity : 0<Cs+1)).mp (he.trans_le (min_le_right _ _))
    nlinarith
  have hinput := hnorm.trans hsmall
  have hchange := hchanges g hKu v Θ (hinput.trans (min_le_left _ _)) i hi
  have hlen := hlength g hKu v Θ (hinput.trans (min_le_right _ _)) i hi
  have hv : g+v=ε⁻¹ • G (ε • u) := by dsimp only [v]; abel
  have hscale : G (ε • u)=ε • (g+v) := by rw [hv,smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hrun j (hj : j≤k+1) : rfcSFunctionRun fullMemory G (ε • u) h j=
      rfcSRun fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) (ε • (g+v)) j := by
    rw [← hscale]
    dsimp only [z]
    rw [hv]
    exact (hs.2.1 j hj).1
  -- Read the actual newest finite probe and total step from the true common recorded prefixes before scaling the line and physical correction.
  have hfields := rfcSFunction_scaled_operator_fields fullMemory G (ε • u) h
    (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) (g+v) ε hε.ne' i
    (hrun i hi.le) (hrun (i+1) (by omega))
  change rfcSFunctionAlpha fullMemory G (ε • u) h i=rfcsDirectAlpha base i z ∧
    rfcSFunctionLineStep fullMemory G (ε • u) h i=ε • rfcsDirectLineStep base i z ∧
    rfcSFunctionCorrection fullMemory G (ε • u) h i=ε • rfcsDirectCorrection base i z at hfields
  rw [hfields.1,hfields.2.1,hfields.2.2,← smul_sub,norm_smul,norm_smul,Real.norm_of_nonneg hε.le]
  refine ⟨hlen.1,hlen.2.1,?_,?_,?_⟩
  · exact (hchange.1.trans (mul_le_mul_of_nonneg_left hnorm hC.le)).trans (by nlinarith)
  · calc
      _ ≤ ε*(C*‖(v,Θ)‖) := mul_le_mul_of_nonneg_left hchange.2.1 hε.le
      _ ≤ ε*(C*(Cs*ε)) := by gcongr
      _ ≤ (C*Cs+1)*ε^2 := by nlinarith [sq_nonneg ε]
  · calc
      _ ≤ ε*(C*‖(v,Θ)‖) := mul_le_mul_of_nonneg_left hchange.2.2 hε.le
      _ ≤ ε*(C*(Cs*ε)) := by gcongr
      _ ≤ (C*Cs+1)*ε^2 := by nlinarith [sq_nonneg ε]

end
end krylov.Nonlinear
