import krylov.Nonlinear.RFCSNonlinearSource
import krylov.Correction.RFCSReferenceTube

/-!
Article: main_krylov, thm:RFCS, uniform genuine nonlinear cubic transfer.
Use: Derive one actual cubic only-last-probe remainder for genuine RFC-S
cycles of a locally Lipschitz-Hessian function, uniformly before compact
full-active initial-gradient references and bounded nonzero finite probes.
Source: actual local gradient-error extension and query localization,
true averaged-Hessian transcript realization, the proved compact fixed-CG
source tube and the genuine quadratic initial-gradient bound.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Filter Topology Metric krylov.Methods krylov.Reference krylov.Correction
open scoped NNReal
variable {k : ℕ}

/-- Genuine finite-probe nonlinear RFC-S cycles of a locally Lipschitz-Hessian gradient have one uniform cubic remainder about their actual last averaged-Hessian mismatch acting on the original fixed quadratic CG reference step.
Use: Supply the full genuine nonlinear cubic transfer for the restarted only-last-probe theorem before estimating its self-concordant leading coefficient.
Article: main_krylov, thm:RFCS, actual uniform nonlinear cubic remainder.
Proof: Choose a genuine local gradient-error Lipschitz constant small enough for the proved compact query-localization theorem. That theorem encloses every real iterate and probe in a ball proportional to the true cycle size. The original Lipschitz Hessian therefore bounds all actual averaged-operator deviations by that size, while the genuine initial-gradient Taylor bound controls its normalized drift. Apply the actual nonlinear scaled quadratic source remainder on this shrinking real domain; multiplication by the cycle scale gives cubic order uniformly over every admitted reference and bounded probe sequence.
-/
theorem compact_rfcs_nonlinear_cubic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (r B T : ℝ) (hr : 0<r) (hB : 0<B) (hT : 0≤T)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0}
    (hH : LipschitzOnWith L H (ball 0 r)) (hG : ∀ x∈ball 0 r, HasFDerivAt G (H x) x) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) → (∀ i<k+1, |h i|≤T) →
      ‖G (rfcSFunctionPoint fullMemory G (ε • u) h (k+1))-
        ε • ((rfcSFunctionSegment fullMemory G H (ε • u) h k-rfcSFunctionProbeOperator fullMemory G H (ε • u) h k)
          (referenceStep (cgOperator base) (cgOperator base u) k))‖≤C*ε^3 := by
  obtain ⟨ε₁,_,Cs,hε₁,_,hCs,hprofile⟩ := compact_rfcs_nonlinear_source base hb K hK hN G H r B T hr hB hT hG₀ hH₀ hH hG
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_rfcs_fixed_reference_quadratic_tube base hb K hK hN hk
  refine ⟨min ε₁ (δ/(Cs+1)),C*Cs^2+1,lt_min hε₁ (div_pos hδ (by positivity)),by positivity,?_⟩
  intro ε hε he u hu hKu h hh hTbound
  have hs := hprofile ε hε (he.trans_le (min_le_left _ _)) u hu hKu h hh hTbound
  let Θ := rfcSFunctionSource base G H (ε • u) h
  let g := cgOperator base u
  let v := ε⁻¹ • G (ε • u)-g
  let z := (g+v,Θ)
  have hnorm : ‖(v,Θ)‖≤Cs*ε := hs.1
  have hsmall : Cs*ε≤δ := by
    have he' := (lt_div_iff₀ (by positivity : 0<Cs+1)).mp (he.trans_le (min_le_right _ _))
    nlinarith
  have hestimate := hbound g hKu v Θ (hnorm.trans hsmall)
  have hv : g+v=ε⁻¹ • G (ε • u) := by dsimp only [v]; abel
  have hrun : rfcSFunctionRun fullMemory G (ε • u) h (k+1)=
      rfcSRun fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) (G (ε • u)) (k+1) := by
    dsimp only [z]
    rw [hv]
    exact (hs.2.1 (k+1) le_rfl).1
  have hgrad := congrArg History.gradient hrun
  rw [rfcSFunctionRun_gradient] at hgrad
  change G (rfcSFunctionPoint fullMemory G (ε • u) h (k+1))=
    rfcSGradient fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) (G (ε • u)) (k+1) at hgrad
  have hscale : G (ε • u)=ε • (g+v) := by rw [hv,smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  rw [hscale,(rfcS_scalar fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z)
    (g+v) ε hε.ne' (k+1)).1] at hgrad
  change G (rfcSFunctionPoint fullMemory G (ε • u) h (k+1))=ε • rfcsDirectOutput base z at hgrad
  have hmismatch : rfcsDirectLine base z k-rfcsDirectProbe base z k=
      rfcSFunctionSegment fullMemory G H (ε • u) h k-rfcSFunctionProbeOperator fullMemory G H (ε • u) h k := by
    dsimp only [rfcsDirectProbe]
    rw [sub_sub_cancel]
    simp only [rfcsOperatorAt,dite_eq_left (Nat.lt_succ_self k)]
    rfl
  rw [← hmismatch,hgrad,← smul_sub,norm_smul,Real.norm_of_nonneg hε.le]
  calc
    _ ≤ ε*(C*‖(v,Θ)‖^2) := mul_le_mul_of_nonneg_left hestimate hε.le
    _ ≤ ε*(C*(Cs*ε)^2) := by gcongr
    _ = (C*Cs^2)*ε^3 := by ring
    _ ≤ (C*Cs^2+1)*ε^3 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end
end krylov.Nonlinear
