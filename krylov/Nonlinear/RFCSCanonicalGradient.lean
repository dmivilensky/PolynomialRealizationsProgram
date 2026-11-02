import krylov.Nonlinear.RFCSLastProbeUniform
import krylov.Nonlinear.RFCSNonlinearCubic

/-!
Article: main_krylov, thm:RFCS, genuine canonical nonlinear gradient bound.
Use: Insert the true last-probe mismatch estimate into the actual nonlinear
cubic output remainder while retaining the literal executed relative probe
factor on the squared original reference last-step norm.
Source: genuine nonlinear cubic transfer, actual canonical last-probe
geometry and fixed continuous-linear metric normalization.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Correction
open scoped NNReal
variable {k : ℕ}

/-- Genuine nonlinear RFC-S cycles with actual canonical Hessian control have normalized output gradient bounded by the true executed relative last-probe error times the squared original reference last-step norm, plus one uniform cubic cycle remainder.
Use: Establish the exact leading coefficient before passing from the actual canonical gradient to the actual error norm.
Article: main_krylov, thm:RFCS, actual canonical nonlinear output estimate.
Proof: The actual finite-probe restriction gives a bounded genuine query family. Normalize the true nonlinear cubic remainder by the fixed inverse coordinate map and identify its leading action by exact congruence. The proved genuine last-probe bound supplies the literal leading factor; compact reference step bounds absorb only the remaining cubic terms.
-/
theorem compact_rfcs_coordinate_gradient_bound (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (r B Cp ρ : ℝ) (hr : 0<r) (hB : 0<B) (hCp : 0<Cp) (hρ : 0<ρ)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0}
    (hH : LipschitzOnWith L H (ball 0 r)) (hG : ∀ x∈ball 0 r, HasFDerivAt G (H x) x)
    (hcan : ∀ R : ℝ, 0<R → R≤ρ → LipschitzOnWith (Real.toNNReal (2+10000*R)) (coordinateDerivative T H) (ball 0 R)) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) →
      (∀ i<k+1, 0<h i ∧ h i≤Cp*CG.length (cgOperator base) (cgOperator base u) i) →
      ‖T.symm (G (rfcSFunctionPoint fullMemory G (ε • u) h (k+1)))‖≤
      |1-h k/rfcSFunctionAlpha fullMemory G (ε • u) h k| *
        (ε*‖T (referenceStep (cgOperator base) (cgOperator base u) k)‖)^2+C*ε^3 := by
  obtain ⟨εp,Cp',hεp,hCp',hprobe⟩ := compact_rfcs_coordinate_last_probe_bound base hb K hK hN T G H r B Cp ρ hr hB hCp hρ hG₀ hH₀ hH hG hcan
  obtain ⟨Mα,hMα,hαref⟩ := compact_rfcs_reference_length_bounds base hb K hK hN
  obtain ⟨εc,Cc,hεc,hCc,hcubic⟩ := compact_rfcs_nonlinear_cubic base hb K hK hN hk G H r B (Cp*Mα) hr hB
    (mul_pos hCp hMα).le hG₀ hH₀ hH hG
  obtain ⟨δ,M,hδ,hM,hprefix⟩ := compact_rfcs_operator_prefix_bounds base hb K hK hN
  have href g (hg : g∈K) : ‖referenceStep (cgOperator base) g k‖≤M := by
    have hh := ((hprefix g hg 0 0 (by simp only [Prod.norm_mk,norm_zero,max_self]; linarith)).2 k (Nat.lt_succ_self k)).2
    rw [add_zero] at hh
    have hz := (rfcs_direct_alpha_reference base hb g k).2.2
    unfold rfcsDirectCorrection at hz
    rw [(rfcs_direct_alpha_reference base hb g k).2.1] at hz
    rw [sub_eq_zero.mp hz] at hh
    exact hh
  let Mref := (‖T.toContinuousLinearMap‖+1)*M+1
  have hMref : 0<Mref := by dsimp only [Mref]; positivity
  let C := ‖T.symm.toContinuousLinearMap‖*Cc+Cp'*Mref+1
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨min εp εc,C,lt_min hεp hεc,hC,?_⟩
  intro ε hε he u hu hKu h hh hrel
  have hp := hprobe ε hε (he.trans_le (min_le_left _ _)) u hu hKu h hh hrel
  have habs i (hi : i<k+1) : |h i|≤Cp*Mα := by
    rw [abs_of_pos (hrel i hi).1]
    exact (hrel i hi).2.trans (mul_le_mul_of_nonneg_left (hαref _ hKu i hi).2.2 hCp.le)
  have hc := hcubic ε hε (he.trans_le (min_le_right _ _)) u hu hKu h hh habs
  let x := rfcSFunctionPoint fullMemory G (ε • u) h (k+1)
  let s := referenceStep (cgOperator base) (cgOperator base u) k
  let P := rfcSFunctionSegment fullMemory G H (ε • u) h k-rfcSFunctionProbeOperator fullMemory G H (ε • u) h k
  let Pc := coordinateCongruence T P
  let E := |1-h k/rfcSFunctionAlpha fullMemory G (ε • u) h k|
  let e := ‖T s‖
  have heRef : e≤Mref := by
    have hn := T.toContinuousLinearMap.le_opNorm s
    simp only [ContinuousLinearEquiv.coe_coe] at hn
    apply hn.trans
    apply (mul_le_mul_of_nonneg_left (href _ hKu) (norm_nonneg T.toContinuousLinearMap)).trans
    dsimp only [Mref]
    nlinarith
  have hpc : T.symm (P s)=Pc (T s) := by
    change T.symm (P s)=T.symm (P (T.symm (T s)))
    rw [T.symm_apply_apply]
  have hrem : ‖T.symm (G x)-ε • Pc (T s)‖≤(‖T.symm.toContinuousLinearMap‖*Cc)*ε^3 := by
    have hn := T.symm.toContinuousLinearMap.le_opNorm (G x-ε • P s)
    simp only [map_sub,map_smul,ContinuousLinearEquiv.coe_coe,hpc] at hn
    exact hn.trans ((mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans_eq (by ring))
  have hleading : ‖ε • Pc (T s)‖≤ε*((E*ε*e+Cp'*ε^2)*e) := by
    rw [norm_smul,Real.norm_of_nonneg hε.le]
    apply (mul_le_mul_of_nonneg_left (Pc.le_opNorm (T s)) hε.le).trans
    apply mul_le_mul_of_nonneg_left _ hε.le
    exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
  have hnorm : ‖T.symm (G x)‖≤‖T.symm (G x)-ε • Pc (T s)‖+‖ε • Pc (T s)‖ := by
    simpa only [sub_add_cancel] using norm_add_le (T.symm (G x)-ε • Pc (T s)) (ε • Pc (T s))
  change ‖T.symm (G x)‖≤E*(ε*e)^2+C*ε^3
  calc
    _ ≤ ‖T.symm.toContinuousLinearMap‖*Cc*ε^3+ε*((E*ε*e+Cp'*ε^2)*e) := hnorm.trans (add_le_add hrem hleading)
    _ = E*(ε*e)^2+(‖T.symm.toContinuousLinearMap‖*Cc+Cp'*e)*ε^3 := by ring
    _ ≤ E*(ε*e)^2+C*ε^3 := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp only [C]
      nlinarith [mul_le_mul_of_nonneg_left heRef hCp'.le]

end
end krylov.Nonlinear
