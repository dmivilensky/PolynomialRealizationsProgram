import krylov.Convergence.SS1FWindowBounds
import krylov.Convergence.WindowModelLimits

/-!
Article: main_krylov, thm:ss1F, genuine corrected-model superlinearity.
Use: original local derivative regularity and actual (S) split remainders
force the computed value model to converge and its real query to be
superlinear. The tensor budget is derived from the true third derivative.
Source: actual normalized value-model estimates and exact square-model
query, followed by continuity of matrix inversion at the identity.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.Secant
  krylov.Reference chebyshev1.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ} {α : Type*} {l : Filter α}

/-- Actual convergent value windows give a superlinear actual SS1-F query.
Every model error and inverse domain is derived from genuine derivatives
and the stated (S) hypothesis. No assumed model convergence is used. -/
theorem ss1F_source_superlinear
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (T : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) {L₂ L₃ : ℝ≥0}
    (hH : LipschitzOnWith L₂ H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    {B₀ : ℝ} (hB₀ : 0≤B₀) (hT₀ : ∀ h,‖h‖=1 → |(T 0).form h h h|≤B₀)
    (a b : α → Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (x : α → EuclideanSpace ℝ (Fin (n+1))) (split : α → Fin (n+1) → ℝ)
    (ha : ∀ i,Tendsto (fun z=>a z i) l (𝓝 0))
    (hb : ∀ i,Tendsto (fun z=>b z i) l (𝓝 0)) (hx : Tendsto x l (𝓝 0))
    {Cw C : ℝ} (hCw : 0≤Cw) (hC : 0≤C)
    (hmem : ∀ᶠ z in l,(∀ i,a z i∈S) ∧(∀ i,b z i∈S) ∧x z∈S)
    (hw : ∀ᶠ z in l,∀ i,‖splitRemainder (a z i) (b z i-a z i) (x z) (split z i)‖≤
      Cw*‖x z-b z i‖)
    (hind : ∀ᶠ z in l,IsUnit (windowMatrix (unitWindow (fun i=>b z i-a z i))).det ∧
      ‖(windowMatrix (unitWindow (fun i=>b z i-a z i)))⁻¹‖≤C) :
    (fun z=>ss1FPoint f G (a z) (fun i=>b z i-a z i) (split z) (x z)) =o[l] (fun z=>‖x z‖) := by
  let s := fun z i=>b z i-a z i
  let V := fun z=>windowMatrix (unitWindow (s z))
  let X := fun z=>ss1FNormalizedError f G (a z) (s z) (split z)
  let A := fun z=>secantMatrix (averagedDerivative H 0 (x z))
  let r := fun z=>sourceWindowRadius (a z) (b z)+‖x z‖
  let B := B₀+(L₃:ℝ)
  have hB : 0≤B := add_nonneg hB₀ L₃.coe_nonneg
  have hr : Tendsto r l (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun i _=>(ha i).norm.add (hb i).norm)
    have hh' : Tendsto (fun z=>sourceWindowRadius (a z) (b z)) l (𝓝 0) := by
      simpa only [sourceWindowRadius,norm_zero,add_zero,Finset.sum_const_zero] using hh
    simpa only [norm_zero,zero_add] using hh'.add hx.norm
  have hr₀ (z : α) : 0≤r z := add_nonneg (sourceWindowRadius_nonneg _ _) (norm_nonneg _)
  have hbound (z : α) (i : Fin (n+1)) : ‖a z i‖≤r z ∧‖b z i‖≤r z ∧‖x z‖≤r z := by
    have hh : ‖a z i‖+‖b z i‖≤sourceWindowRadius (a z) (b z) :=
      Finset.single_le_sum (fun j _=>add_nonneg (norm_nonneg (a z j)) (norm_nonneg (b z j)))
        (Finset.mem_univ i)
    exact ⟨by dsimp only [r]; linarith [norm_nonneg (b z i),norm_nonneg (x z)],
      by dsimp only [r]; linarith [norm_nonneg (a z i),norm_nonneg (x z)],
      by dsimp only [r]; linarith [sourceWindowRadius_nonneg (a z) (b z)]⟩
  have hs : ∀ᶠ z in l,∀ i,s z i≠0 := by
    filter_upwards [hind] with z hz i
    intro hi
    have hh := windowMatrix_step_ne_zero (unitWindow (s z)) hz.1 i
    apply hh
    simp only [unitWindow,krylov.Methods.rescaleWindow,hi,smul_zero]
  have hX : Tendsto X l (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [hmem,hw,hs,hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with z hz hwz hsz hrz
      apply ss1F_source_normalized_error_bound f G H T S hS h₀ hH hH₀ hf hG hT hLip
        (a z) (s z) (split z) (x z) hz.1 (by simpa only [s,add_sub_cancel] using hz.2.1)
        hz.2.2 (hr₀ z) hCw hB (fun i=>(hbound z i).1)
        (fun i=>by simpa only [s,add_sub_cancel] using (hbound z i).2.1) ((hbound z 0).2.2) hsz
      · intro i h hh
        have hd := hLip (b z i) (hz.2.1 i) 0 h₀ h hh
        have hdiag := hT₀ h hh
        have hnorm : ‖b z i‖≤1 := (hbound z i).2.1.trans hrz.le
        have hab : |(T (b z i)).form h h h|≤
            |(T (b z i)).form h h h-(T 0).form h h h|+|(T 0).form h h h| := by
          have hh := abs_add_le ((T (b z i)).form h h h-(T 0).form h h h) ((T 0).form h h h)
          simpa only [sub_add_cancel] using hh
        simpa only [s,add_sub_cancel,B] using hab.trans
          ((add_le_add (hd.trans (by simpa only [sub_zero,mul_one] using
            mul_le_mul_of_nonneg_left hnorm L₃.coe_nonneg)) hdiag).trans_eq (add_comm _ _))
      · simpa only [s,add_sub_cancel] using hwz
    · have ht : Tendsto (fun z=>valueWindowBudget L₂ L₃ B Cw (r z)) l (𝓝 0) := by
        have hh := ((hr.const_mul (L₂:ℝ)).add (hr.const_mul (2*B*Cw))).add
          ((hr.pow 2).const_mul ((L₃:ℝ)*(13/3+2*Cw)))
        simpa only [valueWindowBudget,mul_zero,zero_pow (by decide : 2≠0),add_zero] using hh
      simpa only [mul_zero] using ht.const_mul ((n+1:ℕ):ℝ)
  have hA : Tendsto A l (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (g:=fun z=>(L₂:ℝ)/2*‖x z‖)
    · exact Filter.Eventually.of_forall fun z=>norm_nonneg (A z-1)
    · filter_upwards [hmem] with z hz
      rw [show ‖A z-1‖=‖averagedDerivative H 0 (x z)-ContinuousLinearMap.id ℝ _‖ from secantMatrix_sub_one _]
      have hh := secant_operator_endpoint_bound H S hS h₀ hH 0 (x z) h₀ hz.2.2
      simpa only [hH₀,norm_zero,zero_add,sub_zero] using hh
    · simpa only [norm_zero,mul_zero] using hx.norm.const_mul ((L₂:ℝ)/2)
  have hh := conditioned_model_convergence V X A x hC (hind.mono fun _ h=>h.2) hX hA
  apply hh.2.2.2.2.congr'
  · filter_upwards [hind,hs,hmem] with z hz hsz hzm
    have hmodel := ss1F_normalized_model_error f G (a z) (s z) (split z) hz.1
    have hj : inverseCongruence (V z) (ss1FNormalizedModel f G (a z) (s z) (split z))=
        1+inverseCongruence (V z) (X z) := by rw [←hmodel]; abel
    have hrad : cgOperator (A z) (x z)=G (x z) := by
      rw [secantMatrix_operator]
      have hp t (ht : t∈Icc (0:ℝ) 1) : (0:EuclideanSpace ℝ (Fin (n+1)))+t • x z∈S :=
        hS.add_smul_mem h₀ (by simpa only [zero_add] using hzm.2.2) ht
      have hc := hH.continuousOn.comp
        (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
      simpa only [zero_add,hG₀,sub_zero] using
        averagedDerivative_apply G H 0 (x z) hc (fun t ht=>hG _ (hp t ht))
    rw [ss1FPoint_normalized_model f G (a z) (s z) (split z) (x z) hsz hz.1,hj,←hrad]
    rfl
  · exact Filter.EventuallyEq.refl _ _

end
end krylov.Convergence
