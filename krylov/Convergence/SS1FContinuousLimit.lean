import krylov.Convergence.SS1FContinuousSource
import krylov.Convergence.WindowModelLimits

/-!
Article: main_krylov, thm:ss1F, continuous-D3 source superlinearity.
Use: genuine function values and continuous third derivatives force the
actual corrected matrix and its inverse to converge, with no assumed
model limit and no Lipschitz-third hypothesis.
Source: the anchored continuous trapezoid modulus and the exact observed
query identity; matrix inversion is continuous at the identity.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.Secant
  krylov.Reference chebyshev1.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ} {α : Type*} {l : Filter α}

local notation "E" => EuclideanSpace ℝ (Fin (n+1))
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Continuity of the genuine scalar third derivative supplies an
arbitrarily small oscillation on a convex local source neighborhood, and
its mixed budget is derived with the original spectral norm at zero. -/
theorem continuous_third_source_neighborhood
    (T : E → SymmetricCubic E) (S : Set E) (hS : Convex ℝ S)
    (hnbhd : S∈𝓝 (0:E)) (hc : ContinuousOn (fun z=>(T z).form) S)
    {η : ℝ} (hη : 0<η) :
    ∃ U : Set E,Convex ℝ U ∧(0:E)∈U ∧U∈𝓝 (0:E) ∧U⊆S ∧
      ThirdVariationOscillationOn (fun z=>(T z).form) η U ∧
      ∀ z∈U,∀ u v w,|(T z).form u v w|≤
        (‖canonicalVariation (T 0)‖+η)*‖u‖*‖v‖*‖w‖ := by
  have hcc : ContinuousAt (fun z=>(T z).form) 0 := hc.continuousAt hnbhd
  obtain ⟨r,hr,hmod⟩ := thirdVariationOscillation_small_ball (fun z=>(T z).form) 0 hcc η hη
  let U := S∩Metric.ball 0 r
  have hU₀ : (0:E)∈U := ⟨mem_of_mem_nhds hnbhd,Metric.mem_ball_self hr⟩
  refine ⟨U,hS.inter (convex_ball _ _),hU₀,inter_mem hnbhd (Metric.ball_mem_nhds _ hr),
    inter_subset_left,fun z hz w hw u v t=>hmod z hz.2 w hw.2 u v t,?_⟩
  intro z hz u v w
  have hd := hmod z hz.2 0 hU₀.2 u v w
  have hzero := krylov.Tensor.cubic_diagonal_bound (T 0) ‖canonicalVariation (T 0)‖
    (canonicalVariation_unit_diagonal_bound (T 0)) u v w
  have hh := abs_add_le ((T z).form u v w-(T 0).form u v w) ((T 0).form u v w)
  simp only [sub_add_cancel] at hh
  exact hh.trans ((add_le_add hd hzero).trans_eq (by ring))

/-- Bounded genuine continuous-D3 source version of the actual query limit.
The local budgets will be supplied by continuity on a shrinking ball. -/
theorem ss1F_continuous_bounded_source_superlinear
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (T : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hc : ContinuousOn (fun z=>(T z).form) S)
    {η B : ℝ} (hη : 0≤η) (hB : 0≤B)
    (hmod : ThirdVariationOscillationOn (fun z=>(T z).form) η S)
    (hbudget : ∀ z∈S,∀ u v w,|(T z).form u v w|≤B*‖u‖*‖v‖*‖w‖)
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
  let L₂ : ℝ≥0 := Real.toNNReal B
  have hH := hessian_lipschitz_of_third_spectral_bound H T S hS hT hB (by
    intro z hz u hu
    simpa only [hu,mul_one] using hbudget z hz u u u)
  let s := fun z i=>b z i-a z i
  let V := fun z=>windowMatrix (unitWindow (s z))
  let X := fun z=>ss1FNormalizedError f G (a z) (s z) (split z)
  let A := fun z=>secantMatrix (averagedDerivative H 0 (x z))
  let r := fun z=>sourceWindowRadius (a z) (b z)+‖x z‖
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
    · filter_upwards [hmem,hw,hs] with z hz hwz hsz
      apply ss1F_continuous_normalized_error_bound f G H T S hS h₀ hH₀ hf hG hT hc
        hη hB hmod hbudget (a z) (s z) (split z) (x z) hz.1
        (by simpa only [s,add_sub_cancel] using hz.2.1) hz.2.2 (hr₀ z) hCw
        (fun i=>(hbound z i).1)
        (fun i=>by simpa only [s,add_sub_cancel] using (hbound z i).2.1)
        ((hbound z 0).2.2) hsz
      simpa only [s,add_sub_cancel] using hwz
    · simpa only [mul_zero] using
        hr.const_mul (((n+1:ℕ):ℝ)*(B+2*B*Cw+2*η*(3+Cw)))
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


/-- Original continuous-D3 regularity suffices for the actual corrected
query's superlinearity. All local tensor budgets and oscillation bounds
are derived from continuity at the genuine critical point. -/
theorem ss1F_continuous_source_superlinear
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (T : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hc : ContinuousOn (fun z=>(T z).form) S)
    (a b : α → Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (x : α → EuclideanSpace ℝ (Fin (n+1))) (split : α → Fin (n+1) → ℝ)
    (ha : ∀ i,Tendsto (fun z=>a z i) l (𝓝 0))
    (hb : ∀ i,Tendsto (fun z=>b z i) l (𝓝 0)) (hx : Tendsto x l (𝓝 0))
    {Cw C : ℝ} (hCw : 0≤Cw) (hC : 0≤C)
    (hw : ∀ᶠ z in l,∀ i,‖splitRemainder (a z i) (b z i-a z i) (x z) (split z i)‖≤
      Cw*‖x z-b z i‖)
    (hind : ∀ᶠ z in l,IsUnit (windowMatrix (unitWindow (fun i=>b z i-a z i))).det ∧
      ‖(windowMatrix (unitWindow (fun i=>b z i-a z i)))⁻¹‖≤C) :
    (fun z=>ss1FPoint f G (a z) (fun i=>b z i-a z i) (split z) (x z)) =o[l] (fun z=>‖x z‖) := by
  have hcc : ContinuousAt (fun z=>(T z).form) 0 := hc.continuousAt hnbhd
  obtain ⟨r,hr,hmod⟩ := thirdVariationOscillation_small_ball (fun z=>(T z).form) 0 hcc 1 (by norm_num)
  let U := S∩Metric.ball 0 r
  let B := ‖canonicalVariation (T 0)‖+1
  have hU : Convex ℝ U := hS.inter (convex_ball _ _)
  have hU₀ : (0:E)∈U := ⟨h₀,Metric.mem_ball_self hr⟩
  have hUn : U∈𝓝 (0:E) := inter_mem hnbhd (Metric.ball_mem_nhds _ hr)
  have hB : 0≤B := by dsimp only [B]; positivity
  have hbudget : ∀ z∈U,∀ u v w,|(T z).form u v w|≤B*‖u‖*‖v‖*‖w‖ := by
    intro z hz u v w
    have hd := hmod z hz.2 0 hU₀.2 u v w
    have hzero := krylov.Tensor.cubic_diagonal_bound (T 0) ‖canonicalVariation (T 0)‖
      (canonicalVariation_unit_diagonal_bound (T 0)) u v w
    have hh := abs_add_le ((T z).form u v w-(T 0).form u v w) ((T 0).form u v w)
    simp only [sub_add_cancel] at hh
    exact hh.trans ((add_le_add hd hzero).trans_eq (by dsimp only [B]; ring))
  have hmem : ∀ᶠ z in l,(∀ i,a z i∈U) ∧(∀ i,b z i∈U) ∧x z∈U := by
    have h₁ := Filter.eventually_all.mpr (fun i=>(ha i).eventually hUn)
    have h₂ := Filter.eventually_all.mpr (fun i=>(hb i).eventually hUn)
    exact (h₁.and (h₂.and (hx.eventually hUn)))
  exact ss1F_continuous_bounded_source_superlinear f G H T U hU hU₀ hH₀
    (fun z hz=>hf z hz.1) (fun z hz=>hG z hz.1) hG₀ (fun z hz=>hT z hz.1)
    (hc.mono inter_subset_left) (by norm_num : (0:ℝ)≤1) hB
    (fun z hz w hw u v t=>hmod z hz.2 w hw.2 u v t) hbudget a b x split ha hb hx
    hCw hC hmem hw hind

end
end krylov.Convergence
