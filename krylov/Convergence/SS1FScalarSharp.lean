import krylov.Convergence.SS1FOriginalRegularity
import krylov.Convergence.SS1FScalarModel
import krylov.Convergence.WindowWeightedAges
import krylov.Convergence.WindowSharpQuery

/-!
Article: main_krylov, thm:ss1F, original scalar sharp estimate.
Use: (S) forces the actual endpoint split to one half. Comparing the real
computed curvature directly with radial curvature preserves T3/2 before
taking absolute values; the genuine trapezoid kernel contributes L3/12.
Source: actual scalar model cancellation, original C3,1 and the true
recursive execution. Zero tensor weights and zero errors are included.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.LinearAlgebra
  krylov.Secant krylov.Reference chebyshev1.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
set_option maxHeartbeats 1000000

/-- The genuine scalar SS1-F errors satisfy the stronger exact T3/2 and
L3/12 estimate. Its leading coefficient is below the printed general
(Cw+1/2)T3/σ² bound. -/
theorem ss1FSequence_scalar_sharp_asymptotic
    (f : EuclideanSpace ℝ (Fin (1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (1)) → EuclideanSpace ℝ (Fin (1)))
    (H : EuclideanSpace ℝ (Fin (1)) → EuclideanSpace ℝ (Fin (1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (1)))
    (T : EuclideanSpace ℝ (Fin (1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (1))))
    (S : Set (EuclideanSpace ℝ (Fin (1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (1)))∈S) (hnbhd : S∈𝓝 0)
    {R : ℝ} (hR : 0≤R) (hbounded : ∀ z∈S,‖z‖≤R) {L₃ : ℝ≥0} (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    (split : (Fin (2) → EuclideanSpace ℝ (Fin (1))) → Fin (1) → ℝ)
    (seed : Fin (2) → EuclideanSpace ℝ (Fin (1)))
    (hconv : Tendsto (ss1FSequence f G split seed) atTop (𝓝 0))
    {Cw σ : ℝ} (hCw : 0≤Cw) (hσ : 0<σ)
    (hw : ∀ᶠ k in atTop,∀ i : Fin (1),
      ‖splitRemainder (ss1FSequence f G split seed (k+i.val))
        (windowStep (ss1FSequence f G split seed) k i)
        (ss1FSequence f G split seed (k+1))
        (split (fun j=>ss1FSequence f G split seed (k+j.val)) i)‖≤
      Cw*‖ss1FSequence f G split seed (k+1)-ss1FSequence f G split seed (k+i.val+1)‖)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k)))) :
    let B := ‖canonicalVariation (T 0)‖
    let x := ss1FSequence f G split seed
    ∃ θ : ℕ → ℝ,Tendsto θ atTop (𝓝 0) ∧∀ᶠ k in atTop,
      ‖x (k+2)‖≤(1+θ k)*(B/2*‖x (k+1)‖+(L₃:ℝ)/12*‖x k‖^2)*‖x (k+1)‖ := by
  dsimp only
  let B := ‖canonicalVariation (T 0)‖
  let x := ss1FSequence f G split seed
  let a := fun k=>windowAnchor (n:=1) x k
  let s := fun k=>windowStep (n:=1) x k
  let l := fun k=>split (fun i=>x (k+i.val))
  let V := fun k=>windowMatrix (unitWindow (s k))
  let J := fun k=>inverseCongruence (V k) (ss1FNormalizedModel f G (a k) (s k) (l k))
  let A := fun k=>secantMatrix (averagedDerivative H 0 (x (k+1)))
  let q := fun k=>B*‖x (k+1)‖+(L₃:ℝ)*‖x k‖^2
  let leading := fun k=>B/2*‖x (k+1)‖+(L₃:ℝ)/12*‖x k‖^2
  let r := fun k=>(L₃:ℝ)/6*‖x k‖*‖x (k+1)‖+(25/12:ℝ)*(L₃:ℝ)*‖x (k+1)‖^2
  have hB : 0≤B := norm_nonneg (canonicalVariation (T 0))
  have hH := hessian_lipschitz_of_scalar_third H T S hS h₀ hT L₃ hLip hR hbounded
  have hsuper := ss1FSequence_superlinear f G H T S hS h₀ hnbhd hH hH₀ hf hG hG₀ hT hLip
    hB (canonicalVariation_unit_diagonal_bound (T 0)) split seed hconv hCw hσ hw hind
  have hages := superlinear_weighted_age_remainders x hsuper hB L₃.coe_nonneg
  have hr : r =o[atTop] q := by
    have hh := (hages.2.1.const_mul_left (1/6:ℝ)).add (hages.2.2.const_mul_left (25/12:ℝ))
    apply hh.congr_left
    intro k
    dsimp only [r]
    ring
  have hqnonneg (k : ℕ) : 0≤q k := by dsimp only [q]; positivity
  have hlnonneg (k : ℕ) : 0≤leading k := by dsimp only [leading]; positivity
  have hlead : leading =O[atTop] q := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun k=>?_)
    rw [one_mul,Real.norm_of_nonneg (hlnonneg k),Real.norm_of_nonneg (hqnonneg k)]
    dsimp only [leading,q]
    nlinarith only [mul_nonneg hB (norm_nonneg (x (k+1))),mul_nonneg L₃.coe_nonneg (sq_nonneg ‖x k‖)]
  have hqlead : q =O[atTop] leading := by
    refine IsBigO.of_bound 12 (Filter.Eventually.of_forall fun k=>?_)
    rw [Real.norm_of_nonneg (hlnonneg k),Real.norm_of_nonneg (hqnonneg k)]
    dsimp only [leading,q]
    nlinarith only [mul_nonneg hB (norm_nonneg (x (k+1)))]
  have hn : Tendsto (fun k=>‖x k‖) atTop (𝓝 0) := by simpa only [norm_zero] using hconv.norm
  have hn₁ : Tendsto (fun k=>‖x (k+1)‖) atTop (𝓝 0) := hn.comp (tendsto_add_atTop_nat 1)
  have hq : Tendsto q atTop (𝓝 0) := by
    simpa only [q,mul_zero,add_zero,zero_pow (by decide : 2≠0)] using
      (hn₁.const_mul B).add ((hn.pow 2).const_mul (L₃:ℝ))
  have hmem : ∀ᶠ k in atTop,x k∈S := hconv.eventually hnbhd
  have hmem₁ : ∀ᶠ k in atTop,x (k+1)∈S :=
    (hconv.comp (tendsto_add_atTop_nat 1)).eventually hnbhd
  have hs : ∀ᶠ k in atTop,s k 0≠0 := by
    filter_upwards [hind] with k hk
    intro hz
    have hh := windowMatrix_step_ne_zero (unitWindow (s k)) hk.1 0
    apply hh
    simp only [unitWindow,krylov.Methods.rescaleWindow,hz,smul_zero]
  have herror : ∀ᶠ k in atTop,‖J k-A k‖≤leading k+r k := by
    filter_upwards [hs,hmem,hmem₁,hw] with k hsk hmk hmk₁ hwk
    have hend : a k 0+s k 0=x (k+1) := by
      simp only [a,s,windowAnchor,windowStep,Fin.val_zero,Nat.add_zero,add_sub_cancel]
    have hsplit := hwk (0:Fin 1)
    change ‖splitRemainder (a k 0) (s k 0) (x (k+1)) (l k 0)‖≤Cw*‖x (k+1)-x (k+1)‖ at hsplit
    have hhalf := endpoint_split_eq_half (a k 0) (s k 0) hsk (l k 0) Cw
      (by simpa only [hend] using hsplit)
    have he := scalar_ss1F_model_radial_bound f G H T S hS h₀ hf hG hT L₃ hLip hB
      (canonicalVariation_unit_diagonal_bound (T 0)) (a k) (s k) (l k) hsk hmk
      (by simpa only [hend] using hmk₁) hhalf
    rw [hend] at he
    apply he.trans
    have hstep : ‖s k 0‖≤‖x k‖+‖x (k+1)‖ := by
      simpa only [s,windowStep,Fin.val_zero,Nat.add_zero,add_comm] using norm_sub_le (x (k+1)) (x k)
    have hsq : ‖s k 0‖^2≤(‖x k‖+‖x (k+1)‖)^2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hstep
    have hscaled := mul_le_mul_of_nonneg_left hsq (show 0≤(L₃:ℝ)/12 by positivity)
    dsimp only [leading,r]
    nlinarith only [hscaled]
  have hA : Tendsto A atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (g:=fun k=>B/2*‖x (k+1)‖+(L₃:ℝ)*‖x (k+1)‖^2)
    · exact Filter.Eventually.of_forall fun k=>norm_nonneg (A k-1)
    · filter_upwards [hmem₁] with k hk
      rw [show ‖A k-1‖=‖averagedDerivative H 0 (x (k+1))-ContinuousLinearMap.id ℝ _‖ from secantMatrix_sub_one _]
      have he := averaged_hessian_cubic_endpoint_bound H T S hS h₀ hT L₃ hLip hB
        (canonicalVariation_unit_diagonal_bound (T 0)) 0 (x (k+1)) h₀ hk
        (norm_nonneg (x (k+1))) (by simp only [norm_zero]; exact norm_nonneg _) le_rfl
      simpa only [hH₀,sub_zero,norm_zero,zero_add] using he
    · simpa only [mul_zero,add_zero,zero_pow (by decide : 2≠0)] using
        (hn₁.const_mul (B/2)).add ((hn₁.pow 2).const_mul (L₃:ℝ))
  have hJA : Tendsto (fun k=>J k-A k) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun k=>leading k+r k) herror
    simpa only [add_zero] using (hlead.trans_tendsto hq).add (hr.trans_tendsto hq)
  have hJ : Tendsto J atTop (𝓝 1) := by
    have hh := hJA.add hA
    simpa only [sub_add_cancel,zero_add] using hh
  obtain ⟨R₁,hR₁,hout⟩ := direct_model_sharp_query J A (fun k=>x (k+1)) q leading r hJ hlead hr herror
  obtain ⟨θ,hθ,hfactor⟩ := littleo_relative_factor leading R₁ (hR₁.trans_isBigO hqlead)
  refine ⟨θ,hθ,?_⟩
  filter_upwards [hout,hfactor,hind,hs,hmem₁] with k hk hfk hvk hsk hmk
  have hrad : cgOperator (A k) (x (k+1))=G (x (k+1)) := by
    rw [secantMatrix_operator]
    have hp t (ht : t∈Icc (0:ℝ) 1) : (0:EuclideanSpace ℝ (Fin 1))+t • x (k+1)∈S :=
      hS.add_smul_mem h₀ (by simpa only [zero_add] using hmk) ht
    have hcont := hH.continuousOn.comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
    simpa only [zero_add,hG₀,sub_zero] using
      averagedDerivative_apply G H 0 (x (k+1)) hcont (fun t ht=>hG _ (hp t ht))
  have hpoint : WithLp.toLp 2 (WithLp.ofLp (x (k+1))-(J k)⁻¹*ᵥ(A k*ᵥWithLp.ofLp (x (k+1))))=x (k+2) := by
    rw [show x (k+2)=ss1FPoint f G (a k) (s k) (l k) (x (k+1)) from ss1FSequence_step f G split seed k]
    rw [ss1FPoint_normalized_model f G (a k) (s k) (l k) (x (k+1))
      (by intro i; fin_cases i; exact hsk) hvk.1,←hrad]
    rfl
  rw [hpoint,hfk] at hk
  exact hk

/-- The sharp scalar cancellation estimate implies the exact general
printed coefficients, because a true normalized one-pair frame has gain
one and the original σ is at most one. -/
theorem ss1FSequence_scalar_printed_asymptotic
    (f : EuclideanSpace ℝ (Fin (1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (1)) → EuclideanSpace ℝ (Fin (1)))
    (H : EuclideanSpace ℝ (Fin (1)) → EuclideanSpace ℝ (Fin (1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (1)))
    (T : EuclideanSpace ℝ (Fin (1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (1))))
    (S : Set (EuclideanSpace ℝ (Fin (1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (1)))∈S) (hnbhd : S∈𝓝 0)
    {R : ℝ} (hR : 0≤R) (hbounded : ∀ z∈S,‖z‖≤R) {L₃ : ℝ≥0} (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    (split : (Fin (2) → EuclideanSpace ℝ (Fin (1))) → Fin (1) → ℝ)
    (seed : Fin (2) → EuclideanSpace ℝ (Fin (1)))
    (hconv : Tendsto (ss1FSequence f G split seed) atTop (𝓝 0))
    {Cw σ : ℝ} (hCw : 0≤Cw) (hσ : 0<σ)
    (hw : ∀ᶠ k in atTop,∀ i : Fin (1),
      ‖splitRemainder (ss1FSequence f G split seed (k+i.val))
        (windowStep (ss1FSequence f G split seed) k i)
        (ss1FSequence f G split seed (k+1))
        (split (fun j=>ss1FSequence f G split seed (k+j.val)) i)‖≤
      Cw*‖ss1FSequence f G split seed (k+1)-ss1FSequence f G split seed (k+i.val+1)‖)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k)))) :
    let B := ‖canonicalVariation (T 0)‖
    let x := ss1FSequence f G split seed
    ∃ θ : ℕ → ℝ,Tendsto θ atTop (𝓝 0) ∧∀ᶠ k in atTop,
      ‖x (k+2)‖≤(1+θ k)*
        (((Cw+1/2)*B/σ^2)*‖x (k+1)‖+((L₃:ℝ)/(12*σ^2))*‖x k‖^2)*‖x (k+1)‖ := by
  dsimp only
  let B := ‖canonicalVariation (T 0)‖
  let x := ss1FSequence f G split seed
  obtain ⟨θ,hθ,hbound⟩ := ss1FSequence_scalar_sharp_asymptotic f G H T S hS h₀ hnbhd hR hbounded
    hH₀ hf hG hG₀ hT hLip split seed hconv hCw hσ hw hind
  have hσ₁ : σ≤1 := by
    obtain ⟨k,hk⟩ := hind.exists
    let s := windowStep (n:=1) x k
    have hs : s 0≠0 := by
      intro hz
      have hh := windowMatrix_step_ne_zero (unitWindow s) hk.1 0
      apply hh
      simp only [unitWindow,krylov.Methods.rescaleWindow,hz,smul_zero]
    have hi := scalar_unit_window_inverse_norm s hs
    have hg : leastGain (windowMatrix (unitWindow s))=1 := by rw [leastGain,hi,inv_one]
    exact hk.2.trans_eq hg
  have hsq : σ^2≤1 := by nlinarith only [hσ.le,hσ₁]
  have hinv : 1≤(σ⁻¹)^2 := by
    simpa only [inv_pow] using (one_le_inv₀ (sq_pos_of_pos hσ)).mpr hsq
  have hθpos : ∀ᶠ k in atTop,0≤1+θ k := by
    filter_upwards [hθ.eventually (lt_mem_nhds (by norm_num : (-1:ℝ)<0))] with k hk
    linarith only [hk]
  refine ⟨θ,hθ,?_⟩
  filter_upwards [hbound,hθpos] with k hk hθk
  apply hk.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hθk
  have hB : 0≤B := norm_nonneg (canonicalVariation (T 0))
  have hlarger : B/2*‖x (k+1)‖+(L₃:ℝ)/12*‖x k‖^2≤
      (Cw+1/2)*B*‖x (k+1)‖+(L₃:ℝ)/12*‖x k‖^2 := by
    nlinarith only [mul_nonneg (mul_nonneg hCw hB) (norm_nonneg (x (k+1)))]
  have hn : 0≤(Cw+1/2)*B*‖x (k+1)‖+(L₃:ℝ)/12*‖x k‖^2 := by positivity
  apply hlarger.trans
  have hh := le_mul_of_one_le_left hn hinv
  apply hh.trans_eq
  simp only [div_eq_mul_inv,inv_pow,_root_.mul_inv_rev]
  ring

end
end krylov.Convergence
