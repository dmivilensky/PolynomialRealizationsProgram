import krylov.Convergence.SS1FSharpAsymptotic
import krylov.Convergence.WindowSharpQuery

/-!
Article: main_krylov, thm:ss1F, printed sharp error estimate (dimension ≥2).
Use: preserve the exact T3 and L3/12 matrix coefficients through the genuine
normalized inverse model. The actual inverse norm tends to one, and the
radial source remainder is little-o on the same weighted scale, including
T3=0. Source: true scalar third derivatives, the original (S), actual
normalized independence and the source-derived sharp matrix bound.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.LinearAlgebra
  krylov.Secant krylov.Reference chebyshev1.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- The genuine recursive SS1-F errors satisfy exactly the printed
(Cw+1/2)T3/σ² and L3/(12σ²) leading coefficients, with a literal factor
1+θ_k, θ_k→0. This includes zero source weights and zero trajectory errors. -/
theorem ss1FSequence_sharp_error_asymptotic
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (T : EuclideanSpace ℝ (Fin (n+2)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+2))))
    (S : Set (EuclideanSpace ℝ (Fin (n+2)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈S) (hnbhd : S∈𝓝 0)
    {R : ℝ} (hR : 0≤R) (hbounded : ∀ z∈S,‖z‖≤R) {L₃ : ℝ≥0} (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    (split : (Fin (n+3) → EuclideanSpace ℝ (Fin (n+2))) → Fin (n+2) → ℝ)
    (seed : Fin (n+3) → EuclideanSpace ℝ (Fin (n+2)))
    (hconv : Tendsto (ss1FSequence f G split seed) atTop (𝓝 0))
    {Cw σ : ℝ} (hCw : 0≤Cw) (hσ : 0<σ)
    (hw : ∀ᶠ k in atTop,∀ i : Fin (n+2),
      ‖splitRemainder (ss1FSequence f G split seed (k+i.val))
        (windowStep (ss1FSequence f G split seed) k i)
        (ss1FSequence f G split seed (k+n+2))
        (split (fun j=>ss1FSequence f G split seed (k+j.val)) i)‖≤
      Cw*‖ss1FSequence f G split seed (k+n+2)-ss1FSequence f G split seed (k+i.val+1)‖)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k)))) :
    let B := ‖canonicalVariation (T 0)‖
    let x := ss1FSequence f G split seed
    ∃ θ : ℕ → ℝ,Tendsto θ atTop (𝓝 0) ∧∀ᶠ k in atTop,
      ‖x (k+n+3)‖≤(1+θ k)*
        (((Cw+1/2)*B/σ^2)*‖x (k+1)‖+((L₃:ℝ)/(12*σ^2))*‖x k‖^2)*‖x (k+n+2)‖ := by
  dsimp only
  let B := ‖canonicalVariation (T 0)‖
  let x := ss1FSequence f G split seed
  let C := σ⁻¹
  let a := fun k=>windowAnchor (n:=n+2) x k
  let s := fun k=>windowStep (n:=n+2) x k
  let l := fun k=>split (fun i=>x (k+i.val))
  let V := fun k=>windowMatrix (unitWindow (s k))
  let X := fun k=>ss1FNormalizedError f G (a k) (s k) (l k)
  let A := fun k=>secantMatrix (averagedDerivative H 0 (x (k+n+2)))
  let q := fun k=>B*‖x (k+1)‖+(L₃:ℝ)*‖x k‖^2
  let leading := fun k=>(Cw+1/2)*B*‖x (k+1)‖+(L₃:ℝ)/12*‖x k‖^2
  have hB : 0≤B := norm_nonneg (canonicalVariation (T 0))
  have hC : 0≤C := inv_nonneg.mpr hσ.le
  have hH := hessian_lipschitz_of_scalar_third H T S hS h₀ hT L₃ hLip hR hbounded
  have hsuper := ss1FSequence_superlinear f G H T S hS h₀ hnbhd hH hH₀ hf hG hG₀ hT hLip
    hB (canonicalVariation_unit_diagonal_bound (T 0)) split seed hconv hCw hσ hw hind
  obtain ⟨r,hr,hmatrix⟩ := ss1FSequence_sharp_matrix_asymptotic f G H T S hS h₀ hnbhd hR hbounded
    hH₀ hf hG hG₀ hT hLip split seed hconv hCw hσ hw hind
  have hqnonneg (k : ℕ) : 0≤q k := by dsimp only [q]; positivity
  have hlnonneg (k : ℕ) : 0≤leading k := by dsimp only [leading]; positivity
  have hlead : leading =O[atTop] q := by
    refine IsBigO.of_bound (Cw+1) (Filter.Eventually.of_forall fun k=>?_)
    rw [Real.norm_of_nonneg (hlnonneg k),Real.norm_of_nonneg (hqnonneg k)]
    dsimp only [leading,q]
    nlinarith only [mul_nonneg hB (norm_nonneg (x (k+1))),mul_nonneg L₃.coe_nonneg (sq_nonneg ‖x k‖),
      mul_nonneg (mul_nonneg hCw L₃.coe_nonneg) (sq_nonneg ‖x k‖)]
  have hqlead : q =O[atTop] leading := by
    refine IsBigO.of_bound 12 (Filter.Eventually.of_forall fun k=>?_)
    rw [Real.norm_of_nonneg (hlnonneg k),Real.norm_of_nonneg (hqnonneg k)]
    dsimp only [leading,q]
    nlinarith only [mul_nonneg hB (norm_nonneg (x (k+1))),
      mul_nonneg (mul_nonneg hCw hB) (norm_nonneg (x (k+1)))]
  have hn : Tendsto (fun k=>‖x k‖) atTop (𝓝 0) := by simpa only [norm_zero] using hconv.norm
  have hq : Tendsto q atTop (𝓝 0) := by
    have hh := ((hn.comp (tendsto_add_atTop_nat 1)).const_mul B).add ((hn.pow 2).const_mul (L₃:ℝ))
    simpa only [q,Function.comp_def,mul_zero,add_zero,zero_pow (by decide : 2≠0)] using hh
  have hX : Tendsto X atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun k=>leading k+r k) hmatrix
    simpa only [add_zero] using (hlead.trans_tendsto hq).add (hr.trans_tendsto hq)
  have hmono : ∀ᶠ k in atTop,‖x (k+1)‖≤‖x k‖ := by
    simpa only [one_mul,norm_norm] using hsuper.def (by norm_num : (0:ℝ)<1)
  have hmem : ∀ᶠ k in atTop,x k∈S := hconv.eventually hnbhd
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hmono.and hmem)
  have htail (k : ℕ) (hk : N≤k) (j : ℕ) : ‖x (k+j)‖≤‖x k‖ := by
    induction j with
    | zero => simp only [Nat.add_zero]; exact le_rfl
    | succ j ih => exact ((hN (k+j) (by omega)).1).trans ih
  have hages := superlinear_weighted_age_remainders x hsuper hB L₃.coe_nonneg
  let gamma := fun k=>B/2*‖x (k+2)‖+(L₃:ℝ)*‖x (k+1)‖^2
  have hgamma : gamma =o[atTop] q := by
    have hh := (hages.1.const_mul_left (1/2:ℝ)).add hages.2.2
    apply hh.congr_left
    intro k
    dsimp only [gamma]
    ring
  have hAbig : (fun k=>A k-1) =O[atTop] gamma := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    rw [one_mul,Real.norm_of_nonneg (show 0≤gamma k by dsimp only [gamma]; positivity)]
    rw [show ‖A k-1‖=‖averagedDerivative H 0 (x (k+n+2))-ContinuousLinearMap.id ℝ _‖ from secantMatrix_sub_one _]
    have he := averaged_hessian_cubic_endpoint_bound H T S hS h₀ hT L₃ hLip hB
      (canonicalVariation_unit_diagonal_bound (T 0)) 0 (x (k+n+2)) h₀
      ((hN (k+n+2) (by omega)).2) (norm_nonneg (x (k+n+2)))
      (by simp only [norm_zero]; exact norm_nonneg _) le_rfl
    rw [hH₀,sub_zero,norm_zero,zero_add] at he
    apply he.trans
    have hc₂ : ‖x (k+n+2)‖≤‖x (k+2)‖ := by
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using htail (k+2) (by omega) n
    have hc₁ : ‖x (k+n+2)‖≤‖x (k+1)‖ := by
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using htail (k+1) (by omega) (n+1)
    have h₁ := mul_le_mul_of_nonneg_left hc₂ (show 0≤B/2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hc₁) L₃.coe_nonneg
    exact add_le_add h₁ h₂
  have hnew : (fun k=>A k-1) =o[atTop] q := hAbig.trans_isLittleO hgamma
  have hA : Tendsto A atTop (𝓝 1) := tendsto_iff_norm_sub_tendsto_zero.mpr
    (hnew.norm_left.trans_tendsto hq)
  have hV : ∀ᶠ k in atTop,‖(V k)⁻¹‖≤C :=
    hind.mono fun _ h=>Secant.inverse_bound_of_leastGain _ h.1 hσ h.2
  obtain ⟨R₁,hR₁,hout⟩ := conditioned_model_sharp_query V X A (fun k=>x (k+n+2)) q leading r hC
    hV hX hA hlead hr hmatrix hnew
  have hqscale : q =O[atTop] (fun k=>C^2*leading k) :=
    hqlead.const_mul_right (pow_ne_zero 2 (inv_ne_zero hσ.ne'))
  obtain ⟨θ,hθ,hfactor⟩ := littleo_relative_factor (fun k=>C^2*leading k) R₁ (hR₁.trans_isBigO hqscale)
  refine ⟨θ,hθ,?_⟩
  have hs : ∀ᶠ k in atTop,∀ i,s k i≠0 := by
    filter_upwards [hind] with k hk i
    intro hz
    have hh := windowMatrix_step_ne_zero (unitWindow (s k)) hk.1 i
    apply hh
    simp only [unitWindow,krylov.Methods.rescaleWindow,hz,smul_zero]
  filter_upwards [hout,hfactor,hind,hs,eventually_ge_atTop N] with k hk hfk hvk hsk hNk
  have hmodel := ss1F_normalized_model_error f G (a k) (s k) (l k) hvk.1
  have hj : inverseCongruence (V k) (ss1FNormalizedModel f G (a k) (s k) (l k))=
      1+inverseCongruence (V k) (X k) := by rw [←hmodel]; abel
  have hrad : cgOperator (A k) (x (k+n+2))=G (x (k+n+2)) := by
    rw [secantMatrix_operator]
    have hp t (ht : t∈Icc (0:ℝ) 1) : (0:EuclideanSpace ℝ (Fin (n+2)))+t • x (k+n+2)∈S :=
      hS.add_smul_mem h₀ (by simpa only [zero_add] using (hN (k+n+2) (by omega)).2) ht
    have hcont := hH.continuousOn.comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
    simpa only [zero_add,hG₀,sub_zero] using
      averagedDerivative_apply G H 0 (x (k+n+2)) hcont (fun t ht=>hG _ (hp t ht))
  have hpoint : WithLp.toLp 2 (WithLp.ofLp (x (k+n+2))-
      (1+inverseCongruence (V k) (X k))⁻¹*ᵥ(A k*ᵥWithLp.ofLp (x (k+n+2))))=x (k+n+3) := by
    rw [show x (k+n+3)=ss1FPoint f G (a k) (s k) (l k) (x (k+n+2)) from
      ss1FSequence_step f G split seed k]
    rw [ss1FPoint_normalized_model f G (a k) (s k) (l k) (x (k+n+2)) hsk hvk.1,hj,←hrad]
    rfl
  rw [hpoint,hfk] at hk
  have hcoef : C^2*leading k=
      ((Cw+1/2)*B/σ^2)*‖x (k+1)‖+((L₃:ℝ)/(12*σ^2))*‖x k‖^2 := by
    dsimp only [C,leading]
    simp only [div_eq_mul_inv,inv_pow,_root_.mul_inv_rev]
    ring
  rw [hcoef] at hk
  exact hk

end
end krylov.Convergence
