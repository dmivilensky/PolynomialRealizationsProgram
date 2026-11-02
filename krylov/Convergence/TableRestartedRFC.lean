import krylov.Convergence.RestartedRFCOrder
import krylov.Convergence.OrderCounting

/-!
Article: main_krylov, thm:D and Table s7-orders, actual restarted RFC clock.
Use: derive all true within-cycle point bounds from literal normalized
observations, then count actual iterations. No bound on an output or a
normalized operator input is assumed.
Source: native compact scalar RFC bootstrap and true stationary execution.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Nonlinear krylov.Functions
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- Every genuine RFC prefix is uniformly local under the original
observed-reference compactness. Article: thm:D, s7:N. -/
theorem nativeRFC_prefix_normalized
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) ×
      EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0) :
    ∃ ep M D C : ℝ, 0<ep ∧ 0<M ∧ 0<D ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ep →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖=1 →
      normalizedReference (rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0) (G (ε • u))∈K →
      NativeRFCPrefixBounds T f G H (cgOperator base) r u ε M D C (k+1) := by
  obtain ⟨es,hes,P,hP,hq,hcover⟩ := nativeRFC_normalized_reference_compact T hT f G H (cgOperator base)
    (cgOperator_positive base hb).2 hr hG₀ hH₀ hHc₀ hLr hH hF hG (k+1) K hK hquad
  obtain ⟨δ,hδ,F,hFc,hpre,hfreeze⟩ := compact_own_reference_frozen_tube (cgOperator base) (k+1) P hP hq
  obtain ⟨ed,D,hed,hD,hsource⟩ := nativeRFC_first_reference_drift T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF hG 1 (by norm_num)
  obtain ⟨ec,M,Db,C,hec,hM,hDb,hC,hcycle⟩ := nativeRFC_compact_prefix T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF hG (cgOperator_positive base hb).1 (cgOperator_positive base hb).2
    (k+1) F hFc hpre 1 (by norm_num)
  refine ⟨min es (min ed (min ec (δ/(D+1)))),M,Db,C,by positivity,hM,hDb,hC,?_⟩
  intro ε hε he u hu hn
  have hown := hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn
  have hs := hsource ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu.le
  have hsmall := (lt_div_iff₀ (by positivity : 0<D+1)).mp
    (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hfrozen : cgOperator base u∈F := hfreeze _ _ _ hown (hs.trans (by nlinarith only [hsmall,hε]))
  exact hcycle ε hε (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    u hu.le hfrozen

/-- Genuine ordinary RFC corrected iterates in their actual iteration
clock, including every within-cycle point. Article: Table s7-orders. -/
def rfcRestartedIterate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (N : ℕ) (x₀ : E) (j : ℕ) : E :=
  rfcFunctionPoint T f G fullMemory r (rfcRestartedPoints T f G r N x₀ (j/N)) (j%N)

/-- The original ordinary RFC iteration order follows from actual cycle
convergence and literal s7:N, including stationary tails.
Article: main_krylov, thm:D and Table s7-orders. -/
theorem restarted_nativeRFC_iteration_rorder
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) ×
      EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0)
    (x₀ : EuclideanSpace ℝ (Fin (k+1))) :
    let x := rfcRestartedPoints T f G r (k+1) x₀
    let e := fun c=>‖T (x c)‖
    (∀ᶠ c in atTop, 0<e c →
      normalizedReference (rfcFunctionSearchOperator T f G H fullMemory r (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    HasROrder (fun j=>‖T (rfcRestartedIterate T f G r (k+1) x₀ j)‖) ((3:ℝ)^(1/((k+1:ℕ):ℝ))) := by
  dsimp only
  intro hN hconv
  let x := rfcRestartedPoints T f G r (k+1) x₀
  let e := fun c=>‖T (x c)‖
  let J := ‖T.symm.toContinuousLinearMap‖
  have hJ : 0≤J := norm_nonneg _
  obtain ⟨ep,M,D,C,hep,hM,hD,hC,hprefix⟩ := nativeRFC_prefix_normalized base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hquad
  have hcycle := restarted_nativeRFC_normalized_rorder base hb hk T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hquad x₀ hN hconv
  have hclock := hcycle.clock (by norm_num : (1:ℝ)<3) (k+1) (by omega)
  apply hclock.eventually_mono (show 0<‖T.toContinuousLinearMap‖*M*(J+1)+1 by positivity)
  obtain ⟨N,hsmall⟩ := eventually_atTop.mp
    (hconv.eventually (gt_mem_nhds (div_pos hep (by positivity : 0<J+1))))
  obtain ⟨Nn,hadmit⟩ := eventually_atTop.mp hN
  filter_upwards [eventually_ge_atTop ((max N Nn)*(k+1))] with j hj
  have hidx : max N Nn≤j/(k+1) := (Nat.le_div_iff_mul_le (by omega)).mpr hj
  let c := j/(k+1)
  change ‖T (rfcFunctionPoint T f G fullMemory r (x c) (j%(k+1)))‖≤
    (‖T.toContinuousLinearMap‖*M*(J+1)+1)*e c
  have he : 0≤e c := norm_nonneg _
  by_cases hpos : 0<e c
  · have hxne : x c≠0 := by
      intro hz
      change 0<‖T (x c)‖ at hpos
      rw [hz,map_zero,norm_zero] at hpos
      exact (lt_irrefl 0) hpos
    let ε := ‖x c‖
    have hε : 0<ε := norm_pos_iff.mpr hxne
    have hxbound : ε≤J*e c := by
      have hh := T.symm.toContinuousLinearMap.le_opNorm (T (x c))
      simpa only [ContinuousLinearEquiv.coe_coe,T.symm_apply_apply] using hh
    have hscale : ε≤(J+1)*e c := hxbound.trans (by nlinarith only [he])
    have heps : ε<ep := by
      have hs := (lt_div_iff₀ (by positivity : 0<J+1)).mp
        (hsmall c ((le_max_left _ _).trans hidx))
      exact hscale.trans_lt (by simpa only [mul_comm] using hs)
    let u := ε⁻¹ • x c
    have hu : ‖u‖=1 := by
      rw [show u=ε⁻¹ • x c from rfl,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
      exact inv_mul_cancel₀ hε.ne'
    have hdecomp : ε • u=x c := by
      dsimp only [u]; rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
    have hp := hprefix ε hε heps u hu (by rw [hdecomp]; exact hadmit c ((le_max_right _ _).trans hidx) hpos)
    have hb := (hp.1 (j%(k+1)) (Nat.mod_lt _ (by omega)).le).1
    rw [hdecomp] at hb
    have ht := T.toContinuousLinearMap.le_opNorm
      (rfcFunctionPoint T f G fullMemory r (x c) (j%(k+1)))
    have hmul := mul_le_mul_of_nonneg_left hscale
      (mul_nonneg (norm_nonneg (T.toContinuousLinearMap)) hM.le)
    exact ht.trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
      (by nlinarith only [hmul,he]))
  · have hzero : e c=0 := le_antisymm (by linarith only [hpos]) he
    have hx : x c=0 := by
      apply T.injective
      simpa only [map_zero] using norm_eq_zero.mp hzero
    rw [hx,rfcFunctionPoint,(rfcFunctionRun_stationary T f G fullMemory r 0 hG₀ (j%(k+1))).2]
    simp only [zero_add,map_zero,norm_zero,hzero,mul_zero,le_refl]

end
end krylov.Convergence
