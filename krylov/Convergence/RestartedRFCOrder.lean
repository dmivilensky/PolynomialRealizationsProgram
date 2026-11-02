import krylov.Convergence.RestartedRFCCubic
import krylov.Functions.NativeRFCFStationary

/-!
Article: main_krylov, thm:D, literal normalized restarted ordinary RFC.
Use: derive genuine cubic cycle error from the actual observed-reference
compactness and scalar convergence. All frozen compactness, true source
domains, actual line/model inverses and query enclosures are derived.
Source: native cubic metric-error bound and exact stationary execution.
-/
namespace krylov.Convergence
noncomputable section
open Set Filter Topology Metric krylov.Methods krylov.Reference krylov.Nonlinear krylov.Functions
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- Actual ordinary RFC restart points with fresh full cycle memory.
Article: main_krylov, thm:D. -/
def rfcRestartedPoints {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (N : ℕ) (x₀ : E) : ℕ → E
  | 0=>x₀
  | c+1=>rfcFunctionPoint T f G fullMemory r (rfcRestartedPoints T f G r N x₀ c) N

/-- Literal s7:N implies the actual one-cycle RFC cubic metric-error
bound, with no separate frozen-reference admission premise.
Article: main_krylov, thm:D. -/
theorem nativeRFC_error_normalized
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
      (∀ v, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ep →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖=1 →
      normalizedReference (rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0) (G (ε • u))∈K →
      ‖T (rfcFunctionPoint T f G fullMemory r (ε • u) (k+1))‖≤C*ε^3 := by
  obtain ⟨es,hes,P,hP,hq,hcover⟩ := nativeRFC_normalized_reference_compact T hT f G H (cgOperator base)
    (cgOperator_positive base hb).2 hr hG₀ hH₀ hHc₀ hLr hH hF hG (k+1) K hK hquad
  obtain ⟨δ,hδ,F,hFc,hpre,hfreeze⟩ := compact_own_reference_frozen_tube (cgOperator base) (k+1) P hP hq
  obtain ⟨ed,D,hed,hD,hsource⟩ := nativeRFC_first_reference_drift T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF hG 1 (by norm_num)
  obtain ⟨ec,C,hec,hC,hcycle⟩ := nativeRFC_error_cubic base hb hk T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG F hFc (fun g hg i hi=>hpre g hg i (by omega)) 1 (by norm_num)
  refine ⟨min es (min ed (min ec (δ/(D+1)))),C,by positivity,hC,?_⟩
  intro ε hε he u hu hn
  have hown := hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn
  have hs := hsource ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu.le
  have hsmall := (lt_div_iff₀ (by positivity : 0<D+1)).mp
    (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hfrozen : cgOperator base u∈F := hfreeze _ _ _ hown (hs.trans (by nlinarith only [hsmall,hε]))
  exact hcycle ε hε (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    u hu.le hfrozen

set_option maxHeartbeats 800000 in
/-- Actual restarted RFC has cycle order at least three under precisely
the article's actual normalized observed-reference compactness and error
convergence. Frozen nonstagnation and all source localization are derived.
Stationary tails are included. Article: main_krylov, s7:N, thm:D. -/
theorem restarted_nativeRFC_normalized_cubic
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
    ∃ C : ℝ, 0<C ∧ ∀ᶠ c in atTop, e (c+1)≤C*(e c)^3 := by
  let x := rfcRestartedPoints T f G r (k+1) x₀
  let e := fun c=>‖T (x c)‖
  dsimp only
  intro hNrm hconv
  obtain ⟨ep,C,hep,hC,hcycle⟩ := nativeRFC_error_normalized base hb hk T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hquad
  let J := ‖T.symm.toContinuousLinearMap‖
  have hJ : 0≤J := norm_nonneg _
  have hbound c : ‖x c‖≤J*e c := by
    have hh := T.symm.toContinuousLinearMap.le_opNorm (T (x c))
    simpa only [ContinuousLinearEquiv.coe_coe,T.symm_apply_apply] using hh
  refine ⟨C*(J+1)^3,by positivity,?_⟩
  filter_upwards [hconv.eventually (gt_mem_nhds (div_pos hep (by positivity : 0<J+1))),hNrm] with c hc hn
  change e (c+1)≤C*(J+1)^3*(e c)^3
  by_cases he : 0<e c
  · have hxne : x c≠0 := by
      intro hz
      change 0<‖T (x c)‖ at he
      rw [hz,map_zero,norm_zero] at he
      exact (lt_irrefl 0) he
    let ε := ‖x c‖
    have hε : 0<ε := norm_pos_iff.mpr hxne
    let u := ε⁻¹ • x c
    have hunit : ‖u‖=1 := by
      rw [show u=ε⁻¹ • x c from rfl,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
      exact inv_mul_cancel₀ hε.ne'
    have hdecomp : ε • u=x c := by
      dsimp only [u]; rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
    have hsmall : ε<ep := by
      have hh := (lt_div_iff₀ (by positivity : 0<J+1)).mp hc
      exact (hbound c).trans_lt (by nlinarith only [hh,he])
    have hout := hcycle ε hε hsmall u hunit (by rw [hdecomp]; exact hn he)
    rw [hdecomp] at hout
    have hscale : ε≤(J+1)*e c := (hbound c).trans (by nlinarith only [norm_nonneg (T (x c))])
    have hh := hout.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hscale 3) hC.le)
    exact hh.trans_eq (by rw [mul_pow]; ring)
  · have he₀ : e c=0 := le_antisymm (by linarith only [he]) (norm_nonneg _)
    have hx : x c=0 := by
      apply T.injective
      simpa only [map_zero] using norm_eq_zero.mp he₀
    have hnext : e (c+1)=0 := by
      change ‖T (rfcFunctionPoint T f G fullMemory r (x c) (k+1))‖=0
      rw [hx,rfcFunctionPoint,(rfcFunctionRun_stationary T f G fullMemory r 0 hG₀ (k+1)).2]
      simp only [zero_add,map_zero,norm_zero]
    rw [hnext,he₀]
    positivity

/-- The actual ordinary RFC restarts have literal cubic R-order.
Article: main_krylov, thm:D and Table s7-orders. -/
theorem restarted_nativeRFC_normalized_rorder
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
    HasROrder e 3 := by
  dsimp only
  intro hN hconv
  have hrec := restarted_nativeRFC_normalized_cubic base hb hk T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hquad x₀ hN hconv
  exact rorder_power_recurrence _ (fun _=>norm_nonneg _) hconv 3 (by norm_num) hrec

end
end krylov.Convergence
