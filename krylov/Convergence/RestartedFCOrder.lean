import krylov.Convergence.RestartedFC

/-!
Article: main_krylov, thm:D, genuine normalized restarted FC R-order.
Use: derive the actual quadratic restart recursion and its literal R-order
from the source's normalized observed references and convergence only.
Source: native scalar FC localization, exact stationary execution and the
proved characteristic exponential barrier, including zero errors.
-/
namespace krylov.Convergence
noncomputable section
open Set Filter Topology Metric krylov.Methods krylov.Reference krylov.Nonlinear krylov.Functions
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- Actual restarted FC has cycle order at least two under precisely
the article's actual normalized observed-reference compactness and error
convergence. Frozen nonstagnation and all source localization are derived.
Stationary tails are included. Article: main_krylov, s7:N, thm:D. -/
theorem restarted_nativeFC_normalized_quadratic
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
      (∀ v, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0)
    (x₀ : EuclideanSpace ℝ (Fin (k+1))) :
    let x := fcRestartedPoints T f G r (k+1) x₀
    let e := fun c=>‖T (x c)‖
    (∀ᶠ c in atTop, 0<e c →
      normalizedReference (metricFCOperator T f G H fullMemory r (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    ∃ C : ℝ, 0<C ∧ ∀ᶠ c in atTop, e (c+1)≤C*(e c)^2 := by
  let x := fcRestartedPoints T f G r (k+1) x₀
  let e := fun c=>‖T (x c)‖
  dsimp only
  intro hNrm hconv
  obtain ⟨ep,C,hep,hC,hcycle⟩ := nativeFC_error_normalized base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hquad
  let J := ‖T.symm.toContinuousLinearMap‖
  have hJ : 0≤J := norm_nonneg _
  have hbound c : ‖x c‖≤J*e c := by
    have hh := T.symm.toContinuousLinearMap.le_opNorm (T (x c))
    simpa only [ContinuousLinearEquiv.coe_coe,T.symm_apply_apply] using hh
  refine ⟨C*(J+1)^2,by positivity,?_⟩
  filter_upwards [hconv.eventually (gt_mem_nhds (div_pos hep (by positivity : 0<J+1))),hNrm] with c hc hn
  change e (c+1)≤C*(J+1)^2*(e c)^2
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
    have hh := hout.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hscale 2) hC.le)
    exact hh.trans_eq (by rw [mul_pow]; ring)
  · have he₀ : e c=0 := le_antisymm (by linarith only [he]) (norm_nonneg _)
    have hx : x c=0 := by
      apply T.injective
      simpa only [map_zero] using norm_eq_zero.mp he₀
    have hnext : e (c+1)=0 := by
      change ‖T (metricFCPoint T f G fullMemory r (x c) (k+1))‖=0
      rw [hx]
      have hh := (metricFCPoint_localization T hT f G H hr hG₀ hHc₀ hLr hH hF hG
        fullMemory 0 (by simpa only [map_zero,norm_zero] using half_pos hr) (k+1)).1
      simp only [map_zero,norm_zero,mul_zero] at hh
      exact le_antisymm hh (norm_nonneg _)
    rw [hnext,he₀]
    positivity


/-- Actual normalized restarted FC has the literal quadratic R-order bound.
Article: main_krylov, thm:D and Table s7-orders. -/
theorem restarted_nativeFC_normalized_rorder
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
      (∀ v, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0)
    (x₀ : EuclideanSpace ℝ (Fin (k+1))) :
    let x := fcRestartedPoints T f G r (k+1) x₀
    let e := fun c=>‖T (x c)‖
    (∀ᶠ c in atTop, 0<e c →
      normalizedReference (metricFCOperator T f G H fullMemory r (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    HasROrder e 2 := by
  dsimp only
  intro hN hconv
  have hr := restarted_nativeFC_normalized_quadratic base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hquad x₀ hN hconv
  exact rorder_power_recurrence _ (fun _=>norm_nonneg _) hconv 2 (by norm_num) hr

end
end krylov.Convergence
