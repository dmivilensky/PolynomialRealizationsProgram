import krylov.Convergence.TableRestartedRFC

/-!
Article: main_krylov, Table s7-orders, true restarted RFC gradient clock.
Use: count actual line-search and correction queries, retaining the initial
empty-window correction skip. All queries are genuine scalar-executor
points and inherit their bounds from the true compact prefix bootstrap.
Source: ordinary RFC's real query schedule and the proved cubic cycle order.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Nonlinear krylov.Functions
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- A fresh actual RFC cycle has no correction query at its first
line endpoint. This is the real empty-window branch, independent of
regularity or line-search assumptions. Article: Table s7-orders. -/
theorem rfcFunction_first_correction_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) :
    rfcFunctionCorrectionStep T f G memory r x₀ (rfcFunctionRun T f G memory r x₀ 0)=0 := by
  have he : selectedWindow memory (rfcFunctionRun T f G memory r x₀ 0)=[] := by
    simp only [selectedWindow,rfcFunctionRun,History.pairs,recordPairs,List.take_nil]
  have hg : ¬rfcFunctionGate memory (rfcFunctionRun T f G memory r x₀ 0) := by
    simp only [rfcFunctionGate,he,ne_eq,not_true_eq_false,false_and,not_false_eq_true]
  simp only [rfcFunctionCorrectionStep,ite_eq_right hg]

/-- The first actual line endpoint and corrected point coincide, so its
cached gradient is reused in the original 2n-1 accounting.
Article: main_krylov, Table s7-orders. -/
theorem rfcFunction_first_line_point {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) :
    rfcFunctionPoint T f G memory r x₀ 1=
      rfcFunctionLinePoint T f memory r x₀ (rfcFunctionRun T f G memory r x₀ 0) := by
  rw [show 1=0+1 from rfl,rfcFunctionPoint_succ_line,rfcFunction_first_correction_zero,add_zero]

/-- Actual chronological queried points in a native RFC cycle: the first
line endpoint is already its first corrected point, after which line and
corrected endpoints alternate. The terminal corrected point starts the
next cycle. Article: Table s7-orders, 2n-1 gradients. -/
def rfcGradientCycleQuery {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (_N j : ℕ) : E :=
  if j=0 then x₀ else if j%2=1 then rfcFunctionPoint T f G fullMemory r x₀ ((j+1)/2)
  else rfcFunctionLinePoint T f fullMemory r x₀ (rfcFunctionRun T f G fullMemory r x₀ (j/2))

/-- Every real gradient-query endpoint has the true source prefix bound.
Article: main_krylov, Table s7-orders. -/
theorem rfcGradientCycleQuery_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (N : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C N) (j : ℕ) (hj : j<2*N-1) :
    ‖rfcGradientCycleQuery T f G r (ε • u) N j‖≤M*ε := by
  unfold rfcGradientCycleQuery
  split_ifs with hz hodd
  · have h0 := (hp.1 0 (by omega)).1
    simpa only [rfcFunctionPoint,rfcFunctionRun,History.displacement,List.map_nil,List.sum_nil,add_zero] using h0
  · exact (hp.1 ((j+1)/2) (by omega)).1
  · exact (hp.2 (j/2) (by omega)).2.2.1

/-- Stationary native RFC executes only the actual stationary query,
including the real line-search branch. Article: Table s7-orders. -/
theorem rfcGradientCycleQuery_stationary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (hG : G 0=0) (N j : ℕ) :
    rfcGradientCycleQuery T f G r 0 N j=0 := by
  unfold rfcGradientCycleQuery
  split_ifs
  · rfl
  · rw [rfcFunctionPoint,(rfcFunctionRun_stationary T f G fullMemory r 0 hG _).2,zero_add]
  · have hs := rfcFunctionRun_stationary T f G fullMemory r 0 hG (j/2)
    rw [rfcFunctionLinePoint,hs.2,zero_add,rfcFunctionDirection,hs.1,windowDirection_zero,
      metricLocalExactPoint,map_zero,localExactPoint_zero_direction,map_zero]

/-- Genuine scalar RFC queries, in the original gradient clock.
Article: main_krylov, Table s7-orders. -/
def rfcRestartedGradientQuery {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (N : ℕ) (x₀ : E) (j : ℕ) : E :=
  rfcGradientCycleQuery T f G r (rfcRestartedPoints T f G r N x₀ (j/(2*N-1))) N (j%(2*N-1))

/-- Original observed-reference compactness and actual cycle convergence
give the printed R-order per actual gradient query, including stationary
tails. Article: main_krylov, thm:D and Table s7-orders. -/
theorem restarted_nativeRFC_gradient_rorder
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
    HasROrder (fun j=>‖T (rfcRestartedGradientQuery T f G r (k+1) x₀ j)‖) ((3:ℝ)^(1/((2*(k+1)-1:ℕ):ℝ))) := by
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
  have hclock := hcycle.clock (by norm_num : (1:ℝ)<3) (2*(k+1)-1) (by omega)
  apply hclock.eventually_mono (show 0<‖T.toContinuousLinearMap‖*M*(J+1)+1 by positivity)
  obtain ⟨N,hsmall⟩ := eventually_atTop.mp
    (hconv.eventually (gt_mem_nhds (div_pos hep (by positivity : 0<J+1))))
  obtain ⟨Nn,hadmit⟩ := eventually_atTop.mp hN
  filter_upwards [eventually_ge_atTop ((max N Nn)*(2*(k+1)-1))] with j hj
  have hidx : max N Nn≤j/(2*(k+1)-1) := (Nat.le_div_iff_mul_le (by omega)).mpr hj
  let c := j/(2*(k+1)-1)
  change ‖T (rfcGradientCycleQuery T f G r (x c) (k+1) (j%(2*(k+1)-1)))‖≤
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
    have hb := rfcGradientCycleQuery_bound T f G H (cgOperator base) r u ε M D C (k+1) hp
      (j%(2*(k+1)-1)) (Nat.mod_lt _ (by omega))
    rw [hdecomp] at hb
    have ht := T.toContinuousLinearMap.le_opNorm
      (rfcGradientCycleQuery T f G r (x c) (k+1) (j%(2*(k+1)-1)))
    have hmul := mul_le_mul_of_nonneg_left hscale
      (mul_nonneg (norm_nonneg (T.toContinuousLinearMap)) hM.le)
    exact ht.trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
      (by nlinarith only [hmul,he]))
  · have hzero : e c=0 := le_antisymm (by linarith only [hpos]) he
    have hx : x c=0 := by
      apply T.injective
      simpa only [map_zero] using norm_eq_zero.mp hzero
    rw [hx,rfcGradientCycleQuery_stationary T f G r hG₀]
    simp only [map_zero,norm_zero,hzero,mul_zero,le_refl]

end
end krylov.Convergence
