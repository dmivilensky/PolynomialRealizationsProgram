import krylov.Convergence.OneGradientFunctions
import krylov.Convergence.SecantSourceBounds

/-!
Article: main_krylov, thm:V, prop:EL and lem:cycle-transfer.
Use: construct the normalized true one-gradient source inputs and prove
their first-order size from actual query enclosures. The native localization
module derives these enclosures from the primitive original assumptions;
this helper then identifies the true averaged-operator transcript exactly.
Source: genuine segment FTC, sharp half-endpoint Hessian estimates, and
the actual radial gradient Taylor bound.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric krylov.Methods krylov.Nonlinear krylov.Functions chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Every real chosen one-gradient step is exactly the difference of its
two evaluated points. Article: thm:V and prop:EL. -/
theorem oneGradientFunctionStep_eq_difference (m : OneGradientMethod E) (G : E → E) (x₀ : E) (i : ℕ) :
    m.step (oneGradientFunctionRun m G x₀ i)=
      oneGradientFunctionPoint m G x₀ (i+1)-oneGradientFunctionPoint m G x₀ i := by
  rw [oneGradientFunctionPoint_succ,add_sub_cancel_left]

/-- Every actual finite input consists of the normalized initial gradient
drift, actual evaluated segment averages, and the true output-segment
average used only for semantics. Article: lem:cycle-transfer, thm:V. -/
def oneGradientFunctionInput (m : OneGradientMethod E) (G : E → E)
    (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E) (ε : ℝ) (u : E) (N : ℕ) :
    E × ((Fin N → E →L[ℝ] E) × (E →L[ℝ] E)) :=
  (ε⁻¹ • G (ε • u)-Q u,
    (fun i=>oneGradientFunctionOperator m G H (ε • u) i.val-Q,
      oneGradientFunctionOutputOperator m G H (ε • u) N-Q))

/-- Primitive derivative data and enclosed real vertices identify the
entire actual scalar query prefix with its true averaged-operator run.
Article: lem:cycle-transfer, thm:V and prop:EL. -/
theorem oneGradientFunctionRun_eq_of_local
    (m : OneGradientMethod E) (G : E → E) (H : E → E →L[ℝ] E)
    (x₀ : E) (N : ℕ) (r : ℝ) (hH : ContinuousOn H (ball 0 r))
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (hp : ∀ i≤N,oneGradientFunctionPoint m G x₀ i∈ball 0 r) :
    ∀ i≤N,oneGradientFunctionRun m G x₀ i=
      oneGradientRun m (oneGradientFunctionOperator m G H x₀) (G x₀) i := by
  have hseg i (hi : i<N) t (ht : t∈Icc (0:ℝ) 1) :
      oneGradientFunctionPoint m G x₀ i+t • m.step (oneGradientFunctionRun m G x₀ i)∈ball 0 r := by
    apply (convex_ball (0:E) r).add_smul_mem (hp i hi.le) _ ht
    rw [←oneGradientFunctionPoint_succ]
    exact hp (i+1) (by omega)
  intro i hi
  apply oneGradientFunctionRun_eq m G H x₀ i
  · intro j hj
    exact hH.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (hseg j (hj.trans_le hi))
  · intro j hj t ht
    exact hG _ (hseg j (hj.trans_le hi) t ht)

/-- The actual normalized input is first order, and its real scalar
queries and semantic output are exactly the corresponding independent
operator execution. No output-gradient estimate is assumed.
Article: main_krylov, thm:V and prop:EL. -/
theorem oneGradientFunction_source_bound
    (m : OneGradientMethod E) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (N : ℕ) {r : ℝ} (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=Q) {L : ℝ≥0}
    (hH : LipschitzOnWith L H (ball 0 r))
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (M R : ℝ) (hM : 0≤M) (ε : ℝ) (hε : 0<ε) (u : E) (hu : ‖u‖≤R)
    (hp : ∀ i≤N,oneGradientFunctionPoint m G (ε • u) i∈ball 0 r ∧
      ‖oneGradientFunctionPoint m G (ε • u) i‖≤ε*M)
    (ho : oneGradientFunctionOutput m G (ε • u) N∈ball 0 r ∧
      ‖oneGradientFunctionOutput m G (ε • u) N‖≤ε*M) :
    ‖oneGradientFunctionInput m G H Q ε u N‖≤((L:ℝ)/2*R^2+(L:ℝ)*M+1)*ε ∧
      oneGradientFunctionRun m G (ε • u) N=
        oneGradientRun m (oneGradientFunctionOperator m G H (ε • u)) (G (ε • u)) N ∧
      G (oneGradientFunctionOutput m G (ε • u) N)=
        m.outputGradient (oneGradientFunctionOutputOperator m G H (ε • u) N)
          (oneGradientRun m (oneGradientFunctionOperator m G H (ε • u)) (G (ε • u)) N) := by
  have hz : (0:E)∈ball 0 r := mem_ball_self hr
  have hseg i (hi : i<N) t (ht : t∈Icc (0:ℝ) 1) :
      oneGradientFunctionPoint m G (ε • u) i+
        t • m.step (oneGradientFunctionRun m G (ε • u) i)∈ball 0 r := by
    apply (convex_ball (0:E) r).add_smul_mem (hp i hi.le).1 _ ht
    rw [←oneGradientFunctionPoint_succ]
    exact (hp (i+1) (by omega)).1
  have hsegout t (ht : t∈Icc (0:ℝ) 1) : oneGradientFunctionPoint m G (ε • u) N+
      t • m.output (oneGradientFunctionRun m G (ε • u) N)∈ball 0 r :=
    (convex_ball (0:E) r).add_smul_mem (hp N le_rfl).1 ho.1 ht
  have hcont i (hi : i<N) : ContinuousOn (fun t : ℝ=>H (oneGradientFunctionPoint m G (ε • u) i+
      t • m.step (oneGradientFunctionRun m G (ε • u) i))) (Icc 0 1) :=
    hH.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn (hseg i hi)
  have hcontout : ContinuousOn (fun t : ℝ=>H (oneGradientFunctionPoint m G (ε • u) N+
      t • m.output (oneGradientFunctionRun m G (ε • u) N))) (Icc 0 1) :=
    hH.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hsegout
  have heq := oneGradientFunctionRun_eq m G H (ε • u) N hcont (fun i hi t ht=>hG _ (hseg i hi t ht))
  have hout := oneGradientFunctionOutput_gradient m G H (ε • u) N hcontout (fun t ht=>hG _ (hsegout t ht))
  have hoperator i (hi : i<N) : ‖oneGradientFunctionOperator m G H (ε • u) i-Q‖≤(L:ℝ)*M*ε := by
    rw [oneGradientFunctionOperator,oneGradientFunctionStep_eq_difference,←hH₀]
    have hh := secant_operator_endpoint_bound H (ball 0 r) (convex_ball _ _) hz hH
      _ _ (hp i hi.le).1 (hp (i+1) (by omega)).1
    have hs := add_le_add (hp i hi.le).2 (hp (i+1) (by omega)).2
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hs (show 0≤(L:ℝ)/2 by positivity)])
  have houtputop : ‖oneGradientFunctionOutputOperator m G H (ε • u) N-Q‖≤(L:ℝ)*M*ε := by
    have hs : m.output (oneGradientFunctionRun m G (ε • u) N)=
        oneGradientFunctionOutput m G (ε • u) N-oneGradientFunctionPoint m G (ε • u) N := by
      rw [oneGradientFunctionOutput,add_sub_cancel_left]
    rw [oneGradientFunctionOutputOperator,hs,←hH₀]
    have hh := secant_operator_endpoint_bound H (ball 0 r) (convex_ball _ _) hz hH _ _ (hp N le_rfl).1 ho.1
    have hs := add_le_add (hp N le_rfl).2 ho.2
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hs (show 0≤(L:ℝ)/2 by positivity)])
  have hstart : ε • u∈ball 0 r := by
    simpa only [oneGradientFunctionPoint,oneGradientFunctionRun,History.displacement,
      List.map_nil,List.sum_nil,add_zero] using (hp 0 (by omega)).1
  have hgrad := radial_gradient_endpoint_bound G H (ball 0 r) (convex_ball _ _) hz hH hG hG₀ (ε • u) hstart
  rw [hH₀] at hgrad
  have hg : ‖ε⁻¹ • G (ε • u)-Q u‖≤(L:ℝ)/2*R^2*ε := by
    have hs : ε⁻¹ • G (ε • u)-Q u=ε⁻¹ • (G (ε • u)-Q (ε • u)) := by
      rw [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
    rw [hs,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    have hn : ‖ε • u‖≤ε*R := by
      rw [norm_smul,Real.norm_of_nonneg hε.le]
      exact mul_le_mul_of_nonneg_left hu hε.le
    have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2)
      (show 0≤(L:ℝ)/2 by positivity)
    exact (mul_le_mul_of_nonneg_left (hgrad.trans hb) (inv_nonneg.mpr hε.le)).trans_eq (by field_simp)
  refine ⟨?_,heq,?_⟩
  · rw [oneGradientFunctionInput,Prod.norm_def,Prod.norm_def,max_le_iff,max_le_iff]
    refine ⟨hg.trans ?_,⟨?_,houtputop.trans ?_⟩⟩
    · nlinarith only [mul_nonneg (mul_nonneg L.coe_nonneg hM) hε.le,hε]
    · exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=>(hoperator i.val i.isLt).trans (by
        nlinarith only [mul_nonneg (mul_nonneg (show 0≤(L:ℝ)/2 by positivity) (sq_nonneg R)) hε.le,hε])
    · nlinarith only [mul_nonneg (mul_nonneg (show 0≤(L:ℝ)/2 by positivity) (sq_nonneg R)) hε.le,hε]
  · rw [←heq]
    exact hout.symm

end
end krylov.Convergence
