import krylov.Convergence.OneGradientSourceJet
import krylov.Functions.NormalizedGradientQuadratic

/-!
Article: main_krylov, thm:V and prop:EL, Lipschitz-third remainder.
Use: prove a genuine quadratic remainder for every full native source
component from the true Lipschitz third derivative. Actual midpoint
shadows suffice; no smoothness of the adaptive trajectory is assumed.
Source: Bochner midpoint remainder and the actual radial gradient jet.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Functions
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Genuine third-derivative Lipschitz regularity gives a quadratic full
source-jet remainder on the actual enclosed, quadratically shadowed run.
Article: main_krylov, thm:V, Lipschitz D3 clause. -/
theorem oneGradientFunction_source_quadratic_jet
    (m : OneGradientMethod E) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (D : E → E →L[ℝ] E →L[ℝ] E) (N : ℕ)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hG : ∀ x∈closedBall 0 r,HasFDerivAt G (H x) x)
    (hD : ∀ x∈closedBall 0 r,HasFDerivAt H (D x) x)
    {L : ℝ≥0} (hL : LipschitzOnWith L D (closedBall 0 r))
    (M C R : ℝ) (hM : 0<M) (hC : 0≤C) (hR : 0<R) :
    ∃ ep J : ℝ,0<ep ∧0<J ∧∀ ε : ℝ,0<ε →ε<ep →∀ u : E,‖u‖≤R →
      (∀ i≤N,‖oneGradientFunctionPoint m G (ε • u) i‖≤M*ε) →
      ‖oneGradientFunctionOutput m G (ε • u) N‖≤M*ε →
      (∀ i≤N,‖oneGradientFunctionPoint m G (ε • u) i-
        ε • oneGradientReferencePoint m Q u i‖≤C*ε^2) →
      ‖oneGradientFunctionOutput m G (ε • u) N-
        ε • oneGradientReferenceOutput m Q u N‖≤C*ε^2 →
      ‖oneGradientFunctionInput m G H Q ε u N-ε • oneGradientReferenceJet m Q (D 0) u N‖≤J*ε^2 := by
  have hz : (0:E)∈closedBall 0 r := mem_closedBall_self hr.le
  obtain ⟨eg,Cg,heg,hCg,hgj⟩ := normalizedGradient_reference_quadratic_jet
    (ContinuousLinearEquiv.refl ℝ E) G H Q D hr hG₀ hH₀
    (fun z hz=>hG z (by simpa only [ContinuousLinearEquiv.refl_apply,mem_closedBall,dist_zero_right] using hz))
    (fun z hz=>hD z (by simpa only [ContinuousLinearEquiv.refl_apply,mem_closedBall,dist_zero_right] using hz)) hL R hR
  let J := Cg+(L:ℝ)*M^2+‖D 0‖*C+1
  have hJ : 0<J := by dsimp only [J]; positivity
  refine ⟨min eg (r/(M+1)),J,by positivity,hJ,?_⟩
  intro ε hε he u hu hp ho hps hos
  have hsmall : M*ε<r := by
    have hh := (lt_div_iff₀ (by positivity : 0<M+1)).mp (he.trans_le (min_le_right _ _))
    nlinarith only [hh,hε]
  have haverage (a b p q : E) (ha : ‖a‖≤M*ε) (hb : ‖b‖≤M*ε)
      (hap : ‖a-ε • p‖≤C*ε^2) (hbq : ‖b-ε • q‖≤C*ε^2) :
      ‖chebyshev1.Nonlinear.averagedDerivative H a (b-a)-Q-
        ε • D 0 ((1/2:ℝ) • (p+q))‖≤J*ε^2 := by
    have hs := oneGradient_midpoint_comparison a b p q ε M C ha hb hap hbq
    have hseg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
        a+t • (b-a)∈closedBall 0 r ∧‖a+t • (b-a)‖≤M*ε :=
      ⟨by simpa only [mem_closedBall,dist_zero_right] using (hs.1 t ht).trans hsmall.le,hs.1 t ht⟩
    have hm := averagedHessian_midpoint_quadratic H D (closedBall 0 r) (convex_closedBall _ _)
      hz hD hL a (b-a) (M*ε) (by positivity) hseg
    rw [hH₀] at hm
    have hd : ‖D 0 (a+(1/2:ℝ) • (b-a))-ε • D 0 ((1/2:ℝ) • (p+q))‖≤‖D 0‖*(C*ε^2) := by
      rw [←map_smul,←map_sub]
      exact ((D 0).le_opNorm _).trans (mul_le_mul_of_nonneg_left hs.2 (norm_nonneg _))
    have heq : chebyshev1.Nonlinear.averagedDerivative H a (b-a)-Q-ε • D 0 ((1/2:ℝ) • (p+q))=
        (chebyshev1.Nonlinear.averagedDerivative H a (b-a)-Q-D 0 (a+(1/2:ℝ) • (b-a)))+
        (D 0 (a+(1/2:ℝ) • (b-a))-ε • D 0 ((1/2:ℝ) • (p+q))) := by abel
    rw [heq]
    exact ((norm_add_le _ _).trans (add_le_add hm hd)).trans (by dsimp only [J];nlinarith only [sq_nonneg ε,hCg])
  have hgrad := hgj ε hε (he.trans_le (min_le_left _ _)) u hu
  have hgrad' : ‖ε⁻¹ • G (ε • u)-Q u-ε • ((1/2:ℝ) • D 0 u u)‖≤J*ε^2 :=
    hgrad.trans (mul_le_mul_of_nonneg_right (by
      dsimp only [J]
      nlinarith only [mul_nonneg L.coe_nonneg (sq_nonneg M),mul_nonneg (norm_nonneg (D 0)) hC]) (sq_nonneg ε))
  have hstep (i : Fin N) :
      ‖oneGradientFunctionOperator m G H (ε • u) i.val-Q-
        ε • D 0 ((1/2:ℝ) • (oneGradientReferencePoint m Q u i.val+
          oneGradientReferencePoint m Q u (i.val+1)))‖≤J*ε^2 := by
    rw [oneGradientFunctionOperator,oneGradientFunctionStep_eq_difference]
    exact haverage _ _ _ _ (hp i.val i.isLt.le) (hp (i.val+1) (by omega))
      (hps i.val i.isLt.le) (hps (i.val+1) (by omega))
  have hout :
      ‖oneGradientFunctionOutputOperator m G H (ε • u) N-Q-
        ε • D 0 ((1/2:ℝ) • (oneGradientReferencePoint m Q u N+oneGradientReferenceOutput m Q u N))‖≤J*ε^2 := by
    have heq : m.output (oneGradientFunctionRun m G (ε • u) N)=
        oneGradientFunctionOutput m G (ε • u) N-oneGradientFunctionPoint m G (ε • u) N := by
      rw [oneGradientFunctionOutput,add_sub_cancel_left]
    rw [oneGradientFunctionOutputOperator,heq]
    exact haverage _ _ _ _ (hp N le_rfl) ho (hps N le_rfl) hos
  rw [oneGradientFunctionInput,oneGradientReferenceJet,Prod.norm_def,Prod.norm_def,max_le_iff,max_le_iff]
  exact ⟨hgrad',⟨(pi_norm_le_iff_of_nonneg (mul_nonneg hJ.le (sq_nonneg ε))).mpr hstep,hout⟩⟩

end
end krylov.Convergence
