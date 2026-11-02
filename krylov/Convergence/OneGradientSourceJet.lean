import krylov.Convergence.OneGradientReferenceComparison
import krylov.Functions.NormalizedGradientJet

/-!
Article: main_krylov, lem:cycle-transfer, thm:V and prop:EL.
Use: derive the complete first source jet of the actual scalar one-gradient
execution. Every evaluated Hessian average and the unevaluated semantic
average uses the midpoint of its genuine quadratic-reference segment.
Source: true radial gradient calculus and uniform Bochner midpoint expansion.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- The full compatible first jet, including the genuine initial gradient
and all evaluated and semantic reference midpoints. Article: lem:cycle-transfer. -/
def oneGradientReferenceJet (m : OneGradientMethod E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) (N : ℕ) :
    E × ((Fin N → E →L[ℝ] E) × (E →L[ℝ] E)) :=
  ((1/2:ℝ) • D u u,
    (fun i=>D ((1/2:ℝ) • (oneGradientReferencePoint m Q u i.val+
      oneGradientReferencePoint m Q u (i.val+1))),
     D ((1/2:ℝ) • (oneGradientReferencePoint m Q u N+oneGradientReferenceOutput m Q u N))))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Endpoint bounds give the real segment bound and midpoint replacement
needed by the genuine averaged-Hessian jet. Article: lem:cycle-transfer. -/
theorem oneGradient_midpoint_comparison (a b p q : E) (ε M C : ℝ)
    (ha : ‖a‖≤M*ε) (hb : ‖b‖≤M*ε)
    (hap : ‖a-ε • p‖≤C*ε^2) (hbq : ‖b-ε • q‖≤C*ε^2) :
    (∀ t∈Icc (0:ℝ) 1,‖a+t • (b-a)‖≤M*ε) ∧
      ‖a+(1/2:ℝ) • (b-a)-ε • ((1/2:ℝ) • (p+q))‖≤C*ε^2 := by
  constructor
  · intro t ht
    have hh := (convex_closedBall (0:E) (M*ε)).add_smul_mem
      (show a∈closedBall 0 (M*ε) by simpa only [mem_closedBall,dist_zero_right] using ha)
      (show a+(b-a)∈closedBall 0 (M*ε) by
        simpa only [add_sub_cancel,mem_closedBall,dist_zero_right] using hb) ht
    simpa only [mem_closedBall,dist_zero_right] using hh
  · have he : a+(1/2:ℝ) • (b-a)-ε • ((1/2:ℝ) • (p+q))=
        (1/2:ℝ) • ((a-ε • p)+(b-ε • q)) := by module
    rw [he,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    exact (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hap hbq))
      (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)

omit [FiniteDimensional ℝ E] in
/-- All true finite source components have the compatible reference jet,
uniformly whenever the already-derived native localization and quadratic
shadows hold. No differentiability of the executed trajectory is needed.
Article: main_krylov, lem:cycle-transfer, thm:V and prop:EL. -/
theorem oneGradientFunction_source_jet
    (m : OneGradientMethod E) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E) (N : ℕ)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hH : ContinuousOn H (ball 0 r)) (hD : HasFDerivAt H D 0)
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (M C R : ℝ) (hM : 0<M) (hC : 0≤C) (hR : 0<R) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u : E,‖u‖≤R →
      (∀ i≤N,‖oneGradientFunctionPoint m G (ε • u) i‖≤M*ε) →
      ‖oneGradientFunctionOutput m G (ε • u) N‖≤M*ε →
      (∀ i≤N,‖oneGradientFunctionPoint m G (ε • u) i-
        ε • oneGradientReferencePoint m Q u i‖≤C*ε^2) →
      ‖oneGradientFunctionOutput m G (ε • u) N-
        ε • oneGradientReferenceOutput m Q u N‖≤C*ε^2 →
      ‖oneGradientFunctionInput m G H Q ε u N-ε • oneGradientReferenceJet m Q D u N‖≤η*ε := by
  intro η hη
  obtain ⟨eg,heg,hgj⟩ := normalizedGradient_reference_jet G H Q D hr hG₀ hH₀ hH hD hG R hR η hη
  obtain ⟨ea,hea,haj⟩ := averagedHessian_reference_jet H D hr hH hD M C hM hC η hη
  refine ⟨min eg ea,lt_min heg hea,?_⟩
  intro ε hε he u hu hp ho hps hos
  have hgrad := hgj ε hε (he.trans_le (min_le_left _ _)) u hu
  have hstep (i : Fin N) :
      ‖oneGradientFunctionOperator m G H (ε • u) i.val-Q-
        ε • D ((1/2:ℝ) • (oneGradientReferencePoint m Q u i.val+
          oneGradientReferencePoint m Q u (i.val+1)))‖≤η*ε := by
    rw [oneGradientFunctionOperator,oneGradientFunctionStep_eq_difference]
    have hs := oneGradient_midpoint_comparison _ _ _ _ ε M C
      (hp i.val i.isLt.le) (hp (i.val+1) (by omega))
      (hps i.val i.isLt.le) (hps (i.val+1) (by omega))
    simpa only [hH₀] using haj ε hε (he.trans_le (min_le_right _ _)) _ _ _ hs.1 hs.2
  have hout :
      ‖oneGradientFunctionOutputOperator m G H (ε • u) N-Q-
        ε • D ((1/2:ℝ) • (oneGradientReferencePoint m Q u N+oneGradientReferenceOutput m Q u N))‖≤η*ε := by
    have heq : m.output (oneGradientFunctionRun m G (ε • u) N)=
        oneGradientFunctionOutput m G (ε • u) N-oneGradientFunctionPoint m G (ε • u) N := by
      rw [oneGradientFunctionOutput,add_sub_cancel_left]
    rw [oneGradientFunctionOutputOperator,heq]
    have hs := oneGradient_midpoint_comparison _ _ _ _ ε M C (hp N le_rfl) ho (hps N le_rfl) hos
    simpa only [hH₀] using haj ε hε (he.trans_le (min_le_right _ _)) _ _ _ hs.1 hs.2
  rw [oneGradientFunctionInput,oneGradientReferenceJet,Prod.norm_def,Prod.norm_def,max_le_iff,max_le_iff]
  exact ⟨hgrad,⟨(pi_norm_le_iff_of_nonneg (mul_nonneg hη.le hε.le)).mpr hstep,hout⟩⟩

end
end krylov.Convergence
