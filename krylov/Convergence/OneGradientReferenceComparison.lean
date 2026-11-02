import krylov.Convergence.OneGradientFieldChanges
import krylov.Convergence.OneGradientSourceBounds
import krylov.Functions.MetricFCTrajectoryComparison

/-!
Article: main_krylov, lem:cycle-transfer, thm:V and prop:EL.
Use: compare actual scalar one-gradient queries with the genuinely executed
quadratic policy, using its derived true finite source input. All reference
step and output differences retain the source factor epsilon times the
actual input norm. Native quadratic shadow bounds follow by substitution.
Source: genuine C-one finite-field changes, exact homogeneity and telescoping.
-/
namespace krylov.Convergence
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Functions
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- The actual evaluated quadratic-reference point, including the
prescribed initial position. Article: thm:V and prop:EL. -/
def oneGradientReferencePoint (m : OneGradientMethod E) (Q : E →L[ℝ] E) (u : E) (i : ℕ) : E :=
  u+(oneGradientRun m (fun _=>Q) (Q u) i).displacement

/-- The actual unevaluated output of the quadratic-reference policy.
Article: thm:V and prop:EL. -/
def oneGradientReferenceOutput (m : OneGradientMethod E) (Q : E →L[ℝ] E) (u : E) (N : ℕ) : E :=
  oneGradientReferencePoint m Q u N+m.output (oneGradientRun m (fun _=>Q) (Q u) N)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Consecutive true quadratic-reference vertices differ by exactly the
real reference query. Article: lem:cycle-transfer. -/
theorem oneGradientReferencePoint_step (m : OneGradientMethod E) (Q : E →L[ℝ] E) (u : E) (i : ℕ) :
    oneGradientReferencePoint m Q u (i+1)-oneGradientReferencePoint m Q u i=
      oneGradientStep m (fun _=>Q) (Q u) i := by
  simp only [oneGradientReferencePoint,oneGradientRun,oneGradientAdvance,History.displacement,
    List.map_cons,List.sum_cons,oneGradientStep]
  abel

omit [CompleteSpace E] in
/-- Real scalar query and virtual-correction fields differ from their
quadratic references by epsilon times the true measured input norm.
Article: main_krylov, lem:cycle-transfer, thm:V and prop:EL. -/
theorem compact_oneGradient_native_field_comparison
    (m : OneGradientMethod E) (Q : E →L[ℝ] E) (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hreg : ∀ g∈K,ContDiffAt ℝ 1 (oneGradientFiniteField m Q N) (g,0))
    (hhom : ∀ (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ),0<c →
      (∀ i<N,oneGradientStep m A (c • g) i=c • oneGradientStep m A g i) ∧
        m.output (oneGradientRun m A (c • g) N)=c • m.output (oneGradientRun m A g N)) :
    ∃ δ C : ℝ,0<δ ∧0<C ∧∀ G : E → E,∀ H : E → E →L[ℝ] E,∀ ε : ℝ,0<ε →∀ u : E,Q u∈K →
      ‖oneGradientFunctionInput m G H Q ε u N‖≤δ →
      (∀ i≤N,oneGradientFunctionRun m G (ε • u) i=
        oneGradientRun m (oneGradientFunctionOperator m G H (ε • u)) (G (ε • u)) i) →
      (∀ i<N,‖m.step (oneGradientFunctionRun m G (ε • u) i)-
        ε • oneGradientStep m (fun _=>Q) (Q u) i‖≤C*ε*‖oneGradientFunctionInput m G H Q ε u N‖) ∧
      ‖m.output (oneGradientFunctionRun m G (ε • u) N)-
        ε • m.output (oneGradientRun m (fun _=>Q) (Q u) N)‖≤C*ε*‖oneGradientFunctionInput m G H Q ε u N‖ := by
  obtain ⟨δ,C,hδ,hC,hchange⟩ := compact_oneGradient_field_changes m Q N K hK hreg
  refine ⟨δ,C,hδ,hC,?_⟩
  intro G H ε hε u hKu hinput hrun
  let I := oneGradientFunctionInput m G H Q ε u N
  let J := (I.1,I.2.1)
  let Af := fcFiniteOperatorPath Q N I.2.1
  have hJ : ‖J‖≤‖I‖ := by
    rw [show J=(I.1,I.2.1) from rfl,Prod.norm_def,max_le_iff]
    exact ⟨norm_fst_le I,(norm_fst_le I.2).trans (norm_snd_le I)⟩
  have hc := hchange (Q u) hKu I.1 I.2.1 (hJ.trans hinput)
  have hg : Q u+I.1=ε⁻¹ • G (ε • u) := by dsimp only [I,oneGradientFunctionInput]; abel
  have hscale : G (ε • u)=ε • (Q u+I.1) := by
    rw [hg,smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hAf i (hi : i<N) : Af i=oneGradientFunctionOperator m G H (ε • u) i := by
    simp only [Af,fcFiniteOperatorPath,hi,dite_true,I,oneGradientFunctionInput,add_sub_cancel]
  have hr i (hi : i≤N) : oneGradientFunctionRun m G (ε • u) i=oneGradientRun m Af (G (ε • u)) i := by
    rw [hrun i hi]
    exact oneGradientRun_congr_prefix m _ _ _ i (fun j hj=>(hAf j (hj.trans_le hi)).symm)
  have hs i (hi : i<N) : m.step (oneGradientFunctionRun m G (ε • u) i)=
      ε • oneGradientStep m Af (Q u+I.1) i := by
    rw [hr i hi.le,hscale]
    exact (hhom Af (Q u+I.1) ε hε).1 i hi
  have ho : m.output (oneGradientFunctionRun m G (ε • u) N)=
      ε • m.output (oneGradientRun m Af (Q u+I.1) N) := by
    rw [hr N le_rfl,hscale]
    exact (hhom Af (Q u+I.1) ε hε).2
  have hb : ‖oneGradientFiniteField m Q N (Q u+I.1,I.2.1)-
      oneGradientFiniteField m Q N (Q u,0)‖≤C*‖I‖ :=
    hc.trans (mul_le_mul_of_nonneg_left hJ hC.le)
  refine ⟨?_,?_⟩
  · intro i hi
    have hh := ((norm_le_pi_norm
      (oneGradientFiniteField m Q N (Q u+I.1,I.2.1)-oneGradientFiniteField m Q N (Q u,0)).1
      ⟨i,hi⟩).trans ((norm_fst_le _).trans hb))
    simp only [oneGradientFiniteField,Prod.mk_sub_mk,Pi.sub_apply,fcFiniteOperatorPath_zero] at hh
    rw [hs i hi,←smul_sub,norm_smul,Real.norm_of_nonneg hε.le]
    exact (mul_le_mul_of_nonneg_left hh hε.le).trans_eq (by ring)
  · have hh := (norm_snd_le _).trans hb
    simp only [oneGradientFiniteField,Prod.mk_sub_mk,fcFiniteOperatorPath_zero] at hh
    rw [ho,←smul_sub,norm_smul,Real.norm_of_nonneg hε.le]
    exact (mul_le_mul_of_nonneg_left hh hε.le).trans_eq (by ring)

omit [CompleteSpace E] in
/-- All real evaluated vertices and the genuinely unevaluated output
shadow the executed quadratic policy with the same source-weighted order.
Article: lem:cycle-transfer, thm:V and prop:EL. -/
theorem compact_oneGradient_native_point_comparison
    (m : OneGradientMethod E) (Q : E →L[ℝ] E) (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hreg : ∀ g∈K,ContDiffAt ℝ 1 (oneGradientFiniteField m Q N) (g,0))
    (hhom : ∀ (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ),0<c →
      (∀ i<N,oneGradientStep m A (c • g) i=c • oneGradientStep m A g i) ∧
        m.output (oneGradientRun m A (c • g) N)=c • m.output (oneGradientRun m A g N)) :
    ∃ δ C : ℝ,0<δ ∧0<C ∧∀ G : E → E,∀ H : E → E →L[ℝ] E,∀ ε : ℝ,0<ε →∀ u : E,Q u∈K →
      ‖oneGradientFunctionInput m G H Q ε u N‖≤δ →
      (∀ i≤N,oneGradientFunctionRun m G (ε • u) i=
        oneGradientRun m (oneGradientFunctionOperator m G H (ε • u)) (G (ε • u)) i) →
      (∀ i≤N,‖oneGradientFunctionPoint m G (ε • u) i-ε • oneGradientReferencePoint m Q u i‖≤
        (i:ℝ)*(C*ε*‖oneGradientFunctionInput m G H Q ε u N‖)) ∧
      ‖oneGradientFunctionOutput m G (ε • u) N-ε • oneGradientReferenceOutput m Q u N‖≤
        (N+1:ℕ)*(C*ε*‖oneGradientFunctionInput m G H Q ε u N‖) := by
  obtain ⟨δ,C,hδ,hC,hfields⟩ := compact_oneGradient_native_field_comparison m Q N K hK hreg hhom
  refine ⟨δ,C,hδ,hC,?_⟩
  intro G H ε hε u hKu hinput hrun
  obtain ⟨hs,ho⟩ := hfields G H ε hε u hKu hinput hrun
  let B := C*ε*‖oneGradientFunctionInput m G H Q ε u N‖
  have hp := trajectory_step_error_bound (oneGradientFunctionPoint m G (ε • u))
    (fun i=>ε • oneGradientReferencePoint m Q u i) N B (by
      simp only [oneGradientFunctionPoint,oneGradientFunctionRun,oneGradientReferencePoint,
        oneGradientRun,History.displacement,List.map_nil,List.sum_nil,add_zero]) (fun i hi=>by
      rw [←oneGradientFunctionStep_eq_difference,←smul_sub,oneGradientReferencePoint_step]
      exact hs i hi)
  refine ⟨hp,?_⟩
  have he : oneGradientFunctionOutput m G (ε • u) N-ε • oneGradientReferenceOutput m Q u N=
      (oneGradientFunctionPoint m G (ε • u) N-ε • oneGradientReferencePoint m Q u N)+
      (m.output (oneGradientFunctionRun m G (ε • u) N)-
        ε • m.output (oneGradientRun m (fun _=>Q) (Q u) N)) := by
    simp only [oneGradientFunctionOutput,oneGradientReferenceOutput,smul_add]
    abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (hp N le_rfl) ho).trans_eq (by push_cast; ring))

end
end krylov.Convergence
