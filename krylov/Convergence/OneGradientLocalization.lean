import krylov.Convergence.OneGradientCompact
import krylov.Nonlinear.GradientLocal

/-!
Article: main_krylov, thm:V, prop:EL and lem:cycle-transfer.
Use: localize every actual evaluated query and the genuinely unevaluated
output from primitive local gradient data. A globally Lipschitz auxiliary
oracle is introduced only inside the proof, and exact data-only causality
identifies the entire true local execution afterwards.
Source: the reused McShane extension and true measured representative
calculus; no native trajectory or source-input estimate is a hypothesis.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Every actual one-gradient source is localized from its true local
gradient error, uniformly before the full compact operator reference set.
Article: thm:V and prop:EL, native source domain. -/
theorem compact_oneGradient_localization
    (m : OneGradientMethod E) (Q : E →L[ℝ] E) (hQ : IsSelfAdjoint Q)
    (K : Set E) (hK : IsCompact K)
    (hstep : ∀ g∈K,∀ i<N,ContDiffAt ℝ 1
      (fun z : E × (Fin N → E →L[ℝ] E)=>oneGradientStep m (fcFiniteOperatorPath Q N z.2) z.1 i) (g,0))
    (hout : ∀ g∈K,ContDiffAt ℝ 1
      (fun z : E × (Fin N → E →L[ℝ] E)=>m.output (oneGradientRun m (fcFiniteOperatorPath Q N z.2) z.1 N)) (g,0))
    (hhom : ∀ (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ),0<c →
      (∀ i<N,oneGradientStep m A (c • g) i=c • oneGradientStep m A g i) ∧
        m.output (oneGradientRun m A (c • g) N)=c • m.output (oneGradientRun m A g N)) :
    ∃ δ M : ℝ,0<δ ∧0<M ∧∀ G : E → E,G 0=0 →∀ r R : ℝ,0<r →0<R →
      ∀ η : ℝ≥0,LipschitzOnWith η (fun x=>G x-Q x) (ball 0 r) →
      ((NNReal.sqrt n*η:ℝ≥0):ℝ)≤δ → ((NNReal.sqrt n*η:ℝ≥0):ℝ)*R≤δ →
      ∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u : E,‖u‖≤R →Q u∈K →
      (∀ i≤N,oneGradientFunctionPoint m G (ε • u) i∈ball 0 r ∧
        ‖oneGradientFunctionPoint m G (ε • u) i‖≤ε*(R+(N+1:ℕ)*M)) ∧
      (oneGradientFunctionOutput m G (ε • u) N∈ball 0 r ∧
        ‖oneGradientFunctionOutput m G (ε • u) N‖≤ε*(R+(N+1:ℕ)*M)) ∧
      (∀ i<N,‖m.step (oneGradientFunctionRun m G (ε • u) i)‖≤ε*M) ∧
        ‖m.output (oneGradientFunctionRun m G (ε • u) N)‖≤ε*M := by
  obtain ⟨δ,M,hδ,hM,hgrowth⟩ := compact_oneGradient_function_growth m Q hQ N K hK hstep hout hhom
  refine ⟨δ,M,hδ,hM,?_⟩
  intro G hG₀ r R hr hR η hlocal hη hηR
  obtain ⟨F,hagree,hF⟩ := exists_gradient_model_extension G Q hlocal
  have hF₀ : F 0=0 := (hagree (mem_ball_self hr)).symm.trans hG₀
  let D := R+(N+1:ℕ)*M
  have hD : 0<D := by dsimp only [D]; positivity
  refine ⟨r/(D+1),by positivity,?_⟩
  intro ε hε he u hu hKu
  have hsmall : ε*D<r := by
    have hh := (lt_div_iff₀ (by positivity : 0<D+1)).mp he
    nlinarith only [hh,hε]
  have hinit : ‖ε⁻¹ • F (ε • u)-Q u‖≤δ :=
    (normalized_gradient_error_le F Q hF₀ hF u hε).trans
      ((mul_le_mul_of_nonneg_left hu (NNReal.coe_nonneg _)).trans hηR)
  obtain ⟨hs,ho,hp,houtp⟩ := hgrowth F (ε • u) _ hF hη ε hε (Q u) hKu hinit
  have hstart : ‖ε • u‖≤ε*R := by
    rw [norm_smul,Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left hu hε.le
  have hpoints i (hi : i≤N) : ‖oneGradientFunctionPoint m F (ε • u) i‖≤ε*D := by
    have ht := (norm_le_norm_sub_add (oneGradientFunctionPoint m F (ε • u) i) (ε • u)).trans
      (add_le_add (hp i hi) hstart)
    have hm : (N:ℝ)*(ε*M)+ε*R≤ε*D := by dsimp only [D]; push_cast; nlinarith only [mul_nonneg hε.le hM.le]
    exact ht.trans hm
  have houtput : ‖oneGradientFunctionOutput m F (ε • u) N‖≤ε*D := by
    exact ((norm_le_norm_sub_add _ (ε • u)).trans (add_le_add houtp hstart)).trans_eq (by dsimp only [D]; ring)
  have hpointsBall i (hi : i≤N) : oneGradientFunctionPoint m F (ε • u) i∈ball 0 r := by
    rw [mem_ball_zero_iff]
    exact (hpoints i hi).trans_lt hsmall
  have heq i (hi : i≤N) : oneGradientFunctionRun m F (ε • u) i=oneGradientFunctionRun m G (ε • u) i := by
    apply oneGradientFunctionRun_congr m F G (ε • u) i
    · exact (hagree (by simpa only [oneGradientFunctionPoint,oneGradientFunctionRun,
        History.displacement,List.map_nil,List.sum_nil,add_zero] using hpointsBall 0 (by omega))).symm
    · intro j hj
      rw [←oneGradientFunctionPoint_succ]
      exact (hagree (hpointsBall (j+1) (by omega))).symm
  have hpointEq i (hi : i≤N) : oneGradientFunctionPoint m F (ε • u) i=oneGradientFunctionPoint m G (ε • u) i := by
    unfold oneGradientFunctionPoint
    rw [heq i hi]
  have houtputEq : oneGradientFunctionOutput m F (ε • u) N=oneGradientFunctionOutput m G (ε • u) N := by
    unfold oneGradientFunctionOutput
    rw [hpointEq N le_rfl,heq N le_rfl]
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    rw [←hpointEq i hi]
    exact ⟨hpointsBall i hi,hpoints i hi⟩
  · rw [←houtputEq]
    exact ⟨by simpa only [mem_ball_zero_iff] using houtput.trans_lt hsmall,houtput⟩
  · intro i hi
    rw [←heq i hi.le]
    exact hs i hi
  · rw [←heq N le_rfl]
    exact ho

end
end krylov.Convergence
