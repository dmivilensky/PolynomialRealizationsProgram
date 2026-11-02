import krylov.Convergence.OneGradientRepresentatives
import krylov.Functions.FCReferenceFields
import krylov.Stability.CompactC1Bounds

/-!
Article: main_krylov, thm:V, prop:EL and lem:cycle-transfer.
Use: obtain uniform genuine one-gradient query growth from actual primitive
policy regularity, before choosing or localizing a nonlinear function.
The regularity assumptions concern the independent finite operator executor;
the native output growth is a conclusion derived through true measured
representatives. XRFC and evaluated launch discharge these assumptions from
their original observed trial charts in separate specialization modules.
Source: compact C-one field bounds and genuine scalar homogeneity.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear krylov.Stability
open scoped InnerProductSpace NNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- The actual finite independent-operator query field, including the
unevaluated correction only as a semantic vector. Article: thm:V. -/
def oneGradientFiniteField (m : OneGradientMethod E) (Q : E →L[ℝ] E) (N : ℕ)
    (z : E × (Fin N → E →L[ℝ] E)) : (Fin N → E) × E :=
  (fun i=>oneGradientStep m (fcFiniteOperatorPath Q N z.2) z.1 i.val,
    m.output (oneGradientRun m (fcFiniteOperatorPath Q N z.2) z.1 N))

omit [CompleteSpace E] in
/-- True C-one policy fields have one bounded full input tube before
every compact reference set. Article: lem:cycle-transfer, thm:V and prop:EL. -/
theorem compact_oneGradient_fields (m : OneGradientMethod E) (Q : E →L[ℝ] E) (N : ℕ)
    (K : Set E) (hK : IsCompact K)
    (hstep : ∀ g∈K,∀ i<N,ContDiffAt ℝ 1
      (fun z : E × (Fin N → E →L[ℝ] E)=>oneGradientStep m (fcFiniteOperatorPath Q N z.2) z.1 i) (g,0))
    (hout : ∀ g∈K,ContDiffAt ℝ 1
      (fun z : E × (Fin N → E →L[ℝ] E)=>m.output (oneGradientRun m (fcFiniteOperatorPath Q N z.2) z.1 N)) (g,0)) :
    ∃ δ M : ℝ,0<δ ∧0<M ∧∀ g∈K,∀ v : E,∀ Θ : Fin N → E →L[ℝ] E,‖(v,Θ)‖≤δ →
      (∀ i<N,‖oneGradientStep m (fcFiniteOperatorPath Q N Θ) (g+v) i‖≤M) ∧
        ‖m.output (oneGradientRun m (fcFiniteOperatorPath Q N Θ) (g+v) N)‖≤M := by
  let F := oneGradientFiniteField m Q N
  have hF : ∀ z∈K×ˢ{(0 : Fin N → E →L[ℝ] E)},ContDiffAt ℝ 1 F z := by
    rintro ⟨g,θ⟩ ⟨hg,hθ⟩
    have he : θ=0 := hθ
    subst θ
    exact (contDiffAt_pi.mpr (fun i : Fin N=>hstep g hg i.val i.isLt)).prodMk (hout g hg)
  obtain ⟨δ,L,B,hδ,hL,hB,_,hbound⟩ := compact_c1_field_bounds F
    (K×ˢ{(0 : Fin N → E →L[ℝ] E)}) (hK.prod isCompact_singleton) hF
  refine ⟨δ,B+L+1,hδ,by positivity,?_⟩
  intro g hg v Θ hΘ
  have hd : ‖(g+v,Θ)-(g,0)‖≤δ := by
    simpa only [Prod.mk_sub_mk,add_sub_cancel_left,sub_zero] using hΘ
  have hb := (hbound (g,0) ⟨hg,rfl⟩ (g+v,Θ) hd).2
  refine ⟨fun i hi=>?_,?_⟩
  · exact ((norm_le_pi_norm (F (g+v,Θ)).1 ⟨i,hi⟩).trans
      ((norm_fst_le _).trans hb)).trans (by linarith)
  · exact ((norm_snd_le _).trans hb).trans (by linarith)

/-- Every real nonlinear query is uniformly small relative to its actual
initial gradient scale, when the true gradient model error is globally
small Lipschitz. No native trajectory bound is assumed.
Article: thm:V and prop:EL, source localization backend. -/
theorem compact_oneGradient_function_growth
    (m : OneGradientMethod E) (Q : E →L[ℝ] E) (hQ : IsSelfAdjoint Q) (N : ℕ)
    (K : Set E) (hK : IsCompact K)
    (hstep : ∀ g∈K,∀ i<N,ContDiffAt ℝ 1
      (fun z : E × (Fin N → E →L[ℝ] E)=>oneGradientStep m (fcFiniteOperatorPath Q N z.2) z.1 i) (g,0))
    (hout : ∀ g∈K,ContDiffAt ℝ 1
      (fun z : E × (Fin N → E →L[ℝ] E)=>m.output (oneGradientRun m (fcFiniteOperatorPath Q N z.2) z.1 N)) (g,0))
    (hhom : ∀ (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ),0<c →
      (∀ i<N,oneGradientStep m A (c • g) i=c • oneGradientStep m A g i) ∧
        m.output (oneGradientRun m A (c • g) N)=c • m.output (oneGradientRun m A g N)) :
    ∃ δ M : ℝ,0<δ ∧0<M ∧∀ G : E → E,∀ x₀ : E,∀ η : ℝ≥0,
      LipschitzWith η (fun x=>G x-Q x) → (η:ℝ)≤δ →∀ ε : ℝ,0<ε →∀ g∈K,
      ‖ε⁻¹ • G x₀-g‖≤δ →
      (∀ i<N,‖m.step (oneGradientFunctionRun m G x₀ i)‖≤ε*M) ∧
        ‖m.output (oneGradientFunctionRun m G x₀ N)‖≤ε*M ∧
        (∀ i≤N,‖oneGradientFunctionPoint m G x₀ i-x₀‖≤N*(ε*M)) ∧
        ‖oneGradientFunctionOutput m G x₀ N-x₀‖≤(N+1:ℕ)*(ε*M) := by
  obtain ⟨δ,M,hδ,hM,hfields⟩ := compact_oneGradient_fields m Q N K hK hstep hout
  refine ⟨δ,M,hδ,hM,?_⟩
  intro G x₀ η hG hη ε hε g hg hinit
  obtain ⟨A,hA,hrun⟩ := oneGradientFunctionRun_representatives m G x₀ Q hQ hG
  let Θ : Fin N → E →L[ℝ] E := fun i=>A i.val-Q
  let Af := fcFiniteOperatorPath Q N Θ
  let g' := ε⁻¹ • G x₀
  have hΘ : ‖Θ‖≤δ := (pi_norm_le_iff_of_nonneg hδ.le).mpr
    (fun i=>(hA i.val).2.trans hη)
  have hg' : g+(g'-g)=g' := by abel
  have hf := hfields g hg (g'-g) Θ (norm_prod_le_iff.mpr ⟨hinit,hΘ⟩)
  rw [hg'] at hf
  have hAf i (hi : i<N) : Af i=A i := by simp only [Af,fcFiniteOperatorPath,hi,dite_true,Θ,add_sub_cancel]
  have hrun' i (hi : i≤N) : oneGradientFunctionRun m G x₀ i=oneGradientRun m Af (G x₀) i := by
    rw [hrun i]
    exact oneGradientRun_congr_prefix m A Af (G x₀) i (fun j hj=>(hAf j (hj.trans_le hi)).symm)
  have hscale : G x₀=ε • g' := by
    dsimp only [g']; rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hs i (hi : i<N) : ‖m.step (oneGradientFunctionRun m G x₀ i)‖≤ε*M := by
    rw [hrun' i hi.le,hscale]
    change ‖oneGradientStep m Af (ε • g') i‖≤_
    rw [(hhom Af g' ε hε).1 i hi,norm_smul,Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left (hf.1 i hi) hε.le
  have ho : ‖m.output (oneGradientFunctionRun m G x₀ N)‖≤ε*M := by
    rw [hrun' N le_rfl,hscale,(hhom Af g' ε hε).2,norm_smul,Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left hf.2 hε.le
  have hp i (hi : i≤N) : ‖oneGradientFunctionPoint m G x₀ i-x₀‖≤N*(ε*M) := by
    simp only [oneGradientFunctionPoint,add_sub_cancel_left]
    rw [hrun' i hi,oneGradientRun_displacement_sum]
    calc
      _ ≤ ∑ j∈Finset.range i,‖oneGradientStep m Af (G x₀) j‖ := norm_sum_le _ _
      _ ≤ ∑ _j∈Finset.range i,ε*M := Finset.sum_le_sum fun j hj=>by
        have hh := hs j ((Finset.mem_range.mp hj).trans_le hi)
        rwa [hrun' j ((Finset.mem_range.mp hj).le.trans hi)] at hh
      _ = i*(ε*M) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) (mul_nonneg hε.le hM.le)
  refine ⟨hs,ho,hp,?_⟩
  have he : oneGradientFunctionOutput m G x₀ N-x₀=
      (oneGradientFunctionPoint m G x₀ N-x₀)+m.output (oneGradientFunctionRun m G x₀ N) := by
    unfold oneGradientFunctionOutput
    abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (hp N le_rfl) ho).trans_eq (by push_cast; ring))

end
end krylov.Convergence
