import krylov.Convergence.OrderSearchOnlyBootstrap
import krylov.Functions.MetricFCTrajectoryComparison

/-!
Article: main_krylov, thm:D and lem:cycle-transfer, genuine compact query fields.
Use: derive uniform first-order displacement changes of the independently
executed smooth policy. Actual scalar queries are substituted only after
their complete original observed-history embedding has been proved.
Source: primitive policy calculus, finite sums and compact C-one bounds.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Stability
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The accumulated physical displacement of every actual probed policy
is the finite sum of its genuine recorded steps. Article: thm:D. -/
theorem searchOnlyRun_displacement_sum (m : ProbedMethod E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ) :
    (methodRun m A B g i).displacement=∑ j∈Finset.range i,probedStep m A B g j := by
  induction i with
  | zero=>simp only [methodRun,History.displacement,List.map_nil,List.sum_nil,Finset.range_zero,Finset.sum_empty]
  | succ i ih=>
    change probedStep m A B g i+(methodRun m A B g i).displacement=_
    rw [ih,Finset.sum_range_succ]
    exact add_comm _ _

/-- Scaling a real complete history scales its actual displacement.
Article: main_krylov, lem:U and thm:D. -/
theorem searchOnly_scaleHistory_displacement (c : ℝ) (H : History E) :
    (scaleHistory c H).displacement=c • H.displacement := by
  simp only [History.displacement,scaleHistory,List.map_map,Function.comp_def,scaleRecord]
  rw [List.smul_sum]
  simp only [List.map_map,Function.comp_def]

/-- All finite actual prefix displacements of an independent policy.
Article: main_krylov, thm:D and lem:cycle-transfer. -/
def searchOnlyFinitePoints (m : ProbedMethod E) (Q : E →L[ℝ] E) (N : ℕ)
    (z : E × (Fin N → E →L[ℝ] E)) : Fin (N+1) → E := fun i=>
  (methodRun m (fcFiniteOperatorPath Q N z.2) (fcFiniteOperatorPath Q N z.2) z.1 i.val).displacement

variable [CompleteSpace E]

/-- Primitive smooth CG-consistent policy data give genuine finite-prefix
point-field regularity. Article: main_krylov, lem:U and thm:D. -/
theorem searchOnlyFinitePoints_contDiffAt
    (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v)) (N : ℕ) (g : E)
    (hpre : ∀ i<N,CG.gradient Q g i≠0) (hs : SmoothProbedCycleAt m 2 Q g N) :
    ContDiffAt ℝ 1 (searchOnlyFinitePoints m Q N) (g,0) := by
  let A:=fun z : E × (Fin N → E →L[ℝ] E)=>fcFiniteOperatorPath Q N z.2
  have hA j : ContDiffAt ℝ 2 (fun z=>A z j) (g,0) :=
    (fcFiniteOperatorPath_analytic Q N j (g,0)).contDiffAt
  apply contDiffAt_pi.mpr
  intro i
  simp only [searchOnlyFinitePoints,searchOnlyRun_displacement_sum]
  apply ContDiffAt.sum
  intro j hj
  exact ((smoothProbed_fields_regular m hm A A Prod.fst (g,0) N
    (fun a _=>hA a) (fun a _=>hA a) contDiffAt_fst Q
    (fcFiniteOperatorPath_zero Q N) (fcFiniteOperatorPath_zero Q N) hQ hpos hpre hs j
    (by have hh:=Finset.mem_range.mp hj;omega)).2.2.1).of_le (by norm_num)

variable [FiniteDimensional ℝ E]

/-- One common finite source tube controls all genuine actual prefix
point-field changes on a compact reference family. Article: thm:D. -/
theorem compact_searchOnly_points_changes
    (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v)) (N : ℕ)
    (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i<N,CG.gradient Q g i≠0)
    (hs : ∀ g∈K,SmoothProbedCycleAt m 2 Q g N) :
    ∃ δ C : ℝ,0<δ ∧0<C ∧∀ g∈K,∀ v : E,∀ Θ : Fin N → E →L[ℝ] E,‖(v,Θ)‖≤δ →
      ∀ i≤N,‖(methodRun m (fcFiniteOperatorPath Q N Θ) (fcFiniteOperatorPath Q N Θ) (g+v) i).displacement-
        CG.displacement Q g i‖≤C*‖(v,Θ)‖ := by
  let F:=searchOnlyFinitePoints m Q N
  have hF : ∀ z∈K×ˢ{(0 : Fin N → E →L[ℝ] E)},ContDiffAt ℝ 1 F z := by
    rintro ⟨g,θ⟩ ⟨hg,hθ⟩
    have he : θ=0 := hθ
    subst θ
    exact searchOnlyFinitePoints_contDiffAt m hm Q hQ hpos N g (hpre g hg) (hs g hg)
  obtain ⟨δ,L,B,hδ,hL,_,_,hbound⟩:=compact_c1_field_bounds F
    (K×ˢ{(0 : Fin N → E →L[ℝ] E)}) (hK.prod isCompact_singleton) hF
  refine ⟨δ,L+1,hδ,by positivity,?_⟩
  intro g hg v Θ hΘ i hi
  have hd : ‖(g+v,Θ)-(g,0)‖≤δ := by
    simpa only [Prod.mk_sub_mk,add_sub_cancel_left,sub_zero] using hΘ
  have hh:=(hbound (g,0) ⟨hg,rfl⟩ (g+v,Θ) hd).1
  simp only [Prod.mk_sub_mk,add_sub_cancel_left,sub_zero] at hh
  have hb:=(norm_le_pi_norm (F (g+v,Θ)-F (g,0)) (⟨i,by omega⟩ : Fin (N+1))).trans hh
  dsimp only [F,searchOnlyFinitePoints,Pi.sub_apply] at hb
  rw [fcFiniteOperatorPath_zero,quadratic_displacement_eq_cg m hm Q hQ hpos] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith : L≤L+1) (norm_nonneg _))

end
end krylov.Convergence
