import krylov.Convergence.OrderSearchOnlyInputs
import krylov.Methods.SmoothProbedFields
import krylov.Methods.HomogeneousProtocol
import krylov.Convergence.OneGradientCompact

/-!
Article: main_krylov, thm:D and lem:U, genuine finite search-only domains.
Use: primitive smooth policy charts and actual quadratic CG consistency
supply one uniform positive search-parameter tube on a compact reference
family. These domains will identify the actual scalar observations with
the independently executed true averaged-Hessian protocol.
Source: actual finite-coordinate policy calculus and compact open tubes.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual raw search scalar in finite joint initial-gradient and
operator coordinates. Article: main_krylov, thm:D. -/
def searchOnlyFiniteLength (m : ProbedMethod E) (Q : E →L[ℝ] E) (N i : ℕ)
    (z : E × (Fin N → E →L[ℝ] E)) : ℝ :=
  let A:=fcFiniteOperatorPath Q N z.2
  lineLength (probedGradient m A A z.1 i) (probedDirection m A A z.1 i) (probedProbe m A A z.1 i)

/-- Genuine primitive smoothness makes each actual finite search scalar
continuous at its true quadratic reference. Article: lem:U, thm:D. -/
theorem searchOnlyFiniteLength_contDiffAt
    (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v)) (N : ℕ) (g : E)
    (hpre : ∀ i<N,CG.gradient Q g i≠0) (hs : SmoothProbedCycleAt m 2 Q g N)
    (i : ℕ) (hi : i<N) :
    ContDiffAt ℝ 2 (searchOnlyFiniteLength m Q N i) (g,0) := by
  let A:=fun z : E × (Fin N → E →L[ℝ] E)=>fcFiniteOperatorPath Q N z.2
  have hA j : ContDiffAt ℝ 2 (fun z=>A z j) (g,0) :=
    (fcFiniteOperatorPath_analytic Q N j (g,0)).contDiffAt
  exact (smoothProbed_search_regular m hm A A Prod.fst (g,0) N
    (fun j _=>hA j) (fun j _=>hA j) contDiffAt_fst Q
    (fcFiniteOperatorPath_zero Q N) (fcFiniteOperatorPath_zero Q N) hQ hpos hpre hs i hi).1

/-- Every true compact full-reference family has a common positive
search-length tube derived from primitive smooth policy data. Neither
actual nonlinear search positivity nor a source-domain margin is assumed.
Article: main_krylov, thm:D and lem:U. -/
theorem compact_searchOnly_positive_lengths
    (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v)) (N : ℕ)
    (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i<N,CG.gradient Q g i≠0)
    (hs : ∀ g∈K,SmoothProbedCycleAt m 2 Q g N) :
    ∃ δ : ℝ,0<δ ∧∀ g∈K,∀ v : E,∀ Θ : Fin N → E →L[ℝ] E,‖(v,Θ)‖≤δ →
      ∀ i<N,0<searchOnlyFiniteLength m Q N i (g+v,Θ) := by
  let Z:=E × (Fin N → E →L[ℝ] E)
  let K₀ : Set Z:=K×ˢ{0}
  let S : Set Z:={z | ∀ i<N,0<searchOnlyFiniteLength m Q N i z}
  have hsub : K₀⊆interior S := by
    rintro ⟨g,θ⟩ ⟨hg,hθ⟩
    have hθ0 : θ=0 := hθ
    subst θ
    apply mem_interior_iff_mem_nhds.mpr
    have hi (i : Fin N) : ∀ᶠ z : Z in 𝓝 (g,0),0<searchOnlyFiniteLength m Q N i.val z := by
      have hp : 0<searchOnlyFiniteLength m Q N i.val (g,0) := by
        simp only [searchOnlyFiniteLength,fcFiniteOperatorPath_zero,probedDirection,probedProbe]
        exact (quadratic_search_positive m hm Q hQ hpos g i.val (hpre g hg i.val i.isLt)).2
      exact (searchOnlyFiniteLength_contDiffAt m hm Q hQ hpos N g (hpre g hg) (hs g hg)
        i.val i.isLt).continuousAt.eventually (lt_mem_nhds hp)
    exact (Filter.eventually_all.mpr hi).mono (fun z hz i hi=>hz (⟨i,hi⟩ : Fin N))
  obtain ⟨δ,hδ,htube⟩:=(hK.prod isCompact_singleton).exists_cthickening_subset_open isOpen_interior hsub
  refine ⟨δ,hδ,?_⟩
  intro g hg v Θ hΘ
  apply interior_subset (htube (mem_cthickening_of_dist_le (g+v,Θ) (g,0) δ K₀ ⟨hg,rfl⟩ ?_))
  simpa only [dist_eq_norm,Prod.mk_sub_mk,add_sub_cancel_left,sub_zero] using hΘ

end
end krylov.Convergence
