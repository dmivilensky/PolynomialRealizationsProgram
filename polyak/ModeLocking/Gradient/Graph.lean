import polyak.ModeLocking.Gradient.Kappa
import polyak.ModeLocking.Gradient.ImplicitUnique

/-! The source zero surface is an analytic kappa graph, with local uniqueness,
obtained from the strictly negative kappa derivative. -/
noncomputable section
namespace polyak.ModeLocking.Gradient
open General Levels Continuation Filter
open scoped Topology

abbrev Plane := Fin 2→ℝ

def planeParameters (q:Tuning) : Plane := ![q.y,q.beta]
def graphPoint (z:Plane×ℝ) : Parameters := ![z.2,z.1 0,z.1 1]

theorem scalar_isInvertible {a:ℝ→L[ℝ]ℝ} (ha:a 1≠0) : a.IsInvertible := by
  let e:ℝ≃L[ℝ]ℝ:=(LinearEquiv.smulOfNeZero ℝ ℝ (a 1) ha).toContinuousLinearEquiv
  refine ⟨e,?_⟩
  apply ContinuousLinearMap.ext
  intro x
  change a 1*x=a x
  have hx:a x=x*a 1:=by simpa only [smul_eq_mul,mul_one] using a.map_smul x (1:ℝ)
  rw [hx,mul_comm]

theorem analyticAt_graphPoint (z:Plane×ℝ) : AnalyticAt ℝ graphPoint z := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analyticAt_snd
  · exact ((ContinuousLinearMap.proj (R:=ℝ) 0 : Plane→L[ℝ]ℝ).analyticAt z.1).comp analyticAt_fst
  · exact ((ContinuousLinearMap.proj (R:=ℝ) 1 : Plane→L[ℝ]ℝ).analyticAt z.1).comp analyticAt_fst

theorem analytic_zero_graph {q:Tuning} {S:Parameters→ℝ}
    (hS:AnalyticAt ℝ S (parameters q)) (hzero:S (parameters q)=0)
    (hκ:fderiv ℝ S (parameters q) kappaDirection≠0) :
    ∃g:Plane→ℝ,AnalyticAt ℝ g (planeParameters q) ∧ g (planeParameters q)=q.kappa ∧
      (∀ᶠp in 𝓝 (planeParameters q),S ![g p,p 0,p 1]=0) ∧
      ∀ᶠz:Plane×ℝ in 𝓝 (planeParameters q,q.kappa),S (graphPoint z)=0 ↔ g z.1=z.2 := by
  let u:Plane×ℝ:=(planeParameters q,q.kappa)
  let F:Plane×ℝ→ℝ:=fun z=>S (graphPoint z)
  have hpoint:graphPoint u=parameters q:=rfl
  have hF:AnalyticAt ℝ F u:=hS.comp (f:=graphPoint) (analyticAt_graphPoint u)
  let part:ℝ→L[ℝ]ℝ:=fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ Plane ℝ
  have hin:HasFDerivAt (fun κ:ℝ=>(planeParameters q,κ))
      (ContinuousLinearMap.inr ℝ Plane ℝ) q.kappa:=
    (hasFDerivAt_const (planeParameters q) q.kappa).prodMk (hasFDerivAt_id q.kappa)
  have hpart:=hF.differentiableAt.hasFDerivAt.comp q.kappa hin
  have hpartial:HasDerivAt (fun κ:ℝ=>S ![κ,q.y,q.beta]) (part 1) q.kappa:=by
    exact hpart.hasDerivAt
  have hsource:=hS.differentiableAt.hasFDerivAt.comp_hasDerivAt q.kappa (hasDerivAt_kappaLine q)
  have he:part 1=fderiv ℝ S (parameters q) kappaDirection:=hpartial.unique hsource
  have hp:part.IsInvertible:=scalar_isInvertible (by rw [he];exact hκ)
  obtain ⟨g,hg,hbase,hsol,hiff⟩:=analytic_implicit_function_unique hF hp
  refine ⟨g,hg,hbase,?_,?_⟩
  · filter_upwards [hsol] with p hp
    change S ![g p,p 0,p 1]=S (parameters q) at hp
    exact hp.trans hzero
  · filter_upwards [hiff] with z hz
    change S (graphPoint z)=S (parameters q) ↔g z.1=z.2 at hz
    simpa only [hzero] using hz

end polyak.ModeLocking.Gradient
