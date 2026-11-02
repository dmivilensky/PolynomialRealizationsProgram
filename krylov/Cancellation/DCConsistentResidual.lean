import krylov.Cancellation.DCLinearizedResidual
import krylov.Cancellation.ConsistentProducts
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), original consistent-estimate compact fresh residual.
Use: derive genuine fresh-only residuals up to one compact-uniform quadratic
remainder from the original primitive C-one observed estimate hypotheses.
Source: actual compact reference-weight DC expansion and true consistent
finite product cancellation; no fresh-only response premise is assumed.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Consistent reference estimates leave precisely the actual newest physical
defect in every true retained DC residual, with one compact-uniform quadratic
remainder under original primitive C-one data.
Use: the source's fresh-only assertion holds for actual executed histories
and real perturbed defects, with all true inverse neighborhoods derived.
Article: main_krylov, thm:dcs(c), consistent estimates leave the fresh defect alone.
Proof: derive the genuine compact native reference-weight expansion. Every
consistent reference multiplier is zero with a proved nonzero original
estimate, so all actual old product terms vanish and only the true newest
physical defect remains; the same genuine quadratic remainder bound applies. -/
theorem dc_slide_consistent_compact_fresh
    (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k) (estimate : History E → ℝ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (Q : X → E →L[ℝ] E)
    (T i N : ℕ) (hT : i+N<T) (hN : 0<N) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K,∀ k<T,ContDiffAt ℝ 1 (fun p => A p k) x)
    (hB : ∀ x∈K,∀ k<T,ContDiffAt ℝ 1 (fun p => B p k) x)
    (hg : ∀ x∈K,ContDiffAt ℝ 1 g x)
    (hAx : ∀ x∈K,A x=fun _ => Q x) (hBx : ∀ x∈K,B x=fun _ => Q x)
    (hQ : ∀ x∈K,(Q x).toLinearMap.IsSymmetric)
    (hpos : ∀ x∈K,∀ v : E,v≠0 → 0 < inner ℝ v (Q x v))
    (hpre : ∀ x∈K,∀ k<T,CG.gradient (Q x) (g x) k≠0)
    (ha : ∀ x∈K,∀ k<T,
      let H := methodRun (dcSlideMethod memory estimate) (fun _ => Q x) (fun _ => Q x) (g x) k
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ x∈K,∀ k<T,0<estimate (methodRun (dcSlideMethod memory estimate)
      (fun _ => Q x) (fun _ => Q x) (g x) k))
    (hAi : ∀ p : X,(A p i).toLinearMap.IsSymmetric)
    (hkeep : ∀ j<N,(i+1+j)-1-i<memory (i+1+j))
    (hconsistent : ∀ x∈K,∀ l<N,
      estimate (methodRun (dcSlideMethod memory estimate) (A x) (B x) (g x) (i+1+l))=
        dcSearchedLength memory estimate (A x) (B x) (g x) (i+1+l)) :
    let m := dcSlideMethod memory estimate
    ∃ δ C : ℝ,0<δ ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤δ →
      ‖inner ℝ (probedStep m (A y) (B y) (g y) i) (probedGradient m (A y) (B y) (g y) (i+1+N))-
        dcFreshPairing memory estimate (A y) (B y) (g y) i (i+N)‖≤C*‖y-x‖^2 := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := dc_slide_compact_residual_expansion memory hm estimate A B g Q T i N hT K hK
    hA hB hg hAx hBx hQ hpos hpre ha ha0 hAi hkeep (freezeSearch := true)
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx y hy
  have hs := consistent_residual_products
    (fun l => dcSearchedLength memory estimate (A x) (B x) (g x) (i+1+l))
    (fun l => estimate (methodRun (dcSlideMethod memory estimate) (A x) (B x) (g x) (i+1+l)))
    (fun j => dcFreshPairing memory estimate (A y) (B y) (g y) i (i+1+j)) N hN
    (fun l hl => by
      rw [hAx x hx,hBx x hx]
      exact (ha0 x hx (i+1+l) (by omega)).ne')
    (fun l hl => (hconsistent x hx l hl).symm)
  have he := hbound x hx y hy
  simp only [ite_true] at he
  rw [hs] at he
  simpa only [show i+1+(N-1)=i+N by omega] using he

end
end krylov.Cancellation
