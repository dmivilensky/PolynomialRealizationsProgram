import krylov.Convergence.OrderSearchOnlyTaylor

/-!
Article: main_krylov, thm:D and lem:cycle-transfer, native search-only leading gradient.
Use: genuine C3 scalar data and primitive smooth homogeneous CG-consistent
policy decisions produce the actual quadratic terminal-gradient expansion.
All source jets, query domains and scalar/operator identifications are
derived before the actual full finite Taylor polynomial is substituted.
Source: true scalar Hessian midpoint jets and genuine compact policy calculus.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The true joint finite-output derivative applied to the actual compatible
third-derivative source jet. Article: main_krylov, thm:D. -/
def searchOnlyTensorLeading (m : ProbedMethod E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) : E :=
  fderiv ℝ (searchOnlyFiniteTerminal m Q (Module.finrank ℝ E)) (Q u,0)
    (metricFCReferenceInputJet Q D u (Module.finrank ℝ E))

/-- The actual full search-only scalar cycle has its genuine compact-uniform
quadratic tensor expansion under original function and primitive policy
hypotheses. No rate, source jet or query enclosure is assumed.
Article: main_krylov, thm:D, native DC transfer. -/
theorem scalarSearchOnlyPoint_leading_gradient
    (m : ProbedMethod E) (hm : CorrectionFree m) (hc : CGConsistent m) (hh : m.Homogeneous)
    (T : E ≃L[ℝ] E) (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r →HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r →HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v))
    (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i<Module.finrank ℝ E,CG.gradient Q g i≠0)
    (hs : ∀ g∈K,SmoothProbedCycleAt m 2 Q g (Module.finrank ℝ E))
    (B : ℝ) (hB : 0<B) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u : E,‖u‖≤B →Q u∈K →
      ‖G (scalarFunctionPoint m T f G r (ε • u) (Module.finrank ℝ E))-
        ε^2 • searchOnlyTensorLeading m Q D u‖≤η*ε^2 := by
  let N:=Module.finrank ℝ E
  let U : Set E:={u | ‖u‖≤B ∧Q u∈K}
  let I:=fun ε u=>scalarSearchOnlyInput m T f G H Q r ε u N
  let J:=fun u=>metricFCReferenceInputJet Q D u N
  obtain ⟨es,S,hes,hS,hboot⟩:=scalarSearchOnly_compact_bootstrap m hm hc hh T hT f G H Q
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos N K hK hpre hs B hB
  have hsize : ∃ es : ℝ,0<es ∧∀ ε : ℝ,0<ε →ε<es →∀ u∈U,‖I ε u‖≤S*ε :=
    ⟨es,hes,fun ε hε he u hu=>(hboot ε hε he u hu.1 hu.2).1⟩
  have hjet : ∀ η : ℝ,0<η →∃ ej : ℝ,0<ej ∧∀ ε : ℝ,0<ε →ε<ej →∀ u∈U,‖I ε u-ε • J u‖≤η*ε := by
    intro η hη
    obtain ⟨ej,hej,hj⟩:=scalarSearchOnlyInput_reference_jet m hm hc hh T hT f G H Q D hD
      hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos N K hK hpre hs B hB η hη
    exact ⟨ej,hej,fun ε hε he u hu=>hj ε hε he u hu.1 hu.2⟩
  have hreg g (hg : g∈K) := searchOnlyFiniteTerminal_contDiffAt m hc Q hQ hpos N g (hpre g hg) (hs g hg)
  have hzero g (_hg : g∈K) := searchOnlyFiniteTerminal_reference_zero m hc Q hQ hpos g
  have hlead:=searchOnly_output_source_transfer m Q N U I J K hK (fun _ hu=>hu.2)
    hreg hzero S hS hsize hjet
  intro η hη
  obtain ⟨el,hel,hl⟩:=hlead η hη
  refine ⟨min es el,by positivity,?_⟩
  intro ε hε he u hu hKu
  have hp:=hboot ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  let A:=scalarSearchOnlyOperator m T f G H r (ε • u)
  let P:=fcFiniteOperatorPath Q N (I ε u).2
  have hpath j (hj : j<N) : A j=P j := by
    dsimp only [P,fcFiniteOperatorPath]
    rw [dite_eq_left hj]
    dsimp only [I,scalarSearchOnlyInput]
    abel
  have hinit : G (ε • u)=ε • (Q u+(I ε u).1) := by
    dsimp only [I,scalarSearchOnlyInput]
    rw [add_sub_cancel,smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hout : G (scalarFunctionPoint m T f G r (ε • u) N)=
      ε • searchOnlyFiniteTerminal m Q N ((Q u,0)+I ε u) := by
    rw [←scalarSearchOnlyRun_gradient m hm T f G r (ε • u) N,hp.2 N le_rfl,
      methodRun_congr_prefix m A A P P _ N hpath hpath,hinit,
      methodRun_scalar m hh P P _ ε hε,scaleHistory_gradient]
    have heq : (Q u,0)+I ε u=(Q u+(I ε u).1,(I ε u).2) := by
      apply Prod.ext
      · rfl
      · exact zero_add _
    rw [heq]
    rfl
  rw [hout]
  exact hl ε hε (he.trans_le (min_le_right _ _)) u ⟨hu,hKu⟩

end
end krylov.Convergence
