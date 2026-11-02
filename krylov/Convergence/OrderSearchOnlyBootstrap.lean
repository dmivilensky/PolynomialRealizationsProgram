import krylov.Convergence.OrderSearchOnlyEmbedding

/-!
Article: main_krylov, thm:D, complete genuine search-only source bootstrap.
Use: primitive smooth CG-consistent homogeneous policies execute exactly
on their actual function secants, uniformly over a compact full reference
family. All query bounds, actual source smallness and positive search
parameters are derived from primitive function and policy data.
Source: actual sublevel localization, compact true policy domains and
causal scalar/averaged-Hessian record identification.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The actual scalar search-only program is the original raw protocol
on its true physical Hessian averages, with no supplied positivity,
query-enclosure or source-smallness assumptions.
Article: main_krylov, thm:D and lem:cycle-transfer. -/
theorem scalarSearchOnly_compact_bootstrap
    (m : ProbedMethod E) (hm : CorrectionFree m) (hc : CGConsistent m) (hh : m.Homogeneous)
    (T : E ≃L[ℝ] E) (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r →HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r →HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i<N,CG.gradient Q g i≠0)
    (hs : ∀ g∈K,SmoothProbedCycleAt m 2 Q g N)
    (B : ℝ) (hB : 0<B) :
    ∃ ep D : ℝ,0<ep ∧0<D ∧∀ ε : ℝ,0<ε →ε<ep →∀ u : E,‖u‖≤B →Q u∈K →
      ‖scalarSearchOnlyInput m T f G H Q r ε u N‖≤D*ε ∧
      ∀ i≤N,scalarFunctionRun m T f G r (ε • u) i=
        methodRun m (scalarSearchOnlyOperator m T f G H r (ε • u))
          (scalarSearchOnlyOperator m T f G H r (ε • u)) (G (ε • u)) i := by
  obtain ⟨δ,hδ,hvalid⟩:=compact_searchOnly_positive_lengths m hc Q hQ hpos N K hK hpre hs
  obtain ⟨es,D,hes,hD,hsource⟩:=scalarSearchOnlyInput_bound m hm T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG B hB
  refine ⟨min es (δ/(D+1)),D,by positivity,hD,?_⟩
  intro ε hε he u hu hKu
  have hinput:=hsource ε hε (he.trans_le (min_le_left _ _)) u hu
  have hsmall : ‖scalarSearchOnlyInput m T f G H Q r ε u N‖≤δ := by
    have he':=(lt_div_iff₀ (by positivity : 0<D+1)).mp (he.trans_le (min_le_right _ _))
    exact (hinput.2 N).trans (by nlinarith only [he',hε])
  refine ⟨hinput.2 N,?_⟩
  apply scalarSearchOnlyRun_eq_methodRun m hm T hT f G H hr hG₀ hHc₀ hLr hH hF hG
    (ε • u) hinput.1 N
  intro i hi
  let I:=scalarSearchOnlyInput m T f G H Q r ε u N
  let A:=scalarSearchOnlyOperator m T f G H r (ε • u)
  let P:=fcFiniteOperatorPath Q N I.2
  have hpath j (hj : j<N) : A j=P j := by
    dsimp only [P,fcFiniteOperatorPath]
    rw [dite_eq_left hj]
    dsimp only [I,scalarSearchOnlyInput]
    abel
  have hinit : G (ε • u)=ε • (Q u+I.1) := by
    dsimp only [I,scalarSearchOnlyInput]
    rw [add_sub_cancel,smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hrun : methodRun m A A (G (ε • u)) i=
      scaleHistory ε (methodRun m P P (Q u+I.1) i) := by
    rw [methodRun_congr_prefix m A A P P _ i (fun j hj=>hpath j (hj.trans hi)) (fun j hj=>hpath j (hj.trans hi)),
      hinit,methodRun_scalar m hh P P _ ε hε]
  change 0<lineLength (methodRun m A A (G (ε • u)) i).gradient
    (m.direction (methodRun m A A (G (ε • u)) i))
    (A i (m.direction (methodRun m A A (G (ε • u)) i)))
  rw [hrun,scaleHistory_gradient,(hh ε hε _).1,hpath i hi,map_smul,lineLength_scalar _ _ _ ε hε.ne']
  exact hvalid (Q u) hKu I.1 I.2 hsmall i hi

end
end krylov.Convergence
