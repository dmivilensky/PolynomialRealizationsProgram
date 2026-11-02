import krylov.Functions.NativeRFCJets
import krylov.Functions.RFCLeadingFields
import krylov.Functions.MetricFCInputJet

/-!
Article: main_krylov, lem:cycle-transfer, complete actual ordinary RFC inputs.
Use: give the genuine independent finite operator map its actual normalized
starting gradient and its actual search/correction Hessian averages, with a
proved uniform first jet. Source: genuine gradient FTC, native RFC bootstrap
and the true midpoint jets of the original third derivative.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- All actual normalized ordinary RFC operator inputs. Article: main_krylov,
lem:cycle-transfer. Both operator arrays are actual physical segment averages. -/
def nativeRFCInput (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E) (r ε : ℝ) (u : E) (N : ℕ) :
    E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E)) :=
  (ε⁻¹ • G (ε • u)-Q u,
    (fun i => rfcFunctionSearchOperator T f G H fullMemory r (ε • u) i.val-Q,
     fun i => rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) i.val-Q))

/-- The true complete first jet: gradient quadratic term, true search
midpoints and true next-node correction midpoints. Article: lem:cycle-transfer. -/
def nativeRFCReferenceInputJet (Q : E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E)
    (u : E) (N : ℕ) : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E)) :=
  ((1/2 : ℝ) • D u u,
    (fun i => D (rfcReferenceSearchMidpoint Q u i.val),
     fun i => D (fcQuadraticReferencePoint Q u (i.val+1))))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The exact actual RFC output dictionary, with no prescribed output jet.
Article: main_krylov, lem:cycle-transfer. -/
theorem NativeRFCPrefixBounds.input_terminal
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (hε : ε≠0) (N : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C N) :
    let I := nativeRFCInput T f G H Q r ε u N
    G (rfcFunctionPoint T f G fullMemory r (ε • u) N)=
      ε • rfcFiniteTerminal Q N (Q u+I.1,I.2) := by
  simpa only [nativeRFCInput, add_sub_cancel] using
    hp.normalized_terminal T f G H Q r u ε M D C hε N

/-- All actual normalized RFC inputs are O(ε), uniformly on the genuine
compact nondegenerate reference family. Article: lem:cycle-transfer.
The initial-gradient estimate reuses the already proved zero-query Taylor
bound; the two actual operator bounds are derived by the native RFC bootstrap. -/
theorem nativeRFCInput_bound (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0)
    (B : ℝ) (hB : 0<B) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : E, ‖u‖≤B → Q u∈K → ‖nativeRFCInput T f G H Q r ε u N‖≤C*ε := by
  obtain ⟨eg,Cg,heg,hCg,hg⟩ := metricFCInput_bound T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG B hB
  obtain ⟨ep,M,Da,Cp,hep,_,hDa,_,hp⟩ := nativeRFC_compact_prefix T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre B hB
  refine ⟨min eg ep,Cg+Da,lt_min heg hep,by positivity,?_⟩
  intro ε hε he u hu hKu
  have hb := hp ε hε (he.trans_le (min_le_right _ _)) u hu hKu
  change max ‖ε⁻¹ • G (ε • u)-Q u‖
    (max ‖fun i : Fin N => rfcFunctionSearchOperator T f G H fullMemory r (ε • u) i.val-Q‖
      ‖fun i : Fin N => rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) i.val-Q‖)≤(Cg+Da)*ε
  apply max_le
  · have hi := (norm_fst_le (metricFCInput T f G H Q r ε u 0)).trans
      ((hg ε hε (he.trans_le (min_le_left _ _)) u hu).2 0)
    exact hi.trans (by nlinarith only [hDa,hε])
  · apply max_le
    · apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤(Cg+Da)*ε)).mpr
      intro i
      exact (hb.2 i.val i.isLt).1.trans (by nlinarith only [hCg,hε])
    · apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤(Cg+Da)*ε)).mpr
      intro i
      exact (hb.2 i.val i.isLt).2.1.trans (by nlinarith only [hCg,hε])

/-- Every actual normalized RFC source coordinate has its genuine true-D
first jet, with a common radius on the whole compact family.
Article: main_krylov, lem:cycle-transfer. -/
theorem nativeRFCInput_reference_jet (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0)
    (B : ℝ) (hB : 0<B) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : E, ‖u‖≤B → Q u∈K →
        ‖nativeRFCInput T f G H Q r ε u N-ε • nativeRFCReferenceInputJet Q D u N‖≤η*ε := by
  intro η hη
  obtain ⟨eg,heg,hgj⟩ := metricFCInput_reference_jet T hT f G H Q D hD hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos 0 K hK (by intro g hg i hi; omega) B hB η hη
  obtain ⟨ea,hea,haj⟩ := nativeRFC_reference_operator_jets T hT f G H Q D hD hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre B hB η hη
  refine ⟨min eg ea,lt_min heg hea,?_⟩
  intro ε hε he u hu hKu
  change max ‖ε⁻¹ • G (ε • u)-Q u-ε • ((1/2 : ℝ) • D u u)‖
    (max ‖fun i : Fin N => rfcFunctionSearchOperator T f G H fullMemory r (ε • u) i.val-Q-
      ε • D (rfcReferenceSearchMidpoint Q u i.val)‖
      ‖fun i : Fin N => rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) i.val-Q-
      ε • D (fcQuadraticReferencePoint Q u (i.val+1))‖)≤η*ε
  apply max_le
  · exact (norm_fst_le (_ : E × (Fin 0 → E →L[ℝ] E))).trans
      (hgj ε hε (he.trans_le (min_le_left _ _)) u hu hKu)
  · apply max_le
    · apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤η*ε)).mpr
      intro i
      exact (haj ε hε (he.trans_le (min_le_right _ _)) u hu hKu i.val i.isLt).1
    · apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤η*ε)).mpr
      intro i
      exact (haj ε hε (he.trans_le (min_le_right _ _)) u hu hKu i.val i.isLt).2

end
end krylov.Functions
