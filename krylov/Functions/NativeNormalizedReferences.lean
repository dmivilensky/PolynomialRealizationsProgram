import krylov.Functions.NormalizedReferenceSource
import krylov.Functions.MetricFCLeadingSource
import krylov.Functions.NativeRFCFirstSource

/-!
Article: main_krylov, s7:N, actual normalized FC/RFC reference packaging.
Use: derive physical compactness solely from the paper's normalized observed
pair and primitive original scalar derivatives. All normalization scales come
from the actual first-query Taylor estimate before imposing CG nondegeneracy.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Literal s7:N gives one derived compact full physical reference family
for true native FC. Only the actual normalized pair is required to lie in
the original compact set. Article: main_krylov, thm:Htransfer. -/
theorem metricFC_normalized_reference_compact (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (N : ℕ) (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<N, CG.gradient z.1 z.2 i≠0) :
    ∃ ep : ℝ, 0<ep ∧ ∃ P : Set ((E →L[ℝ] E) × E), IsCompact P ∧
      (∀ z∈P, z.1.toLinearMap.IsSymmetric ∧
        (∀ v : E, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<N, CG.gradient z.1 z.2 i≠0) ∧
      ∀ ε : ℝ, 0<ε → ε<ep → ∀ u : E, ‖u‖=1 →
        normalizedReference (metricFCOperator T f G H fullMemory r (ε • u) 0) (G (ε • u))∈K →
        (metricFCOperator T f G H fullMemory r (ε • u) 0,ε⁻¹ • G (ε • u))∈P := by
  let A := fun (ε : ℝ) (u : E) => metricFCOperator T f G H fullMemory r (ε • u) 0
  let g := fun (ε : ℝ) (u : E) => ε⁻¹ • G (ε • u)
  obtain ⟨es,C,hes,hC,hsrc⟩ := metricFCInput_bound T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG 1 (by norm_num)
  have hsource : ∃ es C : ℝ, 0<es ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<es →
      ∀ u : E, ‖u‖=1 → ‖(A ε u-Q,g ε u-Q u)‖≤C*ε := by
    refine ⟨es,C,hes,hC,?_⟩
    intro ε hε he u hu
    have hs := (hsrc ε hε he u hu.le).2 1
    change max ‖A ε u-Q‖ ‖g ε u-Q u‖≤C*ε
    apply max_le
    · exact (norm_le_pi_norm (metricFCInput T f G H Q r ε u 1).2 (⟨0,by omega⟩ : Fin 1)).trans
        ((norm_snd_le _).trans hs)
    · exact (norm_fst_le _).trans hs
  obtain ⟨ep,hep,P,hP,hq,hcover⟩ := normalized_reference_source_compact Q hpos A g N K hK hquad hsource
  refine ⟨ep,hep,P,hP,hq,?_⟩
  intro ε hε he u hu hn
  apply hcover ε hε he u hu
  simpa only [g,normalizedReference_gradient_smul _ _ ε⁻¹ (inv_pos.mpr hε)] using hn

/-- Literal s7:N gives one derived compact full physical reference family
for true native ordinary RFC. No independent frozen-Hessian reference set
or unnormalized compactness premise remains. Article: thm:Htransfer. -/
theorem nativeRFC_normalized_reference_compact (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (N : ℕ) (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<N, CG.gradient z.1 z.2 i≠0) :
    ∃ ep : ℝ, 0<ep ∧ ∃ P : Set ((E →L[ℝ] E) × E), IsCompact P ∧
      (∀ z∈P, z.1.toLinearMap.IsSymmetric ∧
        (∀ v : E, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<N, CG.gradient z.1 z.2 i≠0) ∧
      ∀ ε : ℝ, 0<ε → ε<ep → ∀ u : E, ‖u‖=1 →
        normalizedReference (rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0) (G (ε • u))∈K →
        (rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0,ε⁻¹ • G (ε • u))∈P := by
  let A := fun (ε : ℝ) (u : E) => rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
  let g := fun (ε : ℝ) (u : E) => ε⁻¹ • G (ε • u)
  obtain ⟨es,C,hes,hC,hsrc⟩ := nativeRFC_first_reference_drift T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG 1 (by norm_num)
  have hsource : ∃ es C : ℝ, 0<es ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<es →
      ∀ u : E, ‖u‖=1 → ‖(A ε u-Q,g ε u-Q u)‖≤C*ε :=
    ⟨es,C,hes,hC,fun ε hε he u hu => hsrc ε hε he u hu.le⟩
  obtain ⟨ep,hep,P,hP,hq,hcover⟩ := normalized_reference_source_compact Q hpos A g N K hK hquad hsource
  refine ⟨ep,hep,P,hP,hq,?_⟩
  intro ε hε he u hu hn
  apply hcover ε hε he u hu
  simpa only [g,normalizedReference_gradient_smul _ _ ε⁻¹ (inv_pos.mpr hε)] using hn

end
end krylov.Functions
