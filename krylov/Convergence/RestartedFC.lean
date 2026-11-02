import krylov.Functions.NativeRFCFPhysicalTransfer
import krylov.Functions.NativeNormalizedReferences
import krylov.Functions.OwnReferenceTube
import krylov.Convergence.RecurrenceOrder

/-!
Article: main_krylov, thm:D, actual restarted full-conjugacy cycles.
Use: derive the genuine quadratic cycle error from the original scalar
executor and literal normalized observed-reference compactness, before
turning the true recursively restarted points into an R-order statement.
Source: actual finite native FC/reference comparison and quadratic CG
termination; no output bound or frozen compact direction set is assumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Nonlinear krylov.Functions
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- Actual full-memory FC cycle points with fresh memory at every restart.
Article: main_krylov, thm:D. -/
def fcRestartedPoints {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (N : ℕ) (x₀ : E) : ℕ → E
  | 0=>x₀
  | c+1=>metricFCPoint T f G fullMemory r (fcRestartedPoints T f G r N x₀ c) N

/-- Genuine scalar FC has compact-uniform quadratic cycle error around
actual full-active frozen references. Article: main_krylov, thm:D. -/
theorem nativeFC_error_quadratic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i<k+1,CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∃ ep C : ℝ,0<ep ∧ 0<C ∧ ∀ ε : ℝ,0<ε → ε<ep → ∀ u,‖u‖≤R → cgOperator base u∈K →
      ‖T (metricFCPoint T f G fullMemory r (ε • u) (k+1))‖≤C*ε^2 := by
  obtain ⟨ep,C,hep,hC,hcomp⟩ := metricFCPoint_reference_points T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF hG (cgOperator_positive base hb).1 (cgOperator_positive base hb).2
    (k+1) K hK hpre R hR
  refine ⟨ep,‖T.toContinuousLinearMap‖*C+1,hep,by positivity,?_⟩
  intro ε hε he u hu hKu
  have hx := hcomp ε hε he u hu hKu (k+1) le_rfl
  rw [fcQuadraticReferencePoint_full_zero base hb u,smul_zero,sub_zero] at hx
  exact (T.toContinuousLinearMap.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans (by nlinarith only [sq_nonneg ε]))

/-- The original normalized observed-reference assumption s7:N suffices
for the true FC quadratic cycle bound. Frozen reference admission follows
from real first-query Taylor bounds and open nonstagnation.
Article: main_krylov, thm:D and s7:N. -/
theorem nativeFC_error_normalized
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) × EuclideanSpace ℝ (Fin (k+1))))
    (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<k+1,CG.gradient z.1 z.2 i≠0) :
    ∃ ep C : ℝ,0<ep ∧ 0<C ∧ ∀ ε : ℝ,0<ε → ε<ep → ∀ u,‖u‖=1 →
      normalizedReference (metricFCOperator T f G H fullMemory r (ε • u) 0) (G (ε • u))∈K →
      ‖T (metricFCPoint T f G fullMemory r (ε • u) (k+1))‖≤C*ε^2 := by
  obtain ⟨es,hes,P,hP,hq,hcover⟩ := metricFC_normalized_reference_compact T hT f G H (cgOperator base)
    (cgOperator_positive base hb).2 hr hG₀ hH₀ hHc₀ hLr hH hF hG (k+1) K hK hquad
  obtain ⟨δ,hδ,F,hFc,hpre,hfreeze⟩ := compact_own_reference_frozen_tube (cgOperator base) (k+1) P hP hq
  obtain ⟨ed,D,hed,hD,hsource⟩ := metricFCInput_bound T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF hG 1 (by norm_num)
  obtain ⟨ec,C,hec,hC,hcycle⟩ := nativeFC_error_quadratic base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG F hFc hpre 1 (by norm_num)
  refine ⟨min es (min ed (min ec (δ/(D+1)))),C,by positivity,hC,?_⟩
  intro ε hε he u hu hn
  have hown := hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn
  have hs := (hsource ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu.le).2 1
  have hpair : ‖(metricFCOperator T f G H fullMemory r (ε • u) 0-cgOperator base,
      ε⁻¹ • G (ε • u)-cgOperator base u)‖≤D*ε := by
    rw [Prod.norm_def,max_le_iff]
    exact ⟨(norm_le_pi_norm (metricFCInput T f G H (cgOperator base) r ε u 1).2 ⟨0,by omega⟩).trans
      ((norm_snd_le _).trans hs),(norm_fst_le _).trans hs⟩
  have hsmall := (lt_div_iff₀ (by positivity : 0<D+1)).mp
    (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hfrozen := hfreeze _ _ _ hown (hpair.trans (by nlinarith only [hsmall,hε]))
  exact hcycle ε hε (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    u hu.le hfrozen

end
end krylov.Convergence
