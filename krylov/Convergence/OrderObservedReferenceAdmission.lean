import krylov.Convergence.OrderUnitReferenceAdmission
import krylov.Convergence.RestartedFC
import krylov.Convergence.RestartedRFCOrder

/-!
Article: main_krylov, thm:D and s7:N, genuine sharp-normalized admission.
Use: derive one compact full true-Hstar reference family for all canonical
unit directions admitted by the actual observed normalized first secant.
Every physical source drift and nonstagnation tube is derived from actual
native FC/RFC execution. Source: original normalized-reference compactness,
true first-segment Taylor estimates and positive-annulus CG homogeneity.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Literal actual s7:N implies compact full frozen-reference admission
at exactly the canonical unit scale printed in the cycle theorem.
Article: main_krylov, thm:D, FC. -/
theorem nativeFC_canonical_observed_admission
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt G (H z) z)
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0) :
    ∃ ep : ℝ,0<ep ∧∃ F : Set E,IsCompact F ∧(∀ g∈F,referenceAtomCount base hb g=k+1) ∧
      ∀ ε : ℝ,0<ε → ε<ep →∀ u : E,‖cgOperator (metricRoot base) u‖=1 →
        normalizedReference (metricFCOperator (metricCoordinates base hb) f G H fullMemory r (ε • u) 0)
          (G (ε • u))∈K →cgOperator base u∈F := by
  let T:=metricCoordinates base hb
  have hT:=metricCoordinates_inverse_symmetric base hb
  have hHc₀:=coordinateDerivative_metric_zero base hb H hH₀
  obtain ⟨es,hes,P,hP,hq,hcover⟩:=metricFC_normalized_reference_compact T hT f G H (cgOperator base)
    (cgOperator_positive base hb).2 hr hG₀ hH₀ hHc₀ hLr hH hF hG (k+1) K hK hquad
  obtain ⟨δ,hδ,F,hFc,hpre,hfreeze⟩:=compact_own_reference_frozen_tube (cgOperator base) (k+1) P hP hq
  obtain ⟨ed,D,hed,hD,hsource⟩:=metricFCInput_bound T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF hG 1 (by norm_num)
  let admission:=fun x : E=>normalizedReference (metricFCOperator T f G H fullMemory r x 0) (G x)∈K
  have hfull : ∀ g∈F,referenceAtomCount base hb g=k+1 :=
    fun g hg=>referenceAtomCount_eq_of_full_nonstagnation base hb g (hpre g hg)
  apply canonical_unit_reference_admission base hb admission (min es (min ed (δ/(D+1)))) (by positivity) F hFc hfull
  intro ε hε he u hu hn
  have hown:=hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn
  have hs:=(hsource ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu.le).2 1
  have hpair : ‖(metricFCOperator T f G H fullMemory r (ε • u) 0-cgOperator base,
      ε⁻¹ • G (ε • u)-cgOperator base u)‖≤D*ε := by
    rw [Prod.norm_def,max_le_iff]
    exact ⟨(norm_le_pi_norm (metricFCInput T f G H (cgOperator base) r ε u 1).2 ⟨0,by omega⟩).trans
      ((norm_snd_le _).trans hs),(norm_fst_le _).trans hs⟩
  have hsmall:=(lt_div_iff₀ (by positivity : 0<D+1)).mp
    (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  exact hfreeze _ _ _ hown (hpair.trans (by nlinarith only [hsmall,hε]))

/-- The same literal actual s7:N admission is derived for native RFC
without presuming a separate full frozen direction family.
Article: main_krylov, thm:D, RFC. -/
theorem nativeRFC_canonical_observed_admission
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt G (H z) z)
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0) :
    ∃ ep : ℝ,0<ep ∧∃ F : Set E,IsCompact F ∧(∀ g∈F,referenceAtomCount base hb g=k+1) ∧
      ∀ ε : ℝ,0<ε → ε<ep →∀ u : E,‖cgOperator (metricRoot base) u‖=1 →
        normalizedReference (rfcFunctionSearchOperator (metricCoordinates base hb) f G H fullMemory r (ε • u) 0)
          (G (ε • u))∈K →cgOperator base u∈F := by
  let T:=metricCoordinates base hb
  have hT:=metricCoordinates_inverse_symmetric base hb
  have hHc₀:=coordinateDerivative_metric_zero base hb H hH₀
  obtain ⟨es,hes,P,hP,hq,hcover⟩:=nativeRFC_normalized_reference_compact T hT f G H (cgOperator base)
    (cgOperator_positive base hb).2 hr hG₀ hH₀ hHc₀ hLr hH hF hG (k+1) K hK hquad
  obtain ⟨δ,hδ,F,hFc,hpre,hfreeze⟩:=compact_own_reference_frozen_tube (cgOperator base) (k+1) P hP hq
  obtain ⟨ed,D,hed,hD,hsource⟩:=nativeRFC_first_reference_drift T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF hG 1 (by norm_num)
  let admission:=fun x : E=>normalizedReference (rfcFunctionSearchOperator T f G H fullMemory r x 0) (G x)∈K
  have hfull : ∀ g∈F,referenceAtomCount base hb g=k+1 :=
    fun g hg=>referenceAtomCount_eq_of_full_nonstagnation base hb g (hpre g hg)
  apply canonical_unit_reference_admission base hb admission (min es (min ed (δ/(D+1)))) (by positivity) F hFc hfull
  intro ε hε he u hu hn
  have hown:=hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn
  have hs:=hsource ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu.le
  have hsmall:=(lt_div_iff₀ (by positivity : 0<D+1)).mp
    (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  exact hfreeze _ _ _ hown (hs.trans (by nlinarith only [hsmall,hε]))

end
end krylov.Convergence
