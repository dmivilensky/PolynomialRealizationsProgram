import krylov.Nonlinear.RFCSCoordinateError
import krylov.Nonlinear.SelfConcordantLocal

/-!
Article: main_krylov, thm:RFCS, genuine self-concordant nonlinear cycle bound.
Use: Derive the actual metric-error inequality directly from original
physical differentiated gradient/Hessian data and the standard mixed
self-concordance inequality, with no supplied local constants or expansions.
Source: Nesterov18, Lemma 5.1.2, mixed differential formulation; actual
positive-root metric normalization, proved genuine nonlinear cubic transfer
and exact leading-coefficient preserving gradient/error comparison.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Correction
open scoped InnerProductSpace NNReal
variable {k : ℕ}

/-- Actual self-concordant gradient/Hessian data yield the genuine nonlinear RFC-S cycle metric-error estimate with the executed last relative probe factor and a uniform cubic remainder before every compact full-active reference family.
Use: Supply the original self-concordant single-cycle conclusion for actual finite-gradient RFC-S execution.
Article: main_krylov, thm:RFCS, genuine self-concordant nonlinear metric error.
Source: Nesterov18, Lemma 5.1.2, standard mixed self-concordance differential bound.
Proof: The original physical differential data derive both true canonical local control with constant term 2 and a real physical Hessian Lipschitz neighborhood. The constructed positive metric root supplies exact model compatibility. Apply the proved actual nonlinear error theorem on that derived physical neighborhood; its leading probe coefficient is unchanged.
-/
theorem compact_rfcs_selfConcordant_error_bound (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (r B Cp : ℝ) (hr : 0<r) (hB : 0<B) (hCp : 0<Cp)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hG : ∀ x∈ball 0 r, HasFDerivAt G (H x) x) (hD : ∀ x∈ball 0 r, HasFDerivAt H (D x) x)
    (hsc : ∀ x∈ball 0 r, ∀ u v w : EuclideanSpace ℝ (Fin (k+1)), |inner ℝ v (D x u w)|≤
      2*Real.sqrt (inner ℝ u (H x u))*Real.sqrt (inner ℝ v (H x v))*Real.sqrt (inner ℝ w (H x w))) :
    let T := metricCoordinates base hb
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) →
      (∀ i<k+1, 0<h i ∧ h i≤Cp*CG.length (cgOperator base) (cgOperator base u) i) →
      ‖T (rfcSFunctionPoint fullMemory G (ε • u) h (k+1))‖≤
      |1-h k/rfcSFunctionAlpha fullMemory G (ε • u) h k| *
        (ε*‖T (referenceStep (cgOperator base) (cgOperator base u) k)‖)^2+C*ε^3 := by
  let T := metricCoordinates base hb
  obtain ⟨ρ,r',hρ,_,hr',hr'r,hcan,hphysical⟩ := selfConcordant_metric_local_constants base hb H D r hr hH₀ hD hsc
  have hmodel (v : EuclideanSpace ℝ (Fin (k+1))) : T.symm (cgOperator base v)=T v := by
    simpa only [T,metricCoordinates_symm_apply,metricCoordinates_apply,cgOperator] using canonical_reference_action base hb v
  exact compact_rfcs_coordinate_error_bound base hb K hK hN hk T hmodel G H r' B Cp ρ hr' hB hCp hρ hG₀ hH₀
    hphysical (fun x hx => hG x (ball_subset_ball hr'r hx)) hcan

end
end krylov.Nonlinear
