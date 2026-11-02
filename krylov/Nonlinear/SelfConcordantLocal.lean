import krylov.Nonlinear.MetricCoordinates
import krylov.Nonlinear.SelfConcordantCoordinates
import krylov.Nonlinear.SelfConcordantHessian
import krylov.Nonlinear.CoordinateLipschitz

/-!
Article: main_krylov, thm:RFCS, actual self-concordant physical/canonical neighborhoods.
Use: Derive both the actual identity-normalized local constant 2+C R and a
genuine physical Hessian Lipschitz neighborhood from the original physical
mixed self-concordance data and actual differentiated Hessian.
Source: Nesterov18, Lemma 5.1.2, mixed differential bound, exact genuine
coordinate derivative/congruence transport and actual positive metric roots.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric krylov.Reference
open scoped InnerProductSpace NNReal
variable {n : ℕ}

/-- Actual physical mixed self-concordant Hessian data give one genuine canonical neighborhood with local Lipschitz constant 2+10000R and a real physical Lipschitz neighborhood under a self-adjoint metric coordinate inverse.
Use: Supply the real local constants for both the physical nonlinear executor and the sharp canonical probe comparison from the same original function.
Article: main_krylov, thm:RFCS, actual self-concordant function neighborhoods.
Source: Nesterov18, Lemma 5.1.2, original mixed differential inequality.
Proof: Choose a true canonical ball mapped inside the original physical domain. Transport the actual Hessian derivative and mixed inequality, derive the identity-normalized local bound, then reconstruct the physical Hessian and pull back its true Lipschitz constant.
-/
theorem coordinate_selfConcordant_local_constants {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (hT : T.symm.toContinuousLinearMap.toLinearMap.IsSymmetric)
    (H : E → E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    (r : ℝ) (hr : 0<r) (h₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    (hD : ∀ x∈ball 0 r, HasFDerivAt H (D x) x)
    (hsc : ∀ x∈ball 0 r, ∀ u v w : E, |inner ℝ v (D x u w)|≤
      2*Real.sqrt (inner ℝ u (H x u))*Real.sqrt (inner ℝ v (H x v))*Real.sqrt (inner ℝ w (H x w))) :
    ∃ ρ r' : ℝ, 0<ρ ∧ ρ≤1 ∧ 0<r' ∧ r'≤r ∧
      (∀ R : ℝ, 0<R → R≤ρ → LipschitzOnWith (Real.toNNReal (2+10000*R)) (coordinateDerivative T H) (ball 0 R)) ∧
      LipschitzOnWith (‖T.toContinuousLinearMap‖₊^3*Real.toNNReal (2+10000*ρ)) H (ball 0 r') := by
  let r₀ := r/(‖T.symm.toContinuousLinearMap‖+1)
  have hr₀ : 0<r₀ := div_pos hr (by positivity)
  have hmap {y : E} (hy : y∈ball 0 r₀) : T.symm y∈ball 0 r := by
    rw [mem_ball_zero_iff] at hy ⊢
    have hb' := T.symm.toContinuousLinearMap.le_opNorm y
    simp only [ContinuousLinearEquiv.coe_coe] at hb'
    have hy' := (lt_div_iff₀ (by positivity : 0<‖T.symm.toContinuousLinearMap‖+1)).mp hy
    nlinarith [norm_nonneg y]
  have hd y (hy : y∈ball 0 r₀) : HasFDerivAt (coordinateDerivative T H) (coordinateHessianVariation T D y) y :=
    coordinateDerivative_hasFDerivAt T H D y (hD _ (hmap hy))
  have hc y (hy : y∈ball 0 r₀) := coordinate_mixed_selfConcordance T
    hT H D y (hsc _ (hmap hy))
  obtain ⟨ρ,hρ,_,hρ1,hcan⟩ := selfConcordant_mixed_local_hessian_lipschitz (coordinateDerivative T H)
    (coordinateHessianVariation T D) r₀ hr₀ h₀ hd hc
  let r' := min r (ρ/(‖T.toContinuousLinearMap‖+1))
  have hr' : 0<r' := lt_min hr (div_pos hρ (by positivity))
  have hRmap : ball (0 : E) r'⊆T ⁻¹' ball 0 ρ := by
    intro x hx
    simp only [Set.mem_preimage]
    rw [mem_ball_zero_iff]
    have hx' := mem_ball_zero_iff.mp hx
    have hxr : ‖x‖<ρ/(‖T.toContinuousLinearMap‖+1) := hx'.trans_le (min_le_right _ _)
    have hxt := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖+1)).mp hxr
    have hn := T.toContinuousLinearMap.le_opNorm x
    simp only [ContinuousLinearEquiv.coe_coe] at hn
    nlinarith [norm_nonneg x]
  exact ⟨ρ,r',hρ,hρ1,hr',min_le_left _ _,hcan,
    (coordinateDerivative_lipschitz_pullback T H (hcan ρ hρ le_rfl)).mono hRmap⟩

/-- The actual positive-root coordinates of the genuine minimizer Hessian derive the canonical self-concordant constant 2+10000R and a genuine physical Hessian Lipschitz neighborhood directly from the original physical data.
Use: Instantiate the coordinate calculus in the source prescribed metric without assuming a canonical function model or a physical Hessian Lipschitz bound.
Article: main_krylov, thm:RFCS, actual self-concordant function neighborhoods.
Source: Nesterov18, Lemma 5.1.2, original mixed differential inequality.
Proof: Use the constructed true metric equivalence, its proved symmetric inverse and exact normalization of the actual minimizer Hessian in the genuine coordinate local-constant theorem.
-/
theorem selfConcordant_metric_local_constants (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hr : 0<r) (h₀ : H 0=cgOperator base)
    (hD : ∀ x∈ball 0 r, HasFDerivAt H (D x) x)
    (hsc : ∀ x∈ball 0 r, ∀ u v w : EuclideanSpace ℝ (Fin n), |inner ℝ v (D x u w)|≤
      2*Real.sqrt (inner ℝ u (H x u))*Real.sqrt (inner ℝ v (H x v))*Real.sqrt (inner ℝ w (H x w))) :
    let T := metricCoordinates base hb
    ∃ ρ r' : ℝ, 0<ρ ∧ ρ≤1 ∧ 0<r' ∧ r'≤r ∧
      (∀ R : ℝ, 0<R → R≤ρ → LipschitzOnWith (Real.toNNReal (2+10000*R)) (coordinateDerivative T H) (ball 0 R)) ∧
      LipschitzOnWith (‖T.toContinuousLinearMap‖₊^3*Real.toNNReal (2+10000*ρ)) H (ball 0 r') := by
  exact coordinate_selfConcordant_local_constants (metricCoordinates base hb)
    (metricCoordinates_inverse_symmetric base hb) H D r hr (coordinateDerivative_metric_zero base hb H h₀) hD hsc

end
end krylov.Nonlinear
