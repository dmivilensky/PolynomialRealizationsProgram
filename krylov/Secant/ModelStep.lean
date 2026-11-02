import krylov.Secant.NormalizedModel
import krylov.Secant.CorrectionOrder

/-!
Article: main_krylov, apG:mss, actual model-step and oldest-pair estimates.
Use: apply the actual model error identities to the true physical inverse-model step.
Source: genuine nonsingular cancellation, exact oldest-dual rank-one norm and
the already proved distance/least-gain geometry.
-/

namespace krylov.Secant
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- The actual inverse model step equals its true model-minus-curvature action.
Use: exact algebraic identity before taking a local convergence or perturbation estimate.
Article: main_krylov, apG:err, x₊=J⁻¹(J−A*)x.
Proof: distribute the actual inverse action and cancel J⁻¹J. -/
theorem model_step_identity (J A : Matrix (Fin n) (Fin n) ℝ) (hJ : IsUnit J.det) (x : Fin n → ℝ) :
    x-J⁻¹*ᵥ (A*ᵥ x)=J⁻¹*ᵥ ((J-A)*ᵥ x) := by
  rw [sub_mulVec, mulVec_sub]
  simp only [mulVec_mulVec, nonsing_inv_mul _ hJ, one_mulVec]

/-- The true physical model step has precisely its printed genuine canonical action.
Use: the convergence estimate concerns actual physical iterates and actual metric roots.
Article: main_krylov, apG:err, x̂₊=Ĵ⁻¹(Ĵ−Â*)x̂.
Proof: identify the actual canonical inverse and cancel the adjacent metric roots
in its true curvature action; use the physical inverse-model identity for the base term. -/
theorem physical_model_step_identity (base J A : Matrix (Fin n) (Fin n) ℝ)
    (hbase : base.PosDef) (hJ : IsUnit J.det) (x : Fin n → ℝ) :
    metricRoot base*ᵥ (x-J⁻¹*ᵥ (A*ᵥ x)) =
      (relativeOperator base J)⁻¹*ᵥ
        ((relativeOperator base J-relativeOperator base A)*ᵥ (metricRoot base*ᵥ x)) := by
  -- Establish the actual canonical inverse domain before identifying either true step action.
  have hR := metricRoot_det_unit base hbase
  have hj : IsUnit (relativeOperator base J).det := by
    simp only [relativeOperator, det_mul, det_nonsing_inv]
    simpa only [Ring.inverse_eq_inv] using
      ((metricRoot_det_unit base hbase).inv.mul hJ).mul ((metricRoot_det_unit base hbase).inv)
  rw [← model_step_identity _ _ hj, relativeOperator_inv base J hbase]
  simp only [relativeOperator, mulVec_mulVec, mulVec_sub]
  have he : metricRoot base*J⁻¹*metricRoot base*((metricRoot base)⁻¹*A*(metricRoot base)⁻¹*metricRoot base)=
      metricRoot base*J⁻¹*A := by
    calc
      _ = metricRoot base*J⁻¹*(metricRoot base*(metricRoot base)⁻¹)*A*
          ((metricRoot base)⁻¹*metricRoot base) := by noncomm_ring
      _ = _ := by rw [mul_nonsing_inv _ hR, nonsing_inv_mul _ hR]; simp only [Matrix.mul_one]
  rw [he]
  simp only [Matrix.mul_assoc]

/-- The actual oldest-diagonal split has its exact dual-norm amplification bound.
Use: separates older diagonal contamination from the conditioned remaining data errors.
Article: main_krylov, apG:mss, refined model error estimate.
Proof: use the actual rank-one split; its actual spectral norm is the square
of the actual oldest dual norm, and the remainder has the proved inverse-congruence bound. -/
theorem oldest_model_error_bound (V X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    ‖inverseCongruence V X‖≤|X 0 0| * ‖oldestDual V‖^2+
      ‖V⁻¹‖^2*‖X-X 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)‖ := by
  -- Measure the actual dual outer product exactly before bounding the separate remainder.
  have he := oldest_model_split V X
  have hn : ‖vecMulVec (WithLp.ofLp (oldestDual V)) (WithLp.ofLp (oldestDual V))‖=‖oldestDual V‖^2 := by
    simpa only [chebyshev1.opNorm, WithLp.toLp_ofLp, pow_two] using
      spectral_norm_rankOne (WithLp.ofLp (oldestDual V)) (WithLp.ofLp (oldestDual V))
  calc
    _ ≤ ‖X 0 0 • vecMulVec (WithLp.ofLp (oldestDual V)) (WithLp.ofLp (oldestDual V))‖+
        ‖inverseCongruence V (X-X 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1))‖ := by
      conv_lhs => rw [he]
      exact norm_add_le _ _
    _ ≤ _ := by
      rw [norm_smul, hn, Real.norm_eq_abs]
      exact add_le_add le_rfl (inverseCongruence_norm V _)

/-- The actual oldest-diagonal amplification is exactly Δ⁻² and the remainder amplification is σ⁻².
Use: the full source model-error decomposition has its printed geometrical denominators.
Article: main_krylov, apG:mss and apG:err, oldest-pair conditioning.
Proof: substitute the proved genuine distance identity and actual least-gain definition
into the proved true dual-norm estimate. -/
theorem oldest_model_distance_bound (V X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hV : IsUnit V.det) :
    ‖inverseCongruence V X‖≤
      |X 0 0|/(Metric.infDist (euclideanColumn V 0) (newerColumnSpan V : Set _))^2+
      ‖X-X 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)‖/(leastGain V)^2 := by
  convert oldest_model_error_bound V X using 1
  simp only [oldest_column_distance V hV, leastGain, inv_pow, inv_inv, div_eq_mul_inv]
  ring

/-- The genuine normalized model step satisfies the complete refined oldest-pair error inequality.
Use: the actual step, actual normalized data correction and actual newest curvature enter directly.
Article: main_krylov, apG:err, displayed norm bound.
Proof: the exact inverse-model identity and two actual operator action bounds
reduce to the proved actual oldest-distance model-error bound plus the actual newest-curvature deviation. -/
theorem oldest_model_step_bound (V X A J : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hV : IsUnit V.det) (hmodel : J-1=inverseCongruence V X) (hJ : IsUnit J.det)
    (x : EuclideanSpace ℝ (Fin (n+1))) :
    ‖WithLp.toLp 2 (WithLp.ofLp x-J⁻¹*ᵥ (A*ᵥ WithLp.ofLp x))‖≤
      ‖J⁻¹‖*
        (|X 0 0|/(Metric.infDist (euclideanColumn V 0) (newerColumnSpan V : Set _))^2+
         ‖X-X 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)‖/(leastGain V)^2+‖A-1‖)*‖x‖ := by
  have hb := oldest_model_distance_bound V X hV
  have hm : ‖J-A‖≤‖inverseCongruence V X‖+‖A-1‖ := by
    have he : J-A=inverseCongruence V X-(A-1) := by rw [← hmodel]; abel
    rw [he]
    exact norm_sub_le _ _
  have ho := Matrix.l2_opNorm_mulVec J⁻¹ (WithLp.toLp 2 ((J-A)*ᵥ WithLp.ofLp x))
  have hi := Matrix.l2_opNorm_mulVec (J-A) x
  rw [model_step_identity J A hJ]
  -- Apply both true operator bounds before inserting the refined geometrical estimate.
  exact ho.trans ((mul_le_mul_of_nonneg_left
    (hi.trans (mul_le_mul_of_nonneg_right (hm.trans (add_le_add hb le_rfl)) (norm_nonneg _)))
      (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

end
end krylov.Secant
