import krylov.LinearAlgebra.MatrixCompression

/-!
Article: main_krylov, apA:lem:flagcd(d), the sharp observed cross-block norm.
Use: the commutator of an orthogonal old flag with a symmetric increment has
exactly the norm of its one cross block, rather than twice the increment norm.
Source: orthogonal Pythagoras, adjoint norm invariance and contractive projections.
-/

namespace krylov.LinearAlgebra
noncomputable section
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The norm of an orthogonal commutator is exactly the norm of its old/new cross block.
Use: retain the sharp constant one in the first-order observable-defect bound.
Article: main_krylov, apA:lem:flagcd(d), ‖[P,T]‖=‖PT(I−P)‖≤‖T‖.
Proof: its two projected outputs are the cross block and its negative adjoint;
Pythagoras bounds their combined action by the common block norm. Conversely,
projecting the commutator recovers the cross block without increasing its norm. -/
theorem orthogonal_commutator_norm (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) :
    ‖K.starProjection * T - T * K.starProjection‖ =
      ‖K.starProjection * T * Kᗮ.starProjection‖ := by
  let P := K.starProjection
  let Q := Kᗮ.starProjection
  let R := P*T*Q
  let L := Q*T*P
  have hadj : star R = L := by
    simp only [R, L, P, Q, star_mul, (isSelfAdjoint_starProjection K).star_eq,
      (isSelfAdjoint_starProjection Kᗮ).star_eq, hT.star_eq, mul_assoc]
  have hnorm : ‖L‖ = ‖R‖ := by
    rw [← hadj]
    exact ContinuousLinearMap.adjoint.norm_map R
  have hdec (v : E) : P v + Q v = v := K.starProjection_add_starProjection_orthogonal v
  have hpp (v : E) : P (P v) = P v :=
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem v)
  have hqq (v : E) : Q (Q v) = Q v :=
    Kᗮ.starProjection_eq_self_iff.mpr (Kᗮ.starProjection_apply_mem v)
  have hpq (v : E) : P (Q v) = 0 := by simp [P, Q, hpp]
  have hqp (v : E) : Q (P v) = 0 := by simp [P, Q, hpp]
  have hcomm (v : E) : (P*T-T*P) v = R (Q v)-L (P v) := by
    have he := congrArg (fun w => P (T w)) (hdec v)
    have hf := hdec (T (P v))
    simp only [map_add] at he
    simp only [R, L, sub_apply, mul_apply_eq_comp, hpp, hqq]
    calc
      _ = (P (T (P v))+P (T (Q v)))-(P (T (P v))+Q (T (P v))) := by rw [he, hf]
      _ = _ := by abel
  have hupper : ‖P*T-T*P‖ ≤ ‖R‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    have hp : P ((P*T-T*P) v) = R (Q v) := by
      rw [hcomm]
      simp only [R, L, mul_apply_eq_comp, map_sub, hpp, hpq, sub_zero]
    have hq : Q ((P*T-T*P) v) = -L (P v) := by
      rw [hcomm]
      simp only [R, L, mul_apply_eq_comp, map_sub, hqp, hqq, zero_sub]
    have hv := K.norm_sq_eq_add_norm_sq_starProjection v
    have hw := K.norm_sq_eq_add_norm_sq_starProjection ((P*T-T*P) v)
    change ‖(P*T-T*P) v‖^2 = ‖P ((P*T-T*P) v)‖^2 + ‖Q ((P*T-T*P) v)‖^2 at hw
    rw [hp, hq, norm_neg] at hw
    have hr := R.le_opNorm (Q v)
    have hl := L.le_opNorm (P v)
    rw [hnorm] at hl
    have hrs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hr
    have hls := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hl
    -- The two cross actions consume disjoint orthogonal input energies.
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    change ‖v‖^2 = ‖P v‖^2 + ‖Q v‖^2 at hv
    nlinarith [sq_nonneg ‖R‖]
  have hrecover : P*(P*T-T*P) = R := by
    apply ContinuousLinearMap.ext
    intro v
    have he := congrArg (fun w => P (T w)) (hdec v)
    simp only [map_add] at he
    simp only [mul_apply_eq_comp, sub_apply, map_sub, hpp, R]
    exact sub_eq_iff_eq_add.mpr (he.symm.trans (add_comm _ _))
  have hlower : ‖R‖ ≤ ‖P*T-T*P‖ := by
    rw [← hrecover]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) K.starProjection_norm_le)
  exact le_antisymm hupper hlower

/-- The observed cross block is contractive with respect to the original symmetric increment.
Use: a single old flag spends at most its own increment budget.
Article: main_krylov, apA:lem:flagcd(d), commutator budget.
Proof: use the exact cross-block norm and contractivity of both actual orthogonal projections. -/
theorem orthogonal_commutator_le (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) :
    ‖K.starProjection*T-T*K.starProjection‖ ≤ ‖T‖ := by
  rw [orthogonal_commutator_norm K T hT]
  -- Both exterior projections are contractive in the genuine Hilbert operator norm.
  calc
    _ ≤ ‖K.starProjection‖*‖T‖*‖Kᗮ.starProjection‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖T‖ := by
      calc
        _ ≤ ‖T‖*‖Kᗮ.starProjection‖ := mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_left (norm_nonneg T) K.starProjection_norm_le) (norm_nonneg _)
        _ ≤ ‖T‖ := mul_le_of_le_one_right (norm_nonneg T) Kᗮ.starProjection_norm_le

/-- Actual finite symmetric projection matrices have precisely their true cross-block commutator norm.
Use: the source's sharp observed-curvature assertion uses its original spectral matrix norm.
Article: main_krylov, apA:lem:flagcd(d), final sentence.
Proof: identify the matrix with its genuine range projection and apply the proved
Hilbert-space equality and contraction, through the isometric matrix/operator bridge. -/
theorem matrix_commutator_norm {n : ℕ} (P T : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsSymm) (hPid : P*P=P) (hT : T.IsSymm) :
    (‖P*T-T*P‖ = ‖P*T*(1-P)‖) ∧ ‖P*T-T*P‖ ≤ ‖T‖ := by
  -- Construct the actual range subspace before using its projection estimates.
  obtain ⟨K, hK, hp⟩ := matrix_projection_representation P hP hPid
  let : K.HasOrthogonalProjection := hK
  have ht : IsSelfAdjoint (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) T) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hT)
  have he := orthogonal_commutator_norm K _ ht
  have hb := orthogonal_commutator_le K _ ht
  rw [K.starProjection_orthogonal, ← hp] at he
  rw [← hp] at hb
  constructor
  · simpa only [Matrix.cstar_norm_def, map_sub, map_mul, map_one, ContinuousLinearMap.one_def] using he
  · simpa only [Matrix.cstar_norm_def, map_sub, map_mul] using hb

end
end krylov.LinearAlgebra
