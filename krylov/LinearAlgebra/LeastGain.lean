import krylov.LinearAlgebra.OldestPair
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: main_krylov, apG:mss, the smallest gain and oldest-pair conditioning.
Use: define the smallest singular value through the actual inverse spectral norm
and prove its attained minimum characterization on the genuine unit sphere.
Source: compactness of a finite-dimensional unit sphere and the inverse action identity;
this is the standard variational characterization of the smallest singular value.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace Topology
variable {n : ℕ}

/-- The actual smallest gain of an invertible square matrix, in inverse-norm form.
Use: equals the attained minimum of its action on the actual Euclidean unit sphere.
Article: main_krylov, apG:mss, σ_min(Û).
Source: the standard inverse-norm characterization, justified by leastGain_isLeast below. -/
def leastGain (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ := ‖V⁻¹‖⁻¹

/-- The actual inverse spectral norm of an invertible nonempty matrix is strictly positive.
Use: every reciprocal conditioning and distance comparison has a justified positive denominator.
Article: main_krylov, apG:mss, σ>0.
Proof: a zero inverse would make its actual product with V zero instead of the identity. -/
theorem inverse_norm_pos (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hV : IsUnit V.det) :
    0<‖V⁻¹‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have he := nonsing_inv_mul V hV
  rw [hz, Matrix.zero_mul] at he
  exact zero_ne_one he

/-- The actual smallest gain bounds every genuine matrix-vector action from below.
Use: controls distances and inverse solves by the same actual conditioning constant.
Article: main_krylov, apG:mss, σ‖a‖≤‖Ûa‖.
Proof: apply the actual inverse norm to V a and cancel V⁻¹V. -/
theorem leastGain_action (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hV : IsUnit V.det)
    (a : EuclideanSpace ℝ (Fin (n+1))) :
    leastGain V*‖a‖≤‖WithLp.toLp 2 (V*ᵥ WithLp.ofLp a)‖ := by
  have he := Matrix.l2_opNorm_mulVec V⁻¹ (WithLp.toLp 2 (V*ᵥ WithLp.ofLp a))
  simp only [mulVec_mulVec, nonsing_inv_mul _ hV, one_mulVec] at he
  change ‖a‖≤‖V⁻¹‖*‖WithLp.toLp 2 (V*ᵥ WithLp.ofLp a)‖ at he
  rw [leastGain, ← div_eq_inv_mul, div_le_iff₀ (inverse_norm_pos V hV)]
  simpa only [mul_comm] using he

/-- The actual finite-dimensional operator norm is attained at a genuine Euclidean unit vector.
Use: constructs the minimizing singular direction, rather than assuming one.
Article: main_krylov, apG:mss, variational singular-value interpretation.
Source: mathlib compactness and maximum theorem on a finite-dimensional sphere.
Proof: take an actual maximum on the compact nonempty unit sphere and identify
its value with the operator norm using the unit-vector norm characterization. -/
theorem euclidean_operator_norm_attained
    (T : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    ∃ a, ‖a‖=1 ∧ ‖T a‖=‖T‖ := by
  -- Compactness produces a true maximizing unit vector; the norm characterization identifies its value.
  have hn : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨a, ha, hm⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1).exists_isMaxOn
    hn T.continuous.norm.continuousOn
  have han : ‖a‖=1 := mem_sphere_zero_iff_norm.mp ha
  refine ⟨a, han, le_antisymm ?_ ?_⟩
  · simpa only [han, mul_one] using T.le_opNorm a
  · exact ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun b hb => hm
      (mem_sphere_zero_iff_norm.mpr hb)

/-- The inverse-norm definition is exactly the attained smallest singular action of the actual matrix.
Use: the conditioning constant is the actual smallest singular value in its standard variational form.
Article: main_krylov, apG:mss, σ=σ_min(Û).
Proof: normalize an actual norm-attaining inverse image; its forward image has
the reciprocal inverse norm, while the proved inverse-action inequality bounds every unit input. -/
theorem leastGain_isLeast (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hV : IsUnit V.det) :
    IsLeast ((fun a : EuclideanSpace ℝ (Fin (n+1)) =>
      ‖WithLp.toLp 2 (V*ᵥ WithLp.ofLp a)‖) '' {a | ‖a‖=1}) (leastGain V) := by
  -- The forward image of a normalized inverse maximizer attains the reciprocal lower bound.
  let T := Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) V⁻¹
  obtain ⟨a, ha, ht⟩ := euclidean_operator_norm_attained T
  have hp := inverse_norm_pos V hV
  have htpos : 0<‖T a‖ := by simpa only [ht, T, Matrix.l2_opNorm_toEuclideanCLM] using hp
  let b := ‖T a‖⁻¹ • T a
  have hb : ‖b‖=1 := by
    simp only [b, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htpos.le), inv_mul_cancel₀ htpos.ne']
  have he : WithLp.toLp 2 (V*ᵥ WithLp.ofLp b)=‖T a‖⁻¹ • a := by
    change Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) V b=_
    simp only [b, map_smul, T, ← mul_apply_eq_comp, ← map_mul, mul_nonsing_inv _ hV, map_one,
      one_apply_eq_self]
  constructor
  · refine ⟨b, hb, ?_⟩
    change ‖WithLp.toLp 2 (V*ᵥ WithLp.ofLp b)‖=leastGain V
    rw [he, norm_smul, ha, mul_one, Real.norm_of_nonneg (inv_nonneg.mpr htpos.le), ht]
    rfl
  · rintro _ ⟨b, hb, rfl⟩
    change ‖b‖=1 at hb
    simpa only [hb, mul_one] using leastGain_action V hV b

/-- The actual oldest dual is bounded by the actual inverse spectral norm, including singular inputs.
Use: uniform column conditioning also bounds the varying oldest rank-one amplification.
Article: main_krylov, apG:mss, ‖b‖≤‖Û⁻¹‖.
Proof: apply the actual inverse transpose to the actual coordinate unit vector;
its norm is one and actual transposition preserves the spectral norm. -/
theorem oldestDual_norm_le_inverse (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    ‖oldestDual V‖≤‖V⁻¹‖ := by
  -- Compute the coordinate unit norm explicitly before applying the inverse-operator bound.
  have he := Matrix.l2_opNorm_mulVec Vᵀ⁻¹
    (WithLp.toLp 2 (Pi.single (0 : Fin (n+1)) (1 : ℝ) : Fin (n+1) → ℝ))
  change ‖oldestDual V‖≤‖Vᵀ⁻¹‖*‖WithLp.toLp 2
    (Pi.single (0 : Fin (n+1)) (1 : ℝ) : Fin (n+1) → ℝ)‖ at he
  have ht : ‖Vᵀ⁻¹‖=‖V⁻¹‖ := by
    rw [← transpose_nonsing_inv]
    simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose V⁻¹
  have hn : ‖WithLp.toLp 2 (Pi.single (0 : Fin (n+1)) (1 : ℝ) : Fin (n+1) → ℝ)‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simp
  simpa only [ht, hn, mul_one] using he

/-- The actual oldest-column distance is bounded below by the actual smallest singular value.
Use: the refined oldest-pair estimate is never worse than the uniform conditioning bound.
Article: main_krylov, apG:mss, Δ≥σ.
Proof: take positive reciprocals of the proved dual/inverse-norm comparison
and substitute the proved actual distance identity. -/
theorem oldest_distance_leastGain (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hV : IsUnit V.det) :
    leastGain V≤Metric.infDist (euclideanColumn V 0) (newerColumnSpan V : Set _) := by
  rw [oldest_column_distance V hV, leastGain]
  have hb : 0<‖oldestDual V‖ := norm_pos_iff.mpr (oldestDual_ne_zero V hV)
  exact (inv_le_inv₀ (inverse_norm_pos V hV) hb).mpr (oldestDual_norm_le_inverse V)

end
end krylov.LinearAlgebra
