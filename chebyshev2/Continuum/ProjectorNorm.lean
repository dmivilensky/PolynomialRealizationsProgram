import chebyshev2.Continuum.NuclearNorm

/-!
Article: chebyshev2, Proposition 3.
Lemma 4(i), the printed projector trace-norm formula for the exponential feature family.
Use: `chebyshev2.Continuum.nuclearNorm_rankOne` feeds
`chebyshev2.Continuum.traceClassFeature_norm` (trace Class Feature norm).
Proof chain: `chebyshev2.Comparison.Profile.signed_determinant_comparison` — chebyshev2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace chebyshev2.Continuum
noncomputable section
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Exact nuclear norm of every rank-one map, including zero vectors.

Exact identity `nuclearNorm (InnerProductSpace.rankOne ℝ a b) = ENNReal.ofReal (‖a‖ * ‖b‖)`.

Use: `chebyshev2.Continuum.traceClassFeature_norm` rewrites with this identity to establish
exact identity `‖traceClassFeature x‖ = 1`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Separate `a = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem nuclearNorm_rankOne (a b : E) :
    nuclearNorm (InnerProductSpace.rankOne ℝ a b) = ENNReal.ofReal (‖a‖ * ‖b‖) := by
  -- Separate `a = 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply le_antisymm (nuclearNorm_le_of_traceBound (traceBound_rankOne a b))
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hua : ‖‖a‖⁻¹ • a‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hna]
  have hub : ‖‖b‖⁻¹ • b‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hnb]
  let u : Fin 1 → E := fun _ => ‖a‖⁻¹ • a
  let v : Fin 1 → E := fun _ => ‖b‖⁻¹ • b
  have hu : Orthonormal ℝ u := orthonormal_subsingleton_iff.mpr (fun _ => hua)
  have hv : Orthonormal ℝ v := orthonormal_subsingleton_iff.mpr (fun _ => hub)
  have he : (∑ i, inner ℝ (u i) ((InnerProductSpace.rankOne ℝ a b) (v i))) = ‖a‖ * ‖b‖ := by
    simp only [Fin.sum_univ_one, u, v, InnerProductSpace.rankOne_apply,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  rw [nuclearNorm]
  apply le_iSup_of_le 1
  apply le_iSup_of_le u
  apply le_iSup_of_le v
  apply le_iSup_of_le hu
  apply le_iSup_of_le hv
  rw [he, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

/--
The precise assertion is `Orthonormal ℝ ![‖a‖⁻¹ • a, ‖b‖⁻¹ • b]`.

Use: `chebyshev2.Continuum.nuclearNorm_half_cross` uses this assertion to establish exact
identity `nuclearNorm ((1/2 : ℝ) • (InnerProductSpace.rankOne ℝ a b + InnerProductSpace.rankOne
ℝ b a)) = ENNReal.ofReal (‖a‖ * ‖b‖)`.

Article: chebyshev2, Proposition 3.

Proof: Check each member of the finite index type; no case is omitted.
-/
private theorem normalized_pair_orthonormal {a b : E} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : inner ℝ a b = 0) :
    Orthonormal ℝ ![‖a‖⁻¹ • a, ‖b‖⁻¹ • b] := by
  -- Check each member of the finite index type; no case is omitted.
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hba : inner ℝ b a = 0 := by rwa [real_inner_comm]
  constructor
  · intro i
    fin_cases i
    · change ‖‖a‖⁻¹ • a‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hna]
    · change ‖‖b‖⁻¹ • b‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hnb]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change inner ℝ (‖a‖⁻¹ • a) (‖b‖⁻¹ • b) = 0
      rw [real_inner_smul_left, real_inner_smul_right, hab, mul_zero, mul_zero]
    · change inner ℝ (‖b‖⁻¹ • b) (‖a‖⁻¹ • a) = 0
      rw [real_inner_smul_left, real_inner_smul_right, hba, mul_zero, mul_zero]
    · exact (hij rfl).elim

/--
The symmetric off-diagonal rank-two operator has nuclear norm equal to the product of the two
orthogonal vectors' norms. A swapped pair of finite frames attains the dual supremum; no
spectral certificate is required.

Exact identity `nuclearNorm ((1/2 : ℝ) • (InnerProductSpace.rankOne ℝ a b +
InnerProductSpace.rankOne ℝ b a)) = ENNReal.ofReal (‖a‖ * ‖b‖)`.

Use: `chebyshev2.Continuum.nuclearNorm_projector_sub` rewrites with this identity to
establish exact identity `nuclearNorm (InnerProductSpace.rankOne ℝ v v -
InnerProductSpace.rankOne ℝ w w) = ENNReal.ofReal (2 * Real.sqrt (1 - (inner ℝ v w)^2))`.

Article: chebyshev2, Proposition 3.

Proof: Separate `a = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem nuclearNorm_half_cross {a b : E} (hab : inner ℝ a b = 0) :
    nuclearNorm ((1/2 : ℝ) • (InnerProductSpace.rankOne ℝ a b +
      InnerProductSpace.rankOne ℝ b a)) = ENNReal.ofReal (‖a‖ * ‖b‖) := by
  -- Separate `a = 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let T := (1/2 : ℝ) • (InnerProductSpace.rankOne ℝ a b + InnerProductSpace.rankOne ℝ b a)
  have hupper : nuclearNorm T ≤ ENNReal.ofReal (‖a‖ * ‖b‖) := by
    apply nuclearNorm_le_of_traceBound
    convert ((traceBound_rankOne a b).add (traceBound_rankOne b a)).smul (1/2) using 1
    simp only [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    ring
  apply le_antisymm hupper
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  let u : Fin 2 → E := ![‖a‖⁻¹ • a, ‖b‖⁻¹ • b]
  let v : Fin 2 → E := ![‖b‖⁻¹ • b, ‖a‖⁻¹ • a]
  have hu : Orthonormal ℝ u := normalized_pair_orthonormal ha hb hab
  have hv : Orthonormal ℝ v := normalized_pair_orthonormal hb ha (by rwa [real_inner_comm])
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hba : inner ℝ b a = 0 := by rwa [real_inner_comm]
  have he : (∑ i, inner ℝ (u i) (T (v i))) = ‖a‖ * ‖b‖ := by
    simp only [Fin.sum_univ_two, u, v, T, Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_apply, add_apply, InnerProductSpace.rankOne_apply, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hab, hba]
    field_simp
    ring
  rw [nuclearNorm]
  apply le_iSup_of_le 2
  apply le_iSup_of_le u
  apply le_iSup_of_le v
  apply le_iSup_of_le hu
  apply le_iSup_of_le hv
  rw [he, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

/--
Exact trace norm of the difference of two unit-vector projectors, including coincident and
opposite vectors.

Exact identity `nuclearNorm (InnerProductSpace.rankOne ℝ v v - InnerProductSpace.rankOne ℝ w w)
= ENNReal.ofReal (2 * Real.sqrt (1 - (inner ℝ v w)^2))`.

Use: `chebyshev2.Continuum.featureProjection_nuclearNorm_sub` rewrites with this identity
to establish the identity `nuclearNorm (featureProjection x-featureProjection y) =
ENNReal.ofReal (2 * Real.sqrt (1-Real.exp (-2*|x-y|)))`.

Article: chebyshev2, Proposition 3.

Proof: Use the identities/estimates `chebyshev2.Continuum.nuclearNorm_half_cross` with the
arguments shown in the proof.
-/
theorem nuclearNorm_projector_sub {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    nuclearNorm (InnerProductSpace.rankOne ℝ v v - InnerProductSpace.rankOne ℝ w w) =
      ENNReal.ofReal (2 * Real.sqrt (1 - (inner ℝ v w)^2)) := by
  -- Use the identities/estimates `chebyshev2.Continuum.nuclearNorm_half_cross` with the
  -- arguments shown in the proof.
  have hab : inner ℝ (v+w) (v-w) = 0 := by
    simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm w v, hv, hw]
    ring
  have he : InnerProductSpace.rankOne ℝ v v - InnerProductSpace.rankOne ℝ w w =
      (1/2 : ℝ) • (InnerProductSpace.rankOne ℝ (v+w) (v-w) +
        InnerProductSpace.rankOne ℝ (v-w) (v+w)) := by
    ext z
    simp only [sub_apply, smul_apply,
      add_apply, InnerProductSpace.rankOne_apply,
      inner_add_left, inner_sub_left, smul_add, smul_sub, add_smul, sub_smul, smul_smul]
    module
  rw [he, nuclearNorm_half_cross hab]
  have hp : (‖v+w‖ * ‖v-w‖)^2 = 4 * (1-(inner ℝ v w)^2) := by
    rw [mul_pow, norm_add_sq_real, norm_sub_sq_real, hv, hw]
    ring
  have hn : 0 ≤ 1-(inner ℝ v w)^2 := by nlinarith [sq_nonneg (‖v+w‖ * ‖v-w‖)]
  congr 1
  nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (1-(inner ℝ v w)^2),
    mul_nonneg (norm_nonneg (v+w)) (norm_nonneg (v-w))]

/--
Lemma 4(i), the printed projector trace-norm formula for the exponential feature family.

Exact identity `nuclearNorm (featureProjection x-featureProjection y) = ENNReal.ofReal (2 *
Real.sqrt (1-Real.exp (-2*|x-y|)))`.

Use: `chebyshev2.Continuum.traceClassFeature_norm_sub` rewrites with this identity to
establish exact identity `‖traceClassFeature x-traceClassFeature y‖ = 2*sqrt (1-exp
(-2*|x-y|))`.

Article: chebyshev2, Proposition 3.

Proof: Use the identities/estimates `chebyshev2.Continuum.nuclearNorm_projector_sub`,
`chebyshev2.Continuum.feature_norm`, `chebyshev2.Continuum.feature_inner` with the
arguments shown in the proof.
-/
theorem featureProjection_nuclearNorm_sub (x y : ℝ) :
    nuclearNorm (featureProjection x-featureProjection y) =
      ENNReal.ofReal (2 * Real.sqrt (1-Real.exp (-2*|x-y|))) := by
  -- Use the identities/estimates `chebyshev2.Continuum.nuclearNorm_projector_sub`,
  -- `chebyshev2.Continuum.feature_norm`, `chebyshev2.Continuum.feature_inner` with the
  -- arguments shown in the proof.
  rw [featureProjection, featureProjection,
    nuclearNorm_projector_sub (feature_norm x) (feature_norm y), feature_inner]
  congr 4
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end
end chebyshev2.Continuum
