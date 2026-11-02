import krylov.Stability.UniformFlags

/-!
Article: main_krylov, eq:weighted-flags and eq:weighted-flag-bound, uniform oblique flag bounds.
Use: derive the actual bound two on genuine normalized oblique flags and
propagate individual weighted actual column changes with dimension-only constants.
Source: the C-star Gram identity, the proved real Neumann inverse bound,
and the exact actual inverse-Gram/rank-one flag decomposition.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Secant
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
/-- The true normalized-column Gram norm equals the square of the actual spectral column-operator norm.
Use: Uniform column conditioning uses genuine Euclidean operator norms.
Article: main_krylov, eq:weighted-flag-bound.
Proof: Apply the actual matrix C-star identity with real transpose as adjoint. -/
theorem gram_norm_eq_sq (T : Matrix (Fin n) (Fin n) ℝ) : ‖Tᵀ*T‖=‖T‖*‖T‖ := by
  simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
    (CStarRing.norm_star_mul_self (x := T))
/-- Every true coordinate prefix projection has spectral norm at most one, including empty spaces.
Use: Bound actual old-column compressions without a nonempty-dimension premise.
Article: main_krylov, eq:weighted-flag-bound.
Proof: Its diagonal entries are zero or one; use the genuine diagonal spectral norm formula. -/
theorem prefix_norm_le (l : ℕ) : ‖prefixProjection n l‖≤(1 : ℝ) := by
  rw [prefixProjection,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  split_ifs <;> norm_num
/-- A true Gram deviation at most one half bounds the squared spectral column norm by three halves.
Use: Uniform oblique flag bounds require no physical step-length lower bound.
Article: main_krylov, eq:weighted-flag-bound.
Proof: Use the exact Gram norm identity and the triangle inequality around the actual identity, whose norm is at most one. -/
theorem gram_norm_bound (T : Matrix (Fin n) (Fin n) ℝ) (hG : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) :
    ‖T‖*‖T‖≤(3/2 : ℝ) := by
  have h₁ : ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖≤1 := by
    rw [Matrix.cstar_norm_def,map_one]
    exact ContinuousLinearMap.norm_id_le
  rw [← gram_norm_eq_sq]
  have ht := norm_add_le (Tᵀ*T-1) (1 : Matrix (Fin n) (Fin n) ℝ)
  rw [sub_add_cancel] at ht
  linarith
/-- Every actual square oblique flag is bounded by the true column/inverse conditioning product.
Use: Reduce flag norms to normalized-column conditioning.
Article: main_krylov, eq:weighted-flag-bound.
Proof: Bound its genuine three-factor product using the actual prefix norm at most one. -/
theorem transportedFlag_norm_product (T : Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    ‖transportedFlag T l‖≤‖T‖*‖T⁻¹‖ := by
  apply (norm_mul_le _ _).trans
  exact mul_le_mul_of_nonneg_right
    ((norm_mul_le _ _).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (prefix_norm_le l) (norm_nonneg T)))
    (norm_nonneg _)
/-- Every actual normalized-column oblique flag has spectral norm at most two when its true Gram deviation is at most one half.
Use: The uniform FC response proof has its printed flag bound discharged from actual Gram conditioning.
Article: main_krylov, eq:weighted-flag-bound.
Proof: The true Gram and inverse Gram bound the squared column and inverse norms. Their product is at most three; taking the nonnegative square root bounds the actual conditioning product by two. -/
theorem transportedFlag_norm_two (T : Matrix (Fin n) (Fin n) ℝ) (hG : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) (l : ℕ) :
    ‖transportedFlag T l‖≤2 := by
  -- Keep the actual inverse Gram and actual column Gram as a paired conditioning product.
  have ht := gram_norm_bound T hG
  have hi := (near_identity_inverse (Tᵀ*T) hG).2.1
  have hinv : ‖(Tᵀ*T)⁻¹‖=‖T⁻¹‖*‖T⁻¹‖ := by
    rw [Matrix.mul_inv_rev,← Matrix.transpose_nonsing_inv]
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CStarRing.norm_self_mul_star (x := T⁻¹))
  rw [hinv] at hi
  have hp := mul_le_mul ht hi (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num : (0 : ℝ)≤3/2)
  have hprod : ‖T‖*‖T⁻¹‖≤2 := by
    nlinarith [mul_nonneg (norm_nonneg T) (norm_nonneg T⁻¹)]
  exact ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (prefix_norm_le l) (norm_nonneg T)))
      (norm_nonneg _))).trans hprod

/-- The real transpose preserves the genuine spectral matrix norm.
Use: Bound true flag sandwiches in the source metric.
Article: main_krylov, eq:weighted-flag-bound.
Proof: Real transpose is the actual C-star adjoint, whose operator norm is unchanged. -/
theorem transpose_norm (T : Matrix (Fin n) (Fin n) ℝ) : ‖Tᵀ‖=‖T‖ := by
  simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using norm_star T
/-- A genuine old-column Gram-error sandwich is bounded by the squared true column norm times its actual middle error.
Use: The uniform flag bound separates the inverse-Gram error from individual physical column changes.
Article: main_krylov, eq:weighted-flag-bound.
Proof: Apply the actual prefix contraction and three genuine operator product bounds. -/
theorem prefix_sandwich_bound (T B : Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    ‖T*prefixProjection n l*B*Tᵀ‖≤(‖T‖*‖T‖)*‖B‖ := by
  -- Each true prefix contraction costs at most one in the genuine spectral norm.
  have hp : ‖T*prefixProjection n l‖≤‖T‖ :=
    (norm_mul_le _ _).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (prefix_norm_le l) (norm_nonneg T))
  calc
    _ ≤ (‖T*prefixProjection n l‖*‖B‖)*‖Tᵀ‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖T‖*‖B‖)*‖T‖ := by
      rw [transpose_norm]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- True normalized oblique flags have a uniform weighted bound from actual Gram error and individually weighted actual column changes.
Use: Weights stay paired with their own reference errors, so no smallest CG energy enters the resulting estimate.
Article: main_krylov, eq:weighted-flag-bound.
Proof: Use the exact actual inverse-Gram/rank-one split. Its Gram sandwich costs at most three times the true Gram deviation; sum each independently weighted actual column error and bound the number of old columns by the ambient dimension. -/
theorem transportedFlag_weighted_bound (T Q : Matrix (Fin n) (Fin n) ℝ) (l : ℕ)
    (hG : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) {r β : ℝ} (hr : 0≤r) (hβ : 0≤β)
    (hcol : ∀ j∈Finset.univ.filter (fun j : Fin n => j.val≤l),
      r*‖vecMulVec (fun i => T i j) (fun i => T i j)-vecMulVec (fun i => Q i j) (fun i => Q i j)‖≤β) :
    r*‖transportedFlag T l-Q*prefixProjection n l*Qᵀ‖≤3*r*‖Tᵀ*T-1‖+(n : ℝ)*β := by
  -- Bound the real inverse-Gram part separately, and retain each true column weight in the finite sum.
  let J := Finset.univ.filter (fun j : Fin n => j.val≤l)
  let D := fun j => vecMulVec (fun i => T i j) (fun i => T i j)-vecMulVec (fun i => Q i j) (fun i => Q i j)
  have hfirst : ‖T*prefixProjection n l*((Tᵀ*T)⁻¹-1)*Tᵀ‖≤3*‖Tᵀ*T-1‖ := by
    apply (prefix_sandwich_bound T _ l).trans
    have hm := mul_le_mul (gram_norm_bound T hG) (near_identity_inverse (Tᵀ*T) hG).2.2
      (norm_nonneg _) (by norm_num : (0 : ℝ)≤3/2)
    exact hm.trans_eq (by ring)
  have hsum : r*‖∑ j∈J, D j‖≤(n : ℝ)*β := by
    calc
      _ ≤ r*(∑ j∈J, ‖D j‖) := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
      _ = ∑ j∈J, r*‖D j‖ := Finset.mul_sum _ _ _
      _ ≤ ∑ _j∈J, β := Finset.sum_le_sum hcol
      _ ≤ (n : ℝ)*β := by
        have hcN : J.card≤n := by
          simpa only [J,Finset.card_univ,Fintype.card_fin] using
            (Finset.card_filter_le Finset.univ (fun j : Fin n => j.val≤l))
        have hc : (J.card : ℝ)≤n := by exact_mod_cast hcN
        simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right hc hβ
  rw [transportedFlag_gram_split T Q (column_unit_of_near_gram T hG) l]
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) hr).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hfirst hr])

end
end krylov.Stability
