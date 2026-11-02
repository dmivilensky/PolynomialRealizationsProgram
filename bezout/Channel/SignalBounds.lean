import bezout.Channel.Signal

/-!
Article: bezout, Appendix D, weighted endpoint and finite-bulk transfer bounds.
Use: rectangular physical channel matrices admit exact row-energy accounting;
adding bulk rows increases the squared operator norm by at most their HS energy.
Proof: temporal Cauchy--Schwarz, orthogonal coordinate masks and the true Euclidean
operator norm, without assumptions about experimental mode weights.
-/

namespace bezout.Channel
noncomputable section
open scoped BigOperators
variable {N : ℕ} {J : Type*} [Fintype J]

/-- Euclidean action of a rectangular temporal channel matrix. -/
def rectangularOperator (M : Matrix J (Fin N) ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ J :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

/-- The actual Euclidean operator norm of a rectangular channel matrix. -/
def rectangularNorm (M : Matrix J (Fin N) ℝ) : ℝ := ‖rectangularOperator M‖

/-- The squared Hilbert--Schmidt norm, with every actual spectral row retained. -/
def rectangularHsSq (M : Matrix J (Fin N) ℝ) : ℝ := ∑ j, ∑ s, M j s^2

/-- The actual matrix action in coordinates. -/
@[simp] theorem rectangularOperator_apply (M : Matrix J (Fin N) ℝ)
    (e : EuclideanSpace ℝ (Fin N)) (j : J) :
    rectangularOperator M e j=∑ s, M j s*e s := rfl

/-- Squared Hilbert--Schmidt energy is nonnegative. -/
theorem rectangularHsSq_nonneg (M : Matrix J (Fin N) ℝ) : 0≤rectangularHsSq M :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Temporal Cauchy--Schwarz bounds the actual channel action by all row energies. -/
theorem rectangular_action_sq_le (M : Matrix J (Fin N) ℝ)
    (e : EuclideanSpace ℝ (Fin N)) :
    ‖rectangularOperator M e‖^2≤rectangularHsSq M*‖e‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, rectangularOperator_apply]
  calc
    _ ≤ ∑ j, (∑ s, M j s^2)*(∑ s, e s^2) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M j) (fun s => e s))
    _ = _ := by
      rw [← Finset.sum_mul, EuclideanSpace.norm_sq_eq]
      simp only [rectangularHsSq, Real.norm_eq_abs, sq_abs]

/-- A quadratic bound on every actual action bounds the squared operator norm. -/
theorem rectangularNorm_sq_le (M : Matrix J (Fin N) ℝ) {C : ℝ} (hC : 0≤C)
    (hb : ∀ e : EuclideanSpace ℝ (Fin N), ‖rectangularOperator M e‖^2≤C*‖e‖^2) :
    rectangularNorm M^2≤C := by
  have hnorm : rectangularNorm M≤Real.sqrt C := by
    apply (rectangularOperator M).opNorm_le_bound (Real.sqrt_nonneg C)
    intro e
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hC]
    exact hb e
  have hz : 0≤rectangularNorm M := norm_nonneg _
  nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C]

/-- The operator gain never exceeds the squared Hilbert--Schmidt energy. -/
theorem rectangularNorm_sq_le_hsSq (M : Matrix J (Fin N) ℝ) :
    rectangularNorm M^2≤rectangularHsSq M :=
  rectangularNorm_sq_le M (rectangularHsSq_nonneg M) (rectangular_action_sq_le M)

variable [DecidableEq J]

/-- Retain exactly the spectral rows in a chosen finite signal block. -/
def rowMask (F : Finset J) (M : Matrix J (Fin N) ℝ) : Matrix J (Fin N) ℝ :=
  fun j s => if j∈F then M j s else 0

/-- A row mask acts as the orthogonal coordinate mask after the actual channel action. -/
@[simp] theorem rowMask_action (F : Finset J) (M : Matrix J (Fin N) ℝ)
    (e : EuclideanSpace ℝ (Fin N)) (j : J) :
    rectangularOperator (rowMask F M) e j=if j∈F then rectangularOperator M e j else 0 := by
  by_cases hj : j∈F <;> simp [rectangularOperator_apply, rowMask, hj]

/-- Endpoint and bulk coordinates contribute orthogonally to the actual squared output. -/
theorem rowMask_action_sq_split (F : Finset J) (M : Matrix J (Fin N) ℝ)
    (e : EuclideanSpace ℝ (Fin N)) :
    ‖rectangularOperator M e‖^2=
      ‖rectangularOperator (rowMask F M) e‖^2+‖rectangularOperator (rowMask Fᶜ M) e‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j∈F <;> simp [rowMask, hj]

/-- Squared HS energy splits exactly between endpoint and bulk rows. -/
theorem rowMask_hsSq_split (F : Finset J) (M : Matrix J (Fin N) ℝ) :
    rectangularHsSq M=rectangularHsSq (rowMask F M)+rectangularHsSq (rowMask Fᶜ M) := by
  unfold rectangularHsSq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j∈F <;> simp [rowMask, hj]

/-- Keeping only selected spectral rows cannot increase the operator norm. -/
theorem rowMask_norm_le (F : Finset J) (M : Matrix J (Fin N) ℝ) :
    rectangularNorm (rowMask F M)≤rectangularNorm M := by
  apply (rectangularOperator (rowMask F M)).opNorm_le_bound (norm_nonneg _)
  intro e
  have hs := rowMask_action_sq_split F M e
  have hn : ‖rectangularOperator (rowMask F M) e‖≤‖rectangularOperator M e‖ := by
    nlinarith [norm_nonneg (rectangularOperator (rowMask F M) e), norm_nonneg (rectangularOperator M e),
      sq_nonneg ‖rectangularOperator (rowMask Fᶜ M) e‖]
  exact hn.trans ((rectangularOperator M).le_opNorm e)

/-- Finite bulk rows add at most their HS energy to the squared operator gain.
Use: general symbolic endpoint-mass and asymptotic transfer comparisons. -/
theorem rowMask_norm_sq_sandwich (F : Finset J) (M : Matrix J (Fin N) ℝ) :
    rectangularNorm (rowMask F M)^2≤rectangularNorm M^2 ∧
    rectangularNorm M^2≤rectangularNorm (rowMask F M)^2+rectangularHsSq (rowMask Fᶜ M) := by
  refine ⟨(sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (rowMask_norm_le F M), ?_⟩
  apply rectangularNorm_sq_le M (add_nonneg (sq_nonneg _) (rectangularHsSq_nonneg _))
  intro e
  rw [rowMask_action_sq_split F M e]
  have he := (rectangularOperator (rowMask F M)).le_opNorm e
  have he2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr he
  rw [mul_pow] at he2
  have hb := rectangular_action_sq_le (rowMask Fᶜ M) e
  change _≤(‖rectangularOperator (rowMask F M)‖^2+_)*_ at ⊢
  nlinarith

end
end bezout.Channel
