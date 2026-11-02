import krylov.Secant.Metric
import Mathlib.Tactic.NoncommRing

/-!
Article: main_krylov, Appendix A, apA:lem:flagcd(c), canonical flag identities.
Use: change physical window coordinates by actual inverse congruences;
the old-flag projectors may be oblique before specialization to conjugate steps.
Source: the exact physical flag identities and nonsingular matrix cancellation.
-/

namespace krylov.Secant
noncomputable section
open Matrix Finset
open scoped Matrix BigOperators
variable {n : ℕ}

/-- Congruence of a window-coordinate form into the ambient canonical coordinates.
Use: transforms both observed defects and hidden model-error forms.
Article: main_krylov, apA:lem:flagcd(c), V^(−T) X V^(−1). -/
def inverseCongruence (V X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Vᵀ⁻¹ * X * V⁻¹

/-- The inverse of an invertible model congruence is its direct inverse-model congruence.
Use: square-window corrections act through the actual ambient inverse model.
Article: main_krylov, apA:galerkin(a), J⁻¹=UH⁻¹Uᵀ.
Proof: reverse the product and cancel the two inverse coordinate matrices. -/
theorem inverseCongruence_inv (U H : Matrix (Fin n) (Fin n) ℝ) (hU : IsUnit U.det) :
    (inverseCongruence U H)⁻¹ = U * H⁻¹ * Uᵀ := by
  have ht : IsUnit Uᵀ.det := by simpa only [det_transpose] using hU
  simp only [inverseCongruence, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hU,
    nonsing_inv_nonsing_inv _ ht, Matrix.mul_assoc]

/-- Whitening the physical compressed form through the actual metric-step matrix
gives precisely its ambient canonical relative form.
Use: discharges V=A¹/²S in the canonical flag theorem, without a hypothetical whitening map.
Article: main_krylov, apA:lem:flagcd(c).
Proof: expand the inverse product and cancel the two physical step matrices. -/
theorem inverseCongruence_metric (A X S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) :
    inverseCongruence (metricRoot A * S) (Sᵀ * X * S) = relativeOperator A X := by
  have ht : IsUnit Sᵀ.det := by simpa only [det_transpose] using hS
  simp only [inverseCongruence, transpose_mul, (metricRoot_isSymm A).eq, Matrix.mul_inv_rev]
  calc
    _ = (metricRoot A)⁻¹ * (Sᵀ⁻¹ * Sᵀ) * X * (S * S⁻¹) * (metricRoot A)⁻¹ := by
      noncomm_ring
    _ = _ := by rw [nonsing_inv_mul _ ht, mul_nonsing_inv _ hS]; simp [relativeOperator]

/-- The actual old-flag projector after an invertible change of step coordinates.
Use: applies to arbitrary full windows, including nonconjugate steps.
Article: main_krylov, apA:lem:flagcd(c), Π_l = V I_≤l V⁻¹. -/
def transportedFlag (V : Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := V * prefixProjection n l * V⁻¹

/-- Inverse congruence transports a flag compression to its oblique projector.
Use: each hidden-curvature summand has its exact canonical form.
Article: main_krylov, apA:lem:flagcd(c), compression transport.
Proof: expand the two projectors, cancel the coordinate matrices, and reassociate. -/
theorem inverseCongruence_compression (V X : Matrix (Fin n) (Fin n) ℝ)
    (hV : IsUnit V.det) (l : ℕ) :
    inverseCongruence V (prefixProjection n l * X * prefixProjection n l) =
      (transportedFlag V l)ᵀ * inverseCongruence V X * transportedFlag V l := by
  have ht : IsUnit Vᵀ.det := by simpa only [det_transpose] using hV
  unfold inverseCongruence transportedFlag
  rw [transpose_mul, transpose_mul, transpose_nonsing_inv, (prefixProjection_isSymm n l).eq]
  symm
  calc
    _ = Vᵀ⁻¹ * prefixProjection n l * (Vᵀ * Vᵀ⁻¹) * X *
        (V⁻¹ * V) * prefixProjection n l * V⁻¹ := by noncomm_ring
    _ = _ := by rw [mul_nonsing_inv _ ht, nonsing_inv_mul _ hV]; noncomm_ring

/-- Inverse congruence transports the observed commutator exactly.
Use: the asymmetric canonical formula is valid also for oblique flags.
Article: main_krylov, apA:lem:flagcd(c), Π_lᵀ Ê_l − Ê_l Π_l.
Proof: expand both terms and cancel the same coordinate matrices as for compression. -/
theorem inverseCongruence_commutator (V X : Matrix (Fin n) (Fin n) ℝ)
    (hV : IsUnit V.det) (l : ℕ) :
    inverseCongruence V (prefixProjection n l * X - X * prefixProjection n l) =
      (transportedFlag V l)ᵀ * inverseCongruence V X -
        inverseCongruence V X * transportedFlag V l := by
  -- Regroup the two inverse pairs before invoking exact nonsingular cancellation.
  have ht : IsUnit Vᵀ.det := by simpa only [det_transpose] using hV
  unfold inverseCongruence transportedFlag
  rw [transpose_mul, transpose_mul, transpose_nonsing_inv, (prefixProjection_isSymm n l).eq]
  symm
  calc
    _ = Vᵀ⁻¹ * prefixProjection n l * (Vᵀ * Vᵀ⁻¹) * X * V⁻¹ -
        Vᵀ⁻¹ * X * (V⁻¹ * V) * prefixProjection n l * V⁻¹ := by noncomm_ring
    _ = _ := by
      rw [mul_nonsing_inv _ ht, nonsing_inv_mul _ hV]
      noncomm_ring

/-- The full exact canonical flag identities for an arbitrary invertible coordinate matrix.
Use: instantiate V=A^(1/2)S for the physical canonical formulas.
Article: main_krylov, apA:lem:flagcd(c), both displayed canonical sums.
Proof: transport every summand of the already proved exact compressed identities. -/
theorem canonical_flag_identities (V : Matrix (Fin n) (Fin n) ℝ) (hV : IsUnit V.det)
    (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (hC : ∀ k, (C k).IsSymm) :
    (inverseCongruence V (C n - latest (observed C)) =
      ∑ l ∈ range n, (transportedFlag V l)ᵀ *
        inverseCongruence V (C (l + 1) - C l) * transportedFlag V l) ∧
    (inverseCongruence V (defect (observed C)) =
      ∑ l ∈ range (n - 1), ((transportedFlag V l)ᵀ *
        inverseCongruence V (C (l + 1) - C l) -
        inverseCongruence V (C (l + 1) - C l) * transportedFlag V l)) := by
  -- The coordinate change is linear on matrix-valued finite sums.
  constructor
  · rw [model_error_eq_sum_compressions C hC]
    simp only [inverseCongruence, Matrix.mul_sum, Matrix.sum_mul]
    exact sum_congr rfl fun l _ => inverseCongruence_compression V _ hV l
  · rw [defect_eq_sum_commutators C hC]
    simp only [inverseCongruence, Matrix.mul_sum, Matrix.sum_mul]
    exact sum_congr rfl fun l _ => inverseCongruence_commutator V _ hV l

/-- Compressing the actual ambient inverse-congruence model recovers its window form.
Use: identify the true physical model error before changing canonical coordinates.
Article: main_krylov, apA:lem:flagcd(c) and apG:mss.
Proof: cancel each nonsingular step matrix against its own inverse. -/
theorem compress_inverseCongruence (S H : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) : Sᵀ * inverseCongruence S H * S = H := by
  have ht : IsUnit Sᵀ.det := by simpa only [det_transpose] using hS
  simp only [inverseCongruence, ← Matrix.mul_assoc]
  rw [mul_nonsing_inv _ ht, Matrix.one_mul, Matrix.mul_assoc,
    nonsing_inv_mul _ hS, Matrix.mul_one]

/-- The canonical flag sums for the actual physical trajectory, metric root and MSS model.
Use: no abstract coordinate-change premise remains in the article's exact canonical identities.
Article: main_krylov, apA:lem:flagcd(c), both canonical formulas.
Proof: apply the exact flag identity to the physical compressed trajectory;
the genuine metric-step inverse congruence cancels S in every increment. -/
theorem physical_canonical_flag_identities (S base : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) (hbase : base.PosDef)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ k, (A k).IsSymm) :
    let V := metricRoot base * S
    let H := latest (Sᵀ * pairImages S A)
    let J := inverseCongruence S H
    (relativeOperator base (A n - J) =
      ∑ l ∈ range n, (transportedFlag V l)ᵀ * relativeOperator base (A (l + 1) - A l) *
        transportedFlag V l) ∧
    (inverseCongruence V (defect (Sᵀ * pairImages S A)) =
      ∑ l ∈ range (n - 1), ((transportedFlag V l)ᵀ *
        relativeOperator base (A (l + 1) - A l) -
        relativeOperator base (A (l + 1) - A l) * transportedFlag V l)) := by
  dsimp only
  have hV : IsUnit (metricRoot base * S).det := by
    rw [det_mul]
    exact (metricRoot_det_unit base hbase).mul hS
  have hc : ∀ k, (Sᵀ * A k * S).IsSymm := by
    intro k
    simp only [Matrix.IsSymm, transpose_mul, transpose_transpose, (hA k).eq, Matrix.mul_assoc]
  have h := canonical_flag_identities (metricRoot base * S) hV (fun k => Sᵀ * A k * S) hc
  -- The compressed trajectory's observed columns are the actual physical secants.
  rw [observed_compression S A] at h
  have he : Sᵀ * A n * S - latest (Sᵀ * pairImages S A) =
      Sᵀ * (A n - inverseCongruence S (latest (Sᵀ * pairImages S A))) * S := by
    rw [Matrix.mul_sub, Matrix.sub_mul, compress_inverseCongruence S _ hS]
  rw [he, inverseCongruence_metric _ _ _ hS] at h
  simpa only [← Matrix.mul_sub, ← Matrix.sub_mul, inverseCongruence_metric _ _ _ hS] using h

/-- Every transported old flag is an actual idempotent, even before conjugacy is imposed.
Use: distinguishes oblique flags from the orthogonal flags at a conjugate window.
Article: main_krylov, apA:lem:flagcd(c), Π_l²=Π_l.
Proof: cancel the coordinate inverse in the middle and square the diagonal indicator. -/
theorem transportedFlag_idempotent (V : Matrix (Fin n) (Fin n) ℝ) (hV : IsUnit V.det) (l : ℕ) :
    transportedFlag V l * transportedFlag V l = transportedFlag V l := by
  -- Squaring an old flag retains exactly the same coordinate indicators.
  have hp : prefixProjection n l * prefixProjection n l = prefixProjection n l := by
    simp only [prefixProjection, diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  unfold transportedFlag
  calc
    _ = V * prefixProjection n l * (V⁻¹ * V) * prefixProjection n l * V⁻¹ := by noncomm_ring
    _ = _ := by rw [nonsing_inv_mul _ hV, Matrix.mul_one, Matrix.mul_assoc V, hp]

/-- Conjugate columns make each actual transported old flag symmetric and hence orthogonal.
Use: the exact canonical commutator becomes the ordinary orthogonal commutator.
Article: main_krylov, apA:lem:flagcd(c), orthogonal projectors for conjugate steps.
Proof: the coordinate indicator commutes with the diagonal column Gram matrix;
cancel Vᵀ and V from the resulting equality of the two compressed flag transposes. -/
theorem transportedFlag_isSymm (V : Matrix (Fin n) (Fin n) ℝ) (hV : IsUnit V.det)
    (c : Fin n → ℝ) (hG : Vᵀ * V = diagonal c) (l : ℕ) :
    (transportedFlag V l).IsSymm := by
  have ht : IsUnit Vᵀ.det := by simpa only [det_transpose] using hV
  have hc : prefixProjection n l * (Vᵀ * V) = (Vᵀ * V) * prefixProjection n l := by
    simp only [hG, prefixProjection, diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _
  -- Cancel the full coordinate matrices only after using the Gram commutation.
  apply Matrix.mul_right_injective_of_inv Vᵀ⁻¹ Vᵀ (nonsing_inv_mul _ ht)
  apply Matrix.mul_left_injective_of_inv V V⁻¹ (mul_nonsing_inv _ hV)
  unfold transportedFlag
  rw [transpose_mul, transpose_mul, transpose_nonsing_inv, (prefixProjection_isSymm n l).eq]
  calc
    _ = (Vᵀ * Vᵀ⁻¹) * prefixProjection n l * (Vᵀ * V) := by noncomm_ring
    _ = (Vᵀ * V) * prefixProjection n l := by rw [mul_nonsing_inv _ ht, Matrix.one_mul, hc]
    _ = _ := by
      symm
      calc
        _ = (Vᵀ * V) * prefixProjection n l * (V⁻¹ * V) := by noncomm_ring
        _ = _ := by rw [nonsing_inv_mul _ hV, Matrix.mul_one]

/-- The actual metric-step matrix has exactly the physical A-Gram matrix.
Use: physical A-conjugacy discharges the diagonal-Gram hypothesis for orthogonal flags.
Article: main_krylov, apA:lem:flagcd(c), ΣᵀΣ=SᵀAS.
Proof: transpose the metric-step product and square the actual symmetric positive root. -/
theorem metric_step_gram (A S : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (metricRoot A * S)ᵀ * (metricRoot A * S) = Sᵀ * A * S := by
  rw [transpose_mul, (metricRoot_isSymm A).eq]
  calc
    _ = Sᵀ * (metricRoot A * metricRoot A) * S := by noncomm_ring
    _ = _ := by rw [metricRoot_square A hA]

end
end krylov.Secant
