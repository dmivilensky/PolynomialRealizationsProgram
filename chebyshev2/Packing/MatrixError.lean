import chebyshev2.Packing.Normalization

/-!
Article: chebyshev2, Theorem 2.3.
The gap 2 log N gives the printed matrix contribution 1/N.
Use: `chebyshev2.Packing.Representation.atomic_matrix_traceBound_logGap` feeds
`chebyshev2.Packing.packed_spectral_distance` (Theorem 2.3, equation (7), for the full fiber
including zero edges).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Packing
noncomputable section
open chebyshev2.Continuum Real
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {N : ℕ} {J : chebyshev2.Jacobi N} {gap : ℝ}

namespace Representation
variable (P : Representation J.green gap)

include P in
/--
Exact identity `sqrt (Jacobi.atomicWeight J i)*sqrt (Jacobi.atomicWeight J j) = sqrt (J.green i
i*J.green j j)/(N : ℝ)^2`.

Use: `chebyshev2.Packing.Representation.atomic_entry_error` rewrites with this identity to
establish the stated quantitative bound `|J.normalizedGreen i j-atomicMatrix
(Jacobi.atomicWeight J) P.point i j| ≤ exp (-gap)*sqrt (Jacobi.atomicWeight J i)*sqrt
(Jacobi.atomicWeight J j)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem sqrt_weight_product (_hN : 0 < N) (i j : Fin N) :
    sqrt (Jacobi.atomicWeight J i)*sqrt (Jacobi.atomicWeight J j) =
      sqrt (J.green i i*J.green j j)/(N : ℝ)^2 := by
  unfold Jacobi.atomicWeight
  rw [sqrt_div (P.diagonal_pos i).le,sqrt_div (P.diagonal_pos j).le,sqrt_sq (Nat.cast_nonneg N),sqrt_mul (P.diagonal_pos i).le]
  ring

/--
The stated quantitative bound `|J.normalizedGreen i j-atomicMatrix (Jacobi.atomicWeight J)
P.point i j| ≤ exp (-gap)*sqrt (Jacobi.atomicWeight J i)*sqrt (Jacobi.atomicWeight J j)`.

Use: `chebyshev2.Packing.Representation.atomic_matrix_traceBound` uses this bound to
establish the precise assertion is `TraceBound (Matrix.toEuclideanCLM (𝕜 := ℝ)
J.normalizedGreen - Matrix.toEuclideanCLM (𝕜 := ℝ) (atomicMatrix (Jacobi.atomicWeight J)
P.point)) (exp (-gap)*(N : ℝ))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Packing.Representation.sqrt_weight_product`
with the arguments shown in the proof.
-/
theorem atomic_entry_error (hN : 0 < N) (i j : Fin N) :
    |J.normalizedGreen i j-atomicMatrix (Jacobi.atomicWeight J) P.point i j| ≤
      exp (-gap)*sqrt (Jacobi.atomicWeight J i)*sqrt (Jacobi.atomicWeight J j) := by
  -- Use the identities/estimates `chebyshev2.Packing.Representation.sqrt_weight_product`
  -- with the arguments shown in the proof.
  have h := div_le_div_of_nonneg_right (P.error i j) (sq_nonneg (N : ℝ))
  change |((N : ℝ)^2)⁻¹*J.green i j -
    sqrt (Jacobi.atomicWeight J i)*sqrt (Jacobi.atomicWeight J j)*exp (-|P.point i-P.point j|)| ≤ _
  have hr : exp (-gap)*sqrt (Jacobi.atomicWeight J i)*sqrt (Jacobi.atomicWeight J j) =
      exp (-gap)*sqrt (J.green i i*J.green j j)/(N : ℝ)^2 := by
    rw [mul_assoc,P.sqrt_weight_product hN]
    ring
  rw [hr,P.sqrt_weight_product hN]
  calc
    _ = |J.green i j-sqrt (J.green i i*J.green j j)*exp (-|P.point i-P.point j|)|/(N : ℝ)^2 := by
      rw [show ((N : ℝ)^2)⁻¹*J.green i j - sqrt (J.green i i*J.green j j)/(N : ℝ)^2 *
          exp (-|P.point i-P.point j|) =
        (J.green i j-sqrt (J.green i i*J.green j j)*exp (-|P.point i-P.point j|))/(N : ℝ)^2 by ring]
      rw [abs_div,abs_of_nonneg (sq_nonneg (N : ℝ))]
    _ ≤ _ := h

/--
The precise assertion is `TraceBound (Matrix.toEuclideanCLM (𝕜 := ℝ) J.normalizedGreen -
Matrix.toEuclideanCLM (𝕜 := ℝ) (atomicMatrix (Jacobi.atomicWeight J) P.point)) (exp (-gap)*(N :
ℝ))`.

Use: `chebyshev2.Packing.Representation.atomic_matrix_traceBound_logGap` uses this identity
to establish `TraceBound (Matrix.toEuclideanCLM (𝕜 := ℝ)
J.normalizedGreen - Matrix.toEuclideanCLM (𝕜 := ℝ) (atomicMatrix (Jacobi.atomicWeight J)
P.point)) (1/(N : ℝ))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.TraceBound.mono`,
`chebyshev2.Continuum.matrix_traceBound`, `chebyshev2.Packing.Jacobi.atomicWeight_pos`
with the arguments shown in the proof.
-/
theorem atomic_matrix_traceBound (hN : 0 < N) (ht : J.Terminal) :
    TraceBound (Matrix.toEuclideanCLM (𝕜 := ℝ) J.normalizedGreen -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (atomicMatrix (Jacobi.atomicWeight J) P.point)) (exp (-gap)*(N : ℝ)) := by
  -- Use the identities/estimates `chebyshev2.Continuum.TraceBound.mono`,
  -- `chebyshev2.Continuum.matrix_traceBound`,
  -- `chebyshev2.Packing.Jacobi.atomicWeight_pos` with the arguments shown in the proof.
  rw [← map_sub]
  apply (matrix_traceBound _).mono
  have hw (i : Fin N) : 0 ≤ Jacobi.atomicWeight J i := (Jacobi.atomicWeight_pos J hN ht i).le
  have hm : (∑ i, Jacobi.atomicWeight J i) = 1 := by
    unfold Jacobi.atomicWeight
    rw [← Finset.sum_div]
    change Matrix.trace J.green/(N : ℝ)^2 = 1
    rw [J.green_trace hN ht,div_self (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hN.ne'))]
  have hs : (∑ i, sqrt (Jacobi.atomicWeight J i))^2 ≤ (N : ℝ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _i : Fin N => (1 : ℝ))
      (fun i => sqrt (Jacobi.atomicWeight J i))
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_fin,nsmul_eq_mul,mul_one,sq_sqrt (hw _),hm] using h
  calc
    (∑ i, ∑ j, |(J.normalizedGreen-atomicMatrix (Jacobi.atomicWeight J) P.point) i j|) ≤
        ∑ i, ∑ j, exp (-gap)*sqrt (Jacobi.atomicWeight J i)*sqrt (Jacobi.atomicWeight J j) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => P.atomic_entry_error hN i j))
    _ = exp (-gap)*(∑ i, sqrt (Jacobi.atomicWeight J i))^2 := by
      simp_rw [← Finset.mul_sum,← Finset.sum_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ exp (-gap)*(N : ℝ) := mul_le_mul_of_nonneg_left hs (exp_pos _).le

/--
The gap 2 log N gives the printed matrix contribution 1/N.

The precise assertion is `TraceBound (Matrix.toEuclideanCLM (𝕜 := ℝ) J.normalizedGreen -
Matrix.toEuclideanCLM (𝕜 := ℝ) (atomicMatrix (Jacobi.atomicWeight J) P.point)) (1/(N : ℝ))`.

Use: `chebyshev2.Packing.packed_spectral_distance` uses this identity to establish the
stated quantitative bound `(∑' j, |packedEigenvalue J hN ht j-finiteEigenvalue N j|) ≤ 2/sqrt
(N : ℝ)+1/(N : ℝ)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem atomic_matrix_traceBound_logGap (hN : 0 < N) (ht : J.Terminal)
    (P : Representation J.green (2*log (N : ℝ))) :
    TraceBound (Matrix.toEuclideanCLM (𝕜 := ℝ) J.normalizedGreen -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (atomicMatrix (Jacobi.atomicWeight J) P.point)) (1/(N : ℝ)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := P.atomic_matrix_traceBound hN ht
  have he : exp (-(2*log (N : ℝ)))*(N : ℝ) = 1/(N : ℝ) := by
    rw [show -(2*log (N : ℝ)) = -(log (N : ℝ)+log (N : ℝ)) by ring,
      exp_neg,exp_add,exp_log (Nat.cast_pos.mpr hN)]
    field_simp
  rwa [he] at h

end Representation
end
end chebyshev2.Packing
