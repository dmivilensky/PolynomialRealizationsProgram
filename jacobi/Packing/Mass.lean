import chebyshev2.Packing.MatrixError

/-!
Article: jacobi, Proposition 3.1.
The geometric Representation and its spreading density are reused verbatim from
chebyshev2. Only the mass-one estimates are generalized here. No prescribed
characteristic polynomial or irreducibility hypothesis is needed.
Use: the spreading and atomic error estimates below keep this actual mass.
-/

namespace jacobi.Packing
noncomputable section
open chebyshev2 chebyshev2.Continuum chebyshev2.Packing
open MeasureTheory Real Set
open scoped BigOperators

variable {N : ℕ} {J : Jacobi N} {gap : ℝ}

/-- The scaled resolvent trace, without the Chebyshev mass-one specialization.
Use: the spreading and atomic error estimates below keep this actual mass.
Article: jacobi, Proposition 3.1.
-/
def mass (J : Jacobi N) : ℝ := Matrix.trace J.green / (N : ℝ)^2

/-- Spreading preserves the scaled trace for every geometric representation.
Use: substitutes the actual mass into the transport estimate.
Article: jacobi, Proposition 3.1.
Proof: each cell has mass dᵢ/N²; sum its diagonal contributions. -/
theorem density_mass (P : Representation J.green gap) (hN : 0 < N) :
    (∫ x, P.density hN x) = mass J := by
  rw [Representation.density, Blocks.closed_mass]
  simp_rw [P.blocks_weight hN]
  unfold chebyshev2.Packing.Jacobi.atomicWeight mass
  rw [← Finset.sum_div]
  rfl

/-- A nonempty represented matrix has strictly positive scaled trace.
Use: makes the separation parameter and its square root well-defined.
Article: jacobi, Proposition 3.1.
Proof: all diagonal entries of a representation are positive. -/
theorem mass_pos (P : Representation J.green gap) (hN : 0 < N) : 0 < mass J := by
  apply div_pos _ (pow_pos (Nat.cast_pos.mpr hN) 2)
  exact Finset.sum_pos' (fun i _ => (P.diagonal_pos i).le)
    ⟨⟨0, hN⟩, Finset.mem_univ _, P.diagonal_pos _⟩

/-- The spreading error for arbitrary mass is 2√(μ/N).
Use: the first of the two spectral errors in the full Packing theorem.
Article: jacobi, Proposition 3.1.
Proof: reuse the existing transport bound and the cost 1/(2N). -/
theorem density_atomic_traceBound (P : Representation J.green gap) (hN : 0 < N) :
    TraceBound (densityOperator (P.density hN) -
      atomicOperator (chebyshev2.Packing.Jacobi.atomicWeight J) P.point)
      (2 * sqrt (mass J / (N : ℝ))) := by
  -- Keep the actual trace mass in the transport estimate and use the existing cell cost bound.
  have h := (P.blocks hN).density_atomic_transport P.point
  simp_rw [P.blocks_weight hN] at h
  have hm : (∫ x, (P.blocks hN).closedDensity x) = mass J := density_mass P hN
  rw [hm] at h
  apply h.mono
  apply mul_le_mul_of_nonneg_left (sqrt_le_sqrt ?_) (by norm_num)
  calc
    2 * mass J * (∫ z, |z.1-z.2| ∂(P.blocks hN).coupling P.point) ≤
        2 * mass J * (1 / (2 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (P.coupling_cost_bound hN)
        (mul_nonneg (by norm_num) (mass_pos P hN).le)
    _ = mass J / (N : ℝ) := by ring

/-- The atomic weights have total mass μ rather than one.
Use: finite Cauchy--Schwarz controls interactions between different blocks.
Article: jacobi, Proposition 3.1.
Proof: atomic weights are precisely the scaled Green diagonal. -/
theorem atomic_mass :
    (∑ i : Fin N, chebyshev2.Packing.Jacobi.atomicWeight J i) = mass J := by
  unfold chebyshev2.Packing.Jacobi.atomicWeight mass
  rw [← Finset.sum_div]
  rfl

/-- Separating irreducible blocks gives an atomic matrix error e⁻ᵍNμ.
Use: choose the gap to make this at most the spreading error.
Article: jacobi, Proposition 3.1.
Proof: sum the existing entry error and apply finite Cauchy--Schwarz. -/
theorem atomic_matrix_traceBound (P : Representation J.green gap) (hN : 0 < N) :
    TraceBound (Matrix.toEuclideanCLM (𝕜 := ℝ) J.normalizedGreen -
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        (atomicMatrix (chebyshev2.Packing.Jacobi.atomicWeight J) P.point))
      (exp (-gap) * (N : ℝ) * mass J) := by
  -- Sum the entry errors and bound the squared sum of square-root weights by finite Cauchy--Schwarz.
  rw [← map_sub]
  apply (matrix_traceBound _).mono
  let w := chebyshev2.Packing.Jacobi.atomicWeight J
  have hw (i : Fin N) : 0 ≤ w i := div_nonneg (P.diagonal_pos i).le (sq_nonneg _)
  have hm : (∑ i, w i) = mass J := atomic_mass
  have hs : (∑ i, sqrt (w i))^2 ≤ (N : ℝ) * mass J := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _i : Fin N => (1 : ℝ))
      (fun i => sqrt (w i))
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      mul_one, sq_sqrt (hw _), hm] using h
  calc
    (∑ i, ∑ j, |(J.normalizedGreen - atomicMatrix w P.point) i j|) ≤
        ∑ i, ∑ j, exp (-gap) * sqrt (w i) * sqrt (w j) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => P.atomic_entry_error hN i j))
    _ = exp (-gap) * (∑ i, sqrt (w i))^2 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ exp (-gap) * ((N : ℝ) * mass J) :=
      mul_le_mul_of_nonneg_left hs (exp_pos _).le
    _ = _ := by ring

end
end jacobi.Packing
