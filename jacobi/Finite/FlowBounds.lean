import jacobi.Finite.FlowDerivatives

/-!
Dimension-uniform differential estimates for the actual resolvent flow.
Entrywise Green positivity controls commutator products; the positive
spectral calculus bounds the square and cube diagonals by the fixed trace.
Use: FlowTaylor integrates these bounds and controls the true energy
remainder at the explicit descent time.
Article: jacobi, Proposition 5.5, Equation (5.12).
Article role: the spectral trace bounds, paired energy derivative and acceleration estimate.
-/
namespace jacobi.Finite
noncomputable section
open Matrix Real
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (S : Nodes (n+1))

/-- The conserved trace in the flow's dimension-scaled time units.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowMass : ℝ := flowScale (n+1)*flowTrace S

/-- The squared-dimension scale is strictly positive for every nonempty chain.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowScale_pos (N : ℕ) (hN : 0<N) : 0<flowScale N := by
  unfold flowScale
  positivity

/-- The conserved scaled trace is positive.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowMass_pos : 0<flowMass S :=
  mul_pos (flowScale_pos (n+1) (by omega)) (flowTrace_pos S)

/-- Absolute generator entries are bounded by the scaled positive Green
entries. Zero diagonal entries satisfy the same bound.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGenerator_abs_le (w : WeightSimplex (n+1)) (t : ℝ) (i j : Fin (n+1)) :
    |flowGenerator S w t i j|≤flowScale (n+1)*flowGreen S w t i j := by
  rw [flowGenerator_sign,abs_mul,abs_mul,abs_of_pos (flowScale_pos _ (by omega)),
    abs_of_pos (flowGreen_pos S w t i j)]
  have h := mul_le_mul_of_nonneg_left (flowSign_abs_le i j)
    (flowScale_pos (n+1) (by omega)).le
  simpa only [mul_one] using mul_le_mul_of_nonneg_right h (flowGreen_pos S w t i j).le

/-- The entrywise Green velocity is bounded by twice the scaled square
of the same positive Green matrix.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGreenVelocity_abs_le (w : WeightSimplex (n+1)) (t : ℝ) (i j : Fin (n+1)) :
    |flowGreenVelocity S w t i j|≤2*flowScale (n+1)*(flowGreen S w t*flowGreen S w t) i j := by
  unfold flowGreenVelocity
  rw [Matrix.sub_apply,Matrix.mul_apply,Matrix.mul_apply,← Finset.sum_sub_distrib]
  calc
    _≤∑ k,|flowGenerator S w t i k*flowGreen S w t k j-
        flowGreen S w t i k*flowGenerator S w t k j| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ k,2*flowScale (n+1)*flowGreen S w t i k*flowGreen S w t k j := by
      apply Finset.sum_le_sum
      intro k _
      calc
        _≤|flowGenerator S w t i k*flowGreen S w t k j|+
            |flowGreen S w t i k*flowGenerator S w t k j| := abs_sub _ _
        _=|flowGenerator S w t i k| *flowGreen S w t k j+
            flowGreen S w t i k*|flowGenerator S w t k j| := by
          rw [abs_mul,abs_mul,abs_of_pos (flowGreen_pos S w t k j),
            abs_of_pos (flowGreen_pos S w t i k)]
        _≤(flowScale (n+1)*flowGreen S w t i k)*flowGreen S w t k j+
            flowGreen S w t i k*(flowScale (n+1)*flowGreen S w t k j) :=
          add_le_add
            (mul_le_mul_of_nonneg_right (flowGenerator_abs_le S w t i k) (flowGreen_pos S w t k j).le)
            (mul_le_mul_of_nonneg_left (flowGenerator_abs_le S w t k j) (flowGreen_pos S w t i k).le)
        _=_ := by ring
    _=_ := by rw [Matrix.mul_apply,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring

/-- The diagonal sum of squared Green entries is precisely the square
matrix diagonal, using symmetry of the actual inverse.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGreen_row_square (w : WeightSimplex (n+1)) (t : ℝ) (i : Fin (n+1)) :
    (∑ j,(flowGreen S w t i j)^2)=(flowGreen S w t*flowGreen S w t) i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [flowGreen_symmetric S w t j i]
  ring

/-- The signed-square diagonal velocity is controlled by twice the
conserved scaled trace times the original positive diagonal.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowDiagonalVelocity_abs_le (w : WeightSimplex (n+1)) (t : ℝ) (i : Fin (n+1)) :
    |flowDiagonalVelocity S w t i|≤2*flowMass S*flowGreen S w t i i := by
  have hk := flowScale_pos (n+1) (by omega)
  unfold flowDiagonalVelocity
  rw [abs_mul,abs_of_pos (mul_pos (by norm_num) hk)]
  calc
    _≤2*flowScale (n+1)*(∑ j,|flowSign i j*(flowGreen S w t i j)^2|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _≤2*flowScale (n+1)*(∑ j,(flowGreen S w t i j)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_of_nonneg (sq_nonneg (flowGreen S w t i j))]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (flowSign_abs_le i j) (sq_nonneg _)
    _≤2*flowScale (n+1)*(flowTrace S*flowGreen S w t i i) := by
      rw [flowGreen_row_square]
      exact mul_le_mul_of_nonneg_left (flowGreen_square_diag_le S w t i) (by positivity)
    _=_ := by unfold flowMass; ring

/-- The actual second diagonal derivative is controlled by eight times
the squared conserved scaled trace times the original diagonal.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowDiagonalAcceleration_abs_le (w : WeightSimplex (n+1)) (t : ℝ) (i : Fin (n+1)) :
    |flowDiagonalAcceleration S w t i|≤8*(flowMass S)^2*flowGreen S w t i i := by
  have hk := flowScale_pos (n+1) (by omega)
  unfold flowDiagonalAcceleration
  rw [abs_mul,abs_of_pos (mul_pos (by norm_num) hk)]
  calc
    _≤4*flowScale (n+1)*∑ j,|flowSign i j*flowGreen S w t i j*flowGreenVelocity S w t i j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _≤4*flowScale (n+1)*∑ j,flowGreen S w t i j*
        (2*flowScale (n+1)*(flowGreen S w t*flowGreen S w t) i j) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_mul,abs_of_pos (flowGreen_pos S w t i j)]
      calc
        _≤flowGreen S w t i j*|flowGreenVelocity S w t i j| := by
          have h := mul_le_mul_of_nonneg_right (flowSign_abs_le i j) (flowGreen_pos S w t i j).le
          exact (mul_le_mul_of_nonneg_right h (abs_nonneg _)).trans_eq (by ring)
        _≤_ := mul_le_mul_of_nonneg_left (flowGreenVelocity_abs_le S w t i j)
          (flowGreen_pos S w t i j).le
    _=8*(flowScale (n+1))^2*(flowGreen S w t*flowGreen S w t*flowGreen S w t) i i := by
      rw [Matrix.mul_apply]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_apply]
      simp_rw [flowGreen_symmetric S w t _ i]
      ring
    _≤8*(flowScale (n+1))^2*((flowTrace S)^2*flowGreen S w t i i) :=
      mul_le_mul_of_nonneg_left (flowGreen_cube_diag_le S w t i) (by positivity)
    _=_ := by unfold flowMass; ring

/-- The true first energy derivative is bounded by four times the
conserved scaled trace times the true energy.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowEnergyVelocity_abs_le (w : WeightSimplex (n+1)) (t : ℝ) :
    |flowEnergyVelocity S w t|≤4*flowMass S*flowEnergy S w t := by
  unfold flowEnergyVelocity
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _≤2*∑ i,|flowGreen S w t i i*flowDiagonalVelocity S w t i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _≤2*∑ i,flowGreen S w t i i*(2*flowMass S*flowGreen S w t i i) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_pos (flowGreen_pos S w t i i)]
      exact mul_le_mul_of_nonneg_left (flowDiagonalVelocity_abs_le S w t i)
        (flowGreen_pos S w t i i).le
    _=_ := by
      unfold flowEnergy
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The true second energy derivative is bounded by twenty-four times
the squared conserved scaled trace times the true energy.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowEnergyAcceleration_abs_le (w : WeightSimplex (n+1)) (t : ℝ) :
    |flowEnergyAcceleration S w t|≤24*(flowMass S)^2*flowEnergy S w t := by
  unfold flowEnergyAcceleration
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _≤2*∑ i,|(flowDiagonalVelocity S w t i)^2+
        flowGreen S w t i i*flowDiagonalAcceleration S w t i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _≤2*∑ i,12*(flowMass S)^2*(flowGreen S w t i i)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i _
      have h1 := flowDiagonalVelocity_abs_le S w t i
      have h2 := flowDiagonalAcceleration_abs_le S w t i
      have hd := flowGreen_pos S w t i i
      have hm := flowMass_pos S
      have hsq := sq_le_sq₀ (abs_nonneg (flowDiagonalVelocity S w t i)) (by positivity) |>.mpr h1
      calc
        _≤|(flowDiagonalVelocity S w t i)^2|+
            |flowGreen S w t i i*flowDiagonalAcceleration S w t i| := abs_add_le _ _
        _≤(2*flowMass S*flowGreen S w t i i)^2+
            flowGreen S w t i i*(8*(flowMass S)^2*flowGreen S w t i i) := by
          rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_pos hd]
          rw [sq_abs] at hsq
          exact add_le_add hsq (mul_le_mul_of_nonneg_left h2 hd.le)
        _=_ := by ring
    _=_ := by
      unfold flowEnergy
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end
end jacobi.Finite
