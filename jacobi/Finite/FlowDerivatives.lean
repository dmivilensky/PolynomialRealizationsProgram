import jacobi.Finite.FlowSpectralBounds

/-!
Exact diagonal and energy derivatives of the actual resolvent flow.
The diagonal velocity is a signed sum of squared Green entries. Its next
derivative and the first two energy derivatives are finite sums of the
actual Green entries and their already proved commutator derivatives.
Use: FlowBounds bounds these explicit sums by the conserved trace.
Article: jacobi, Proposition 5.5, Equation (5.12).
Article role: the spectral trace bounds, paired energy derivative and acceleration estimate.
-/
namespace jacobi.Finite
noncomputable section
open Matrix Real
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (S : Nodes (n+1))

/-- Inverse squared dimension, the fixed time normalization of the flow.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowScale (N : ℕ) : ℝ := 1/(N:ℝ)^2

/-- Physical index orientation of the strictly lower-minus-upper part.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowSign {N : ℕ} (i j : Fin N) : ℝ :=
  if j < i then 1 else if i < j then -1 else 0

/-- The orientation multiplier has absolute value at most one.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowSign_abs_le {N : ℕ} (i j : Fin N) : |flowSign i j|≤1 := by
  unfold flowSign
  split_ifs <;> norm_num

/-- The actual matrix commutator derivative of the Green inverse.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowGreenVelocity (w : WeightSimplex (n+1)) (t : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  flowGenerator S w t*flowGreen S w t-flowGreen S w t*flowGenerator S w t

/-- The generator is the signed and scaled actual Green matrix.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGenerator_sign (w : WeightSimplex (n+1)) (t : ℝ) (i j : Fin (n+1)) :
    flowGenerator S w t i j=flowScale (n+1)*flowSign i j*flowGreen S w t i j := by
  rw [flowGenerator_formula]
  unfold flowSign flowScale flowGreen flowEigenvalue
  push_cast
  split_ifs <;> ring

/-- The commutator formula differentiates every specified Green entry.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGreen_hasDerivAt (w : WeightSimplex (n+1)) (t : ℝ) (i j : Fin (n+1)) :
    HasDerivAt (fun s => flowGreen S w s i j) (flowGreenVelocity S w t i j) t :=
  flowSpectral_hasDerivAt S w (flowEigenvalue S) t i j

/-- The exact signed-square formula for the diagonal velocity.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowDiagonalVelocity (w : WeightSimplex (n+1)) (t : ℝ) (i : Fin (n+1)) : ℝ :=
  2*flowScale (n+1)*∑ j,flowSign i j*(flowGreen S w t i j)^2

/-- The actual commutator diagonal equals the signed-square formula.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGreenVelocity_diag (w : WeightSimplex (n+1)) (t : ℝ) (i : Fin (n+1)) :
    flowGreenVelocity S w t i i=flowDiagonalVelocity S w t i := by
  unfold flowGreenVelocity flowDiagonalVelocity
  simp only [Matrix.sub_apply,Matrix.mul_apply,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hb := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => A i j)
    (flowGenerator_skew S w t)
  change flowGenerator S w t j i = -flowGenerator S w t i j at hb
  rw [hb,flowGreen_symmetric S w t j i,flowGenerator_sign]
  ring

/-- The exact first derivative of each actual Green diagonal.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowDiagonal_hasDerivAt (w : WeightSimplex (n+1)) (t : ℝ) (i : Fin (n+1)) :
    HasDerivAt (fun s => flowGreen S w s i i) (flowDiagonalVelocity S w t i) t := by
  rw [← flowGreenVelocity_diag]
  exact flowGreen_hasDerivAt S w t i i

/-- The finite sum obtained by differentiating the true signed-square
diagonal velocity.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowDiagonalAcceleration (w : WeightSimplex (n+1)) (t : ℝ) (i : Fin (n+1)) : ℝ :=
  4*flowScale (n+1)*∑ j,flowSign i j*flowGreen S w t i j*flowGreenVelocity S w t i j

/-- Differentiate the actual diagonal velocity, not a surrogate curve.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowDiagonalVelocity_hasDerivAt (w : WeightSimplex (n+1)) (t : ℝ)
    (i : Fin (n+1)) : HasDerivAt (fun s => flowDiagonalVelocity S w s i)
      (flowDiagonalAcceleration S w t i) t := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((flowGreen_hasDerivAt S w t i j).pow 2).const_mul (flowSign i j))).const_mul
      (2*flowScale (n+1))
  convert h using 1
  · rfl
  · unfold flowDiagonalAcceleration
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    norm_num only [Nat.cast_ofNat,pow_one]
    ring

/-- The actual finite Green energy along the reconstructed family.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowEnergy (w : WeightSimplex (n+1)) (t : ℝ) : ℝ :=
  ∑ i,(flowGreen S w t i i)^2

/-- This finite sum is exactly the Jacobi energy used by the original
minimization problem.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowEnergy_eq (w : WeightSimplex (n+1)) (t : ℝ) :
    flowEnergy S w t=(reconstructFiber S (resolventWeights S w t)).val.energy := by
  simp only [flowEnergy,chebyshev2.Jacobi.energy,flowGreen_eq]

/-- The first energy derivative as the finite diagonal pairing.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowEnergyVelocity (w : WeightSimplex (n+1)) (t : ℝ) : ℝ :=
  2*∑ i,flowGreen S w t i i*flowDiagonalVelocity S w t i

/-- The second energy derivative as the finite diagonal pairing.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowEnergyAcceleration (w : WeightSimplex (n+1)) (t : ℝ) : ℝ :=
  2*∑ i,((flowDiagonalVelocity S w t i)^2+
    flowGreen S w t i i*flowDiagonalAcceleration S w t i)

/-- The first energy pairing differentiates the actual energy.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowEnergy_hasDerivAt (w : WeightSimplex (n+1)) (t : ℝ) :
    HasDerivAt (flowEnergy S w) (flowEnergyVelocity S w t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (flowDiagonal_hasDerivAt S w t i).pow 2)
  convert h using 1
  · rfl
  · unfold flowEnergyVelocity
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    norm_num only [Nat.cast_ofNat,pow_one]
    ring

/-- The second pairing differentiates the actual first energy derivative.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowEnergyVelocity_hasDerivAt (w : WeightSimplex (n+1)) (t : ℝ) :
    HasDerivAt (flowEnergyVelocity S w) (flowEnergyAcceleration S w t) t := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (flowDiagonal_hasDerivAt S w t i).mul (flowDiagonalVelocity_hasDerivAt S w t i))).const_mul 2
  convert h using 1
  · rfl
  · unfold flowEnergyAcceleration
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Pairing opposite index orientations yields the exact energy derivative
as a sum over strictly ordered physical vertex pairs. This is the form
used in the continuum limit of the standard realization's initial slope.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowEnergyVelocity_pairs (w : WeightSimplex (n+1)) (t : ℝ) :
    flowEnergyVelocity S w t=4*flowScale (n+1)*∑ i,∑ j,
      if j < i then (flowGreen S w t i i-flowGreen S w t j j)*(flowGreen S w t i j)^2 else 0 := by
  have hs (i j : Fin (n+1)) : flowSign i j*(flowGreen S w t i j)^2=
      (if j < i then (flowGreen S w t i j)^2 else 0)-
        (if i < j then (flowGreen S w t i j)^2 else 0) := by
    unfold flowSign
    split_ifs <;> simp_all
    omega
  have he : (∑ i,∑ j,if i < j then flowGreen S w t i i*(flowGreen S w t i j)^2 else 0)=
      ∑ i,∑ j,if j < i then flowGreen S w t j j*(flowGreen S w t i j)^2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [flowGreen_symmetric S w t j i]
  have hp : (∑ i,∑ j,flowGreen S w t i i*(flowSign i j*(flowGreen S w t i j)^2))=
      ∑ i,∑ j,if j < i then
        (flowGreen S w t i i-flowGreen S w t j j)*(flowGreen S w t i j)^2 else 0 := by
    simp_rw [hs,mul_sub,mul_ite,mul_zero]
    simp_rw [Finset.sum_sub_distrib]
    rw [he,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  calc
    _=4*flowScale (n+1)*(∑ i,∑ j,flowGreen S w t i i*
        (flowSign i j*(flowGreen S w t i j)^2)) := by
      unfold flowEnergyVelocity flowDiagonalVelocity
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _=_ := by rw [hp]

end
end jacobi.Finite
