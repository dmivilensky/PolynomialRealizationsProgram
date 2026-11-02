import jacobi.Finite.FlowBasis
import jacobi.Finite.GreenEntries

/-!
The Lax equation for the globally reconstructed resolvent flow.
The polynomial-degree orthogonality identity determines the canonical
eigenbasis velocity. Spectral conjugation then differentiates every fixed
spectral observable, including the Jacobi matrix and its Green inverse.
Use: FlowBounds computes the diagonal and energy derivatives from this
actual flow rather than assuming a differentiable isospectral lift.
Article: jacobi, Proposition 5.5, Equation (5.11).
Article role: the global positive-weight construction and its exact resolvent Lax equation.
-/
namespace jacobi.Finite
noncomputable section
open Matrix Real chebyshev2
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (S : Nodes (n+1))

/-- The skew velocity of the actual orthonormal basis in physical row
coordinates. The resolvent formula below identifies this concrete matrix.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def flowGenerator (w : WeightSimplex (n+1)) (t : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  flowBasisVelocity S w t*(flowBasis S w t)ᵀ

/-- Every fixed spectral observable transported by the canonical basis.
The choice zeta gives J, and the reciprocal endpoint gap gives its Green inverse.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def flowSpectral (w : WeightSimplex (n+1)) (f : Fin (n+1) → ℝ) (t : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  flowBasis S w t*diagonal f*(flowBasis S w t)ᵀ

/-- The entrywise finite spectral sum, preserving the multiplication order
when differentiating matrix-valued expressions.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowSpectral_entry (w : WeightSimplex (n+1)) (f : Fin (n+1) → ℝ)
    (t : ℝ) (i j : Fin (n+1)) :
    flowSpectral S w f t i j=∑ k,flowBasis S w t i k*f k*flowBasis S w t j k := by
  rw [flowSpectral,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply]

/-- The actual matrix is the observable with the original, unchanged roots.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowSpectral_matrix (w : WeightSimplex (n+1)) (t : ℝ) :
    flowSpectral S w S.value t=(reconstructFiber S (resolventWeights S w t)).val.matrix := by
  rw [show (reconstructFiber S (resolventWeights S w t)).val.matrix=
      (flowMeasure S w t).multiplication from (flowMeasure S w t).reconstructed_matrix,
    (flowMeasure S w t).multiplication_diagonalization]
  rfl

/-- The reciprocal-gap observable is exactly the actual matrix inverse.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowSpectral_green (w : WeightSimplex (n+1)) (t : ℝ) :
    flowSpectral S w (fun k => (1-S.value k)⁻¹) t=
      (reconstructFiber S (resolventWeights S w t)).val.green := by
  change flowSpectral S w (fun k => (1-S.value k)⁻¹) t=(flowMeasure S w t).reconstructed.green
  ext i j
  rw [green_entry_spectral _ (flowMeasure S w t).reconstructedBasis
    (fun k => (sub_pos.mpr (S.interval k).2).ne'),flowSpectral_entry]
  apply Finset.sum_congr rfl
  intro k _
  change flowBasis S w t i k*(1-S.value k)⁻¹*flowBasis S w t j k=
    flowBasis S w t i k*flowBasis S w t j k/(1-S.value k)
  ring

/-- Differentiated orthogonality makes the physical generator skew.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowGenerator_skew (w : WeightSimplex (n+1)) (t : ℝ) :
    (flowGenerator S w t)ᵀ = -flowGenerator S w t := by
  ext i j
  have h := flowBasisVelocity_skew S w t i j
  simp only [flowGenerator,Matrix.mul_apply,Matrix.transpose_apply,Matrix.neg_apply]
  linarith

/-- Multiplying the physical generator by the basis recovers its actual
time derivative, since the original basis is square and orthogonal.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowBasisVelocity_eq (w : WeightSimplex (n+1)) (t : ℝ) :
    flowBasisVelocity S w t=flowGenerator S w t*flowBasis S w t := by
  rw [flowGenerator,Matrix.mul_assoc]
  change _=flowBasisVelocity S w t*
    ((flowMeasure S w t).eigenvectorsᵀ*(flowMeasure S w t).eigenvectors)
  rw [(flowMeasure S w t).eigenvectors_transpose_mul,Matrix.mul_one]

/-- The upper generator entries are minus the scaled actual Green
entries. The polynomial argument, not isospectrality alone, gives this sign.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowGenerator_upper (w : WeightSimplex (n+1)) (t : ℝ)
    (i j : Fin (n+1)) (hij : i<j) :
    flowGenerator S w t i j =
      -(flowSpectral S w (fun k => (1-S.value k)⁻¹) t i j/(n+1:ℝ)^2) := by
  change (∑ k,flowBasisVelocity S w t i k*flowBasis S w t j k)=_
  rw [flowBasisVelocity_upper S w t i j hij,flowSpectral_entry]
  simp only [Finset.sum_div,Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold resolventVelocity
  field_simp [(sub_pos.mpr (S.interval k).2).ne',show (n+1:ℝ)≠0 by positivity]

/-- The generator is the strict lower scaled Green matrix minus its
strict upper part. Its diagonal is exactly zero.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowGenerator_formula (w : WeightSimplex (n+1)) (t : ℝ) (i j : Fin (n+1)) :
    flowGenerator S w t i j=
      (if j < i then flowSpectral S w (fun k => (1-S.value k)⁻¹) t i j/(n+1:ℝ)^2
      else if i < j then -(flowSpectral S w (fun k => (1-S.value k)⁻¹) t i j/(n+1:ℝ)^2)
      else 0) := by
  have hg := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => A i j)
    (flowGenerator_skew S w t)
  change flowGenerator S w t j i = -flowGenerator S w t i j at hg
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [ite_eq_right (not_lt_of_gt hij),ite_eq_left hij]
    exact flowGenerator_upper S w t i j hij
  · simp only [lt_self_iff_false,ite_false]
    linarith
  · rw [ite_eq_left hji]
    have hu := flowGenerator_upper S w t j i hji
    have hs : flowSpectral S w (fun k => (1-S.value k)⁻¹) t j i=
        flowSpectral S w (fun k => (1-S.value k)⁻¹) t i j := by
      simp only [flowSpectral_entry]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hs] at hu
    linarith

/-- Every fixed spectral observable satisfies the genuine commutator
equation. This simultaneously proves the matrix and resolvent derivatives.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowSpectral_hasDerivAt (w : WeightSimplex (n+1)) (f : Fin (n+1) → ℝ)
    (t : ℝ) (i j : Fin (n+1)) :
    HasDerivAt (fun s => flowSpectral S w f s i j)
      ((flowGenerator S w t*flowSpectral S w f t-
        flowSpectral S w f t*flowGenerator S w t) i j) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((flowBasis_analytic S w t i k).differentiableAt.hasDerivAt.mul_const (f k)).mul
      (flowBasis_analytic S w t j k).differentiableAt.hasDerivAt)
  have he : flowBasisVelocity S w t*diagonal f*(flowBasis S w t)ᵀ+
      flowBasis S w t*diagonal f*(flowBasisVelocity S w t)ᵀ=
      flowGenerator S w t*flowSpectral S w f t-
        flowSpectral S w f t*flowGenerator S w t := by
    rw [flowBasisVelocity_eq S w t,Matrix.transpose_mul,flowGenerator_skew]
    unfold flowSpectral
    noncomm_ring
  rw [← he,Matrix.add_apply]
  have h1 : (flowBasisVelocity S w t*diagonal f*(flowBasis S w t)ᵀ) i j=
      ∑ k,flowBasisVelocity S w t i k*f k*flowBasis S w t j k := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
  have h2 : (flowBasis S w t*diagonal f*(flowBasisVelocity S w t)ᵀ) i j=
      ∑ k,flowBasis S w t i k*f k*flowBasisVelocity S w t j k := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
  rw [h1,h2]
  simpa only [flowSpectral_entry,flowBasisVelocity,Pi.mul_apply,Finset.sum_add_distrib] using h

/-- The globally constructed flow satisfies the requested matrix Lax
equation through the actual initial fibre member.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventFlow_lax (J : Fiber (n+1) S.polynomial) (t : ℝ)
    (i j : Fin (n+1)) :
    HasDerivAt (fun s => (resolventFlow S J s).val.matrix i j)
      ((flowGenerator S (spectralWeights S J) t*(resolventFlow S J t).val.matrix-
        (resolventFlow S J t).val.matrix*flowGenerator S (spectralWeights S J) t) i j) t := by
  simpa only [flowSpectral_matrix,resolventFlow] using
    flowSpectral_hasDerivAt S (spectralWeights S J) S.value t i j

/-- The actual Green inverse along this same flow satisfies its own
commutator equation, without assuming differentiability of matrix inversion.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventFlow_green_hasDerivAt (J : Fiber (n+1) S.polynomial) (t : ℝ)
    (i j : Fin (n+1)) :
    HasDerivAt (fun s => (resolventFlow S J s).val.green i j)
      ((flowGenerator S (spectralWeights S J) t*(resolventFlow S J t).val.green-
        (resolventFlow S J t).val.green*flowGenerator S (spectralWeights S J) t) i j) t := by
  simpa only [flowSpectral_green,resolventFlow] using
    flowSpectral_hasDerivAt S (spectralWeights S J) (fun k => (1-S.value k)⁻¹) t i j

/-- The generator in the actual matrix equation is exactly the strict
lower part of R/n² minus its strict upper part.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventFlow_generator (J : Fiber (n+1) S.polynomial) (t : ℝ)
    (i j : Fin (n+1)) :
    flowGenerator S (spectralWeights S J) t i j=
      (if j < i then (resolventFlow S J t).val.green i j/(n+1:ℝ)^2
      else if i < j then -((resolventFlow S J t).val.green i j/(n+1:ℝ)^2)
      else 0) := by
  simpa only [flowSpectral_green,resolventFlow] using
    flowGenerator_formula S (spectralWeights S J) t i j

end
end jacobi.Finite
