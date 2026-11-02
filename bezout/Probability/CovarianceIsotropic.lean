import bezout.Probability.Covariance

/-!
Article: bezout, isotropic worker covariance in the rank-one ridge MSE model.
Use: an actual coordinate covariance equal to variance times the identity is
intrinsically isotropic, hence remains so in every constructed eigenbasis.
Proof: square-integrable coordinate products justify the finite integral
expansion of both inner products; the identity covariance removes cross terms.
-/

namespace bezout.Probability
noncomputable section
open MeasureTheory
open scoped BigOperators
variable {Ω J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [Fintype J] [DecidableEq J]

/-- Coordinate covariance isotropy is a genuine intrinsic second-moment identity. -/
theorem covariance_isotropic_inner {X : Ω → EuclideanSpace ℝ J}
    (hX : MemLp X 2 μ) (hmean : (∫ ω, X ω ∂μ)=0) (variance : ℝ)
    (hcov : covarianceMatrix X μ=variance • (1 : Matrix J J ℝ))
    (x y : EuclideanSpace ℝ J) :
    (∫ ω, inner ℝ x (X ω)*inner ℝ y (X ω) ∂μ)=variance*inner ℝ x y := by
  have hsecond : secondMomentMatrix X μ=variance • (1 : Matrix J J ℝ) := by
    rwa [covarianceMatrix_of_mean_zero _ hmean] at hcov
  have he (i j : J) : (∫ ω, X ω i*X ω j ∂μ)=if i=j then variance else 0 := by
    have hh := congrFun (congrFun hsecond i) j
    simpa only [secondMomentMatrix,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,
      mul_ite,mul_one,mul_zero] using hh
  have hinner (a b : EuclideanSpace ℝ J) : inner ℝ a b=∑ i, a i*b i := by
    simp only [PiLp.inner_apply,Real.inner_apply]
  have hf (ω : Ω) : inner ℝ x (X ω)*inner ℝ y (X ω)=
      ∑ i, ∑ j, (x i*y j)*(X ω i*X ω j) := by
    rw [hinner,hinner,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : J) : Integrable (fun ω => (x i*y j)*(X ω i*X ω j)) μ :=
    (coordinate_mul_integrable hX i j).const_mul _
  simp_rw [hf]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j),integral_const_mul,he]
  calc
    _ = ∑ i, variance*(x i*y i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      ring
    _ = _ := by rw [← Finset.mul_sum,hinner]

end
end bezout.Probability
