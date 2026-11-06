import chebyshev1.Stochastic.UniformSphere
import chebyshev1.Spectral.Basis

/-! Uniform directions in an orthonormal spectral frame, including a removed constant mode. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {d a : Type*} [Fintype d] [DecidableEq d] [Nonempty d] [Fintype a]

theorem uniformSphere_rectangular_norm_sq (M : Matrix a d ℝ) :
    (∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
      ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp x.val))‖^2
      ∂uniformSphere (EuclideanSpace ℝ d)) =
        (∑ i, ∑ j, (M i j)^2)/(Fintype.card d:ℝ) := by
  have hi (i j k) : Integrable (fun x : Metric.sphere (0:EuclideanSpace ℝ d) 1 =>
      (M i j*M i k)*(x.val j*x.val k)) (uniformSphere (EuclideanSpace ℝ d)) := by
    have hc : Continuous (fun x : Metric.sphere (0:EuclideanSpace ℝ d) 1 =>
      (M i j*M i k)*(x.val j*x.val k)) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (x : Metric.sphere (0:EuclideanSpace ℝ d) 1) :
      ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp x.val))‖^2 =
        ∑ i, ∑ j, ∑ k, (M i j*M i k)*(x.val j*x.val k) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mulVec, dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_finsetSum _ (fun k _ => hi i j k)))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi _ j k)),
    integral_finsetSum _ (fun k _ => hi _ _ k), integral_const_mul, uniformSphere_coord_pair]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [← Finset.sum_div, sq, mul_one_div]

end
end chebyshev1.Stochastic

namespace chebyshev1.SpectralBasis
noncomputable section
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d] [DecidableEq d]
  {H : Matrix d d ℝ} (B : SpectralBasis H)

def omittedFrame (c : d) : Matrix d {j : d // j≠c} ℝ := fun i j => B.Q i j.val

def frameError (c : d) (x : EuclideanSpace ℝ {j : d // j≠c}) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 ((B.omittedFrame c).mulVec (WithLp.ofLp x))

theorem omittedFrame_orthonormal (c : d) : (B.omittedFrame c)ᵀ*B.omittedFrame c=1 := by
  ext i j
  have hh := congrArg (fun M : Matrix d d ℝ => M i.val j.val) B.transpose_mul
  simpa only [omittedFrame, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    Subtype.coe_inj] using hh

/-- The initial directions are sampled by an actual isometric embedding. -/
theorem frameError_norm (c : d) (x : EuclideanSpace ℝ {j : d // j≠c}) :
    ‖B.frameError c x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [sq]
  change dotProduct ((B.omittedFrame c).mulVec (WithLp.ofLp x))
      ((B.omittedFrame c).mulVec (WithLp.ofLp x)) = dotProduct (WithLp.ofLp x) (WithLp.ofLp x)
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    B.omittedFrame_orthonormal, Matrix.one_mulVec]

theorem frameError_orthogonal (c : d) (x : EuclideanSpace ℝ {j : d // j≠c}) :
    dotProduct (fun i => B.Q i c) (WithLp.ofLp (B.frameError c x)) = 0 := by
  have hcol (j : {j : d // j≠c}) : ∑ i, B.Q i c*B.Q i j.val = 0 := by
    have hh := congrArg (fun M : Matrix d d ℝ => M c j.val) B.transpose_mul
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Ne.symm j.property, ite_false] using hh
  change dotProduct (fun i => B.Q i c) ((B.omittedFrame c).mulVec (WithLp.ofLp x))=0
  rw [Matrix.dotProduct_mulVec]
  have hz : Matrix.vecMul (fun i => B.Q i c) (B.omittedFrame c)=0 := by
    ext j
    exact hcol j
  rw [hz]
  simp

/-- The frame covers the entire orthogonal hyperplane, not a smaller set of directions. -/
theorem frameError_range (c : d) : Set.range (B.frameError c) =
    {y : EuclideanSpace ℝ d | dotProduct (fun i => B.Q i c) (WithLp.ofLp y)=0} := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact B.frameError_orthogonal c x
  · intro hy
    let a : d → ℝ := B.Qᵀ.mulVec (WithLp.ofLp y)
    have hac : a c=0 := hy
    let x : EuclideanSpace ℝ {j : d // j≠c} := WithLp.toLp 2 (fun j => a j.val)
    refine ⟨x,?_⟩
    have hsum (i : d) : (∑ j : {j : d // j≠c}, B.Q i j.val*a j.val) =
        ∑ j, B.Q i j*a j := by
      have hh := Fintype.sum_subtype_add_sum_subtype (fun j : d => j≠c)
        (fun j => B.Q i j*a j)
      have hz : (∑ j : {j : d // ¬j≠c}, B.Q i j.val*a j.val)=0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [not_ne_iff.mp j.property,hac,mul_zero]
      simpa only [hz,add_zero] using hh
    have hfull : B.Q.mulVec a = WithLp.ofLp y := by
      dsimp only [a]
      rw [Matrix.mulVec_mulVec,B.mul_transpose,Matrix.one_mulVec]
    apply (WithLp.linearEquiv 2 ℝ (d → ℝ)).injective
    funext i
    exact (hsum i).trans (congrFun hfull i)

theorem omittedFrame_hsSq (c : d) (M : Matrix d d ℝ) (hc : ∀ i, (M*B.Q) i c=0) :
    (∑ i, ∑ j : {j : d // j≠c}, (M*B.omittedFrame c) i j ^ 2) = hsSq M := by
  calc
    _ = hsSq (M*B.Q) := by
      apply Finset.sum_congr rfl
      intro i _
      have hh := Fintype.sum_subtype_add_sum_subtype (fun j : d => j≠c)
        (fun j => (M*B.Q) i j ^ 2)
      have hz : (∑ j : {j : d // ¬j≠c}, (M*B.Q) i j.val ^ 2)=0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [not_ne_iff.mp j.property, hc, zero_pow (by norm_num : 2≠0)]
      change (∑ j : {j : d // j≠c}, (M*B.Q) i j.val ^ 2) = _
      simpa only [hz, add_zero] using hh
    _ = _ := hsSq_orthogonal_right B.Q M B.mul_transpose

theorem uniformSphere_frame_matrix_norm_sq (c : d) [Nonempty {j : d // j≠c}]
    (M : Matrix d d ℝ) (hc : ∀ i, (M*B.Q) i c=0) :
    (∫ x : Metric.sphere (0:EuclideanSpace ℝ {j : d // j≠c}) 1,
      ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp (B.frameError c x.val)))‖^2
      ∂Stochastic.uniformSphere (EuclideanSpace ℝ {j : d // j≠c})) =
        hsSq M / (Fintype.card {j : d // j≠c}:ℝ) := by
  change (∫ x : Metric.sphere (0:EuclideanSpace ℝ {j : d // j≠c}) 1,
      ‖WithLp.toLp 2 (M.mulVec ((B.omittedFrame c).mulVec (WithLp.ofLp x.val)))‖^2
      ∂Stochastic.uniformSphere (EuclideanSpace ℝ {j : d // j≠c})) = _
  simp_rw [Matrix.mulVec_mulVec]
  rw [Stochastic.uniformSphere_rectangular_norm_sq, B.omittedFrame_hsSq c M hc]

end
end chebyshev1.SpectralBasis
