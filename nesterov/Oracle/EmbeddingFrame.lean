import nesterov.Oracle.ResistingFrame

/-! Linear isometric realization of a finite orthonormal frame and its
actual coordinate map. -/
namespace nesterov.Oracle
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace
variable {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def frameLift (v : I→E) : EuclideanSpace ℝ I→ₗ[ℝ] E where
  toFun x := ∑ i,x i • v i
  map_add' x y := by simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a x := by simp only [PiLp.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

def frameCoordinates (v : I→E) (y : E) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i=>inner ℝ (v i) y)

omit [Fintype I] in
theorem frameCoordinates_apply (v : I→E) (y : E) (i : I) :
    frameCoordinates v y i=inner ℝ (v i) y := rfl

theorem inner_frameLift (v : I→E) (x : EuclideanSpace ℝ I) (y : E) :
    inner ℝ (frameLift v x) y=inner ℝ x (frameCoordinates v y) := by
  change inner ℝ (∑ i,x i • v i) y=inner ℝ x (frameCoordinates v y)
  rw [sum_inner,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [real_inner_smul_left,frameCoordinates_apply,Real.inner_apply]

theorem frameCoordinates_lift {v : I→E} (hv : Orthonormal ℝ v) (x : EuclideanSpace ℝ I) :
    frameCoordinates v (frameLift v x)=x := by
  ext i
  exact hv.inner_right_fintype x i

theorem norm_frameLift {v : I→E} (hv : Orthonormal ℝ v) (x : EuclideanSpace ℝ I) :
    ‖frameLift v x‖=‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [←real_inner_self_eq_norm_sq,inner_frameLift,frameCoordinates_lift hv,
    real_inner_self_eq_norm_sq]

def frameIsometry {v : I→E} (hv : Orthonormal ℝ v) : EuclideanSpace ℝ I→ₗᵢ[ℝ] E where
  toLinearMap := frameLift v
  norm_map' := norm_frameLift hv

theorem inner_frameLift_left {v : I→E} (hv : Orthonormal ℝ v)
    (x y : EuclideanSpace ℝ I) :
    inner ℝ (frameLift v x) (frameLift v y)=inner ℝ x y := by
  rw [inner_frameLift,frameCoordinates_lift hv]

omit [Fintype I] in
theorem frameCoordinates_frame [DecidableEq I] {v : I→E} (hv : Orthonormal ℝ v) (i : I) :
    frameCoordinates v (v i)=EuclideanSpace.single i 1 := by
  ext j
  simp only [frameCoordinates_apply,PiLp.single_apply]
  exact orthonormal_iff_ite.mp hv j i

end
end nesterov.Oracle
