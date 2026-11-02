import krylov.Functions.PlanarEuclideanGradient
import krylov.LinearAlgebra.HilbertSchmidtCompression

/-!
Article: main_krylov, prop:Fcycle(iii), genuine full-space planar coordinates.
Use: embed the exact two-dimensional cubic fibre in any real Hilbert space
and project every unrestricted full-space output without loss in the lower
bound. Source: true orthonormal coordinates and the finite Bessel inequality.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic krylov.LinearAlgebra
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual coordinate reconstruction in the two chosen physical directions.
Article: main_krylov, prop:Fcycle(iii). -/
def hilbertPlaneEmbed (e h : E) : Plane →L[ℝ] E :=
  (EuclideanSpace.proj 0).smulRight e+(EuclideanSpace.proj 1).smulRight h

/-- Actual two inner-product observations, as a genuine Hilbert-plane map.
Article: main_krylov, prop:Fcycle(iii). -/
def hilbertPlaneProject (e h : E) : E →L[ℝ] Plane :=
  ({ toFun := fun x => planeOfPair (inner ℝ e x,inner ℝ h x)
     map_add' := by intro x y; rw [←planeOfPair_add]; congr 1; ext <;> simp [inner_add_right]
     map_smul' := by intro c x; rw [←planeOfPair_smul]; congr 1; ext <;> simp [real_inner_smul_right]
    } : E →ₗ[ℝ] Plane).mkContinuous
    (2*(‖e‖+‖h‖)) (by
      intro x
      apply (planeOfPair_norm_le _).trans
      have he := (abs_real_inner_le_norm e x)
      have hh := (abs_real_inner_le_norm h x)
      rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
      have hb : max |inner ℝ e x| |inner ℝ h x|≤(‖e‖+‖h‖)*‖x‖ := by
        apply max_le <;> nlinarith [norm_nonneg e,norm_nonneg h,norm_nonneg x]
      nlinarith only [hb])

/-- The embedding has its literal two-coordinate formula. Article: prop:Fcycle. -/
theorem hilbertPlaneEmbed_apply (e h : E) (z : Plane) :
    hilbertPlaneEmbed e h z=z 0 • e+z 1 • h := rfl

/-- The projection has its literal two inner-product coordinates. Article: prop:Fcycle. -/
theorem hilbertPlaneProject_apply (e h x : E) :
    hilbertPlaneProject e h x=planeOfPair (inner ℝ e x,inner ℝ h x) := rfl

/-- The two actual coordinate maps are true adjoints. Article: prop:Fcycle(iii). -/
theorem hilbertPlane_adjoint (e h x : E) (z : Plane) :
    inner ℝ (hilbertPlaneEmbed e h z) x=inner ℝ z (hilbertPlaneProject e h x) := by
  simp only [hilbertPlaneEmbed_apply,hilbertPlaneProject_apply,inner_add_left,
    real_inner_smul_left,PiLp.inner_apply,Fin.sum_univ_two,Real.inner_apply,
    planeOfPair,Matrix.cons_val_zero,Matrix.cons_val_one]

/-- Unit orthogonal coordinates recover every plane vector exactly.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneProject_embed (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (z : Plane) :
    hilbertPlaneProject e h (hilbertPlaneEmbed e h z)=z := by
  have hhe : inner ℝ h e=0 := by rw [real_inner_comm,heh]
  ext i
  fin_cases i <;> simp [hilbertPlaneProject_apply,hilbertPlaneEmbed_apply,
    inner_add_right,real_inner_smul_right,he,hh,heh,hhe,planeOfPair]

/-- True plane coordinates cannot increase a full-space output norm.
Article: main_krylov, prop:Fcycle(iii), unrestricted-output lower transfer. -/
theorem hilbertPlaneProject_norm_le (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (x : E) : ‖hilbertPlaneProject e h x‖≤‖x‖ := by
  have hb := two_unit_bessel e h x he hh heh
  have hs := plane_norm_sq (hilbertPlaneProject e h x)
  change ‖hilbertPlaneProject e h x‖^2=(inner ℝ e x)^2+(inner ℝ h x)^2 at hs
  nlinarith only [hb,hs,norm_nonneg (hilbertPlaneProject e h x),norm_nonneg x]

/-- The actual embedding is an isometry on the chosen orthonormal plane.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneEmbed_norm (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (z : Plane) : ‖hilbertPlaneEmbed e h z‖=‖z‖ := by
  have hs := plane_norm_sq z
  have heq : ‖hilbertPlaneEmbed e h z‖^2=(z 0)^2+(z 1)^2 := by
    rw [hilbertPlaneEmbed_apply,norm_add_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,sq_abs,he,hh,mul_one,
      real_inner_smul_left,real_inner_smul_right,heh,mul_zero,add_zero]
  nlinarith only [hs,heq,norm_nonneg (hilbertPlaneEmbed e h z),norm_nonneg z]

end
end krylov.Functions
