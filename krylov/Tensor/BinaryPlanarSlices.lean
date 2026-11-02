import krylov.Tensor.BinaryMixed
import krylov.Information.PlanarRadius

/-!
Article: main_krylov, thm:H, true operator budgets of compatible binary tensors.
Use: lift the actual diagonal binary unit ball to its real planar slice
matrices in arbitrary orthonormal physical directions. Source: the proved
Banach tensor bound and the actual two-vector Bessel inequality.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section
open Real Matrix krylov.Functions krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual physical matrix slice of one compatible binary tensor.
Article: main_krylov, thm:H, equation (apD:eq:slice). -/
def planarSlice (e h : EuclideanSpace ℝ (Fin n)) (t : BinaryCubic) (z : Plane) :
    Matrix (Fin n) (Fin n) ℝ :=
  planarMatrix e h (z 0*t.t0+z 1*t.t1) (z 0*t.t1+z 1*t.t2) (z 0*t.t2+z 1*t.t3)

/-- Every genuine compatible binary slice obeys its actual physical spectral-norm budget.
Article: main_krylov, thm:H, operator constraints inherited from one tensor. -/
theorem planarSlice_norm {t : BinaryCubic} (ht : t.InBall)
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (z : Plane) : ‖planarSlice e h t z‖ ≤ ‖z‖ := by
  let coords := fun v : EuclideanSpace ℝ (Fin n) =>
    (WithLp.toLp 2 ![inner ℝ e v, inner ℝ h v] : Plane)
  have hc v : ‖coords v‖ ≤ ‖v‖ := by
    have hs := two_unit_bessel e h v he hh heh
    have hv : ‖coords v‖^2 = (inner ℝ e v)^2+(inner ℝ h v)^2 := by
      simpa only [coords, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.isValue] using plane_norm_sq (coords v)
    nlinarith [norm_nonneg (coords v), norm_nonneg v]
  have heval v w : inner ℝ (cgOperator (planarSlice e h t z) v) w =
      t.tensor.form z (coords v) (coords w) := by
    simp only [planarSlice, cgOperator, planarMatrix_action, inner_add_left,
      real_inner_smul_left, tensor_apply, coords,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    ring
  have hinner v w : |inner ℝ (cgOperator (planarSlice e h t z) v) w| ≤ ‖z‖*‖v‖*‖w‖ := by
    rw [heval]
    exact (tensor_bound ht z (coords v) (coords w)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (hc v) (norm_nonneg _)) (hc w)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg z)
  intro v
  have hs := hinner v (cgOperator (planarSlice e h t z) v)
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hs
  change ‖cgOperator (planarSlice e h t z) v‖ ≤ ‖z‖*‖v‖
  by_contra hn
  have hn' : ‖z‖*‖v‖ < ‖cgOperator (planarSlice e h t z) v‖ := lt_of_not_ge hn
  have hp : 0 < ‖cgOperator (planarSlice e h t z) v‖ :=
    (mul_nonneg (norm_nonneg z) (norm_nonneg v)).trans_lt hn'
  have hh := mul_lt_mul_of_pos_right hn' hp
  nlinarith only [hs, hh]

/-- Both source endpoint slice matrices have their genuine unit spectral budget.
Article: main_krylov, thm:H, the two actual nonzero compatible midpoint increments. -/
theorem endpoint_slice_norms {t : BinaryCubic} (ht : t.InBall)
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) :
    ‖planarMatrix e h t.t0 t.t1 t.t2‖ ≤ 1 ∧ ‖planarMatrix e h t.t1 t.t2 t.t3‖ ≤ 1 := by
  let e0 : Plane := WithLp.toLp 2 ![1,0]
  let e1 : Plane := WithLp.toLp 2 ![0,1]
  have h0 : ‖e0‖=1 := by
    have hs : ‖e0‖^2=1 := by rw [plane_norm_sq]; norm_num [e0]
    nlinarith [norm_nonneg e0]
  have h1 : ‖e1‖=1 := by
    have hs : ‖e1‖^2=1 := by rw [plane_norm_sq]; norm_num [e1]
    nlinarith [norm_nonneg e1]
  constructor
  · simpa only [planarSlice, e0, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue, zero_mul, one_mul, add_zero, h0] using planarSlice_norm ht e h he hh heh e0
  · simpa only [planarSlice, e1, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue, zero_mul, one_mul, zero_add, h1] using planarSlice_norm ht e h he hh heh e1

end
end krylov.Tensor.BinaryCubic
