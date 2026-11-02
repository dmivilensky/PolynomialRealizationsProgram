import krylov.Envelope.KrylovFlags

set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:F1 and apB:lem:mu(b), genuine polynomial Krylov propagation.
Use: propagate actual Krylov vectors under true operator powers and real
polynomial actions with their genuine degree bounds, for canonical
absorption of the actual common tilt and unexplored response.
Source: standard polynomial functional calculus, true degree-bounded
Krylov flags and their proved genuine operator propagation.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial krylov.Reference
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual power of the true reference operator moves a genuine order-k Krylov vector into its real order-k-plus-power flag.
Use: Every actual power of the true reference operator moves a genuine order-k Krylov vector into its real order-k-plus-power flag.
Article: main_krylov, apB:eq:F1 and apB:lem:mu(b), genuine polynomial Krylov propagation.
Proof: Iterate the proved actual reference-operator Krylov propagation. -/
theorem krylovSpace_operator_pow (Q : E →L[ℝ] E) (g : E) (k r : ℕ) {v : E}
    (hv : v∈CG.krylovSpace Q g k) : (Q.toLinearMap^r) v∈CG.krylovSpace Q g (k+r) := by
  induction r with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.add_zero] using hv
  | succ r ih =>
    rw [pow_succ',Module.End.mul_apply]
    convert! krylovSpace_operator Q g (k+r) ih using 1

/-- Every actual reference-polynomial action moves a genuine Krylov vector into the true flag increased by its real polynomial degree.
Use: Every actual reference-polynomial action moves a genuine Krylov vector into the true flag increased by its real polynomial degree.
Article: main_krylov, apB:eq:F1 and apB:lem:mu(b), genuine polynomial Krylov propagation.
Proof: Expand the genuine finite operator-power sum; each actual power has the proved true flag membership, which increases monotonically to the real common degree bound. -/
theorem krylovSpace_polynomial (Q : E →L[ℝ] E) (g : E) (k : ℕ) (p : ℝ[X]) {v : E}
    (hv : v∈CG.krylovSpace Q g k) : (aeval Q.toLinearMap p) v∈CG.krylovSpace Q g (k+p.natDegree) := by
  -- Each actual polynomial power term enters its true finite Krylov flag before passing to the genuine common degree bound.
  rw [Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  apply krylovSpace_mono Q g (show k+j≤k+p.natDegree by have := Finset.mem_range.mp hj;omega)
  exact krylovSpace_operator_pow Q g k j hv
end
end krylov.Envelope
