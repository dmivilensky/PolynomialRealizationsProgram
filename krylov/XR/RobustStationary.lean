import krylov.XR.RobustExistence

/-!
Article: main_krylov, thm:metric, true interior robust stationarity.
Use: derive the positive regularization parameter from an actual robust
minimizer away from the endpoint branches. Source: the proved norm
differential and Fermat's theorem, followed by exact self-adjoint algebra.
-/
namespace krylov.XR
noncomputable section
open Set Filter Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine interior minimizer has zero actual normalized residual
gradient. Article: main_krylov, thm:metric, Tikhonov optimality. -/
theorem robust_interior_balance (N : E →L[ℝ] E) (hN : N.toLinearMap.IsSymmetric)
    (rho b : E) (omega : ℝ) (hb : b≠0) (hr : rho+N b≠0)
    (hmin : ∀ z : E,robustModelObjective N rho omega b≤robustModelObjective N rho omega z) :
    ‖rho+N b‖⁻¹ • N (rho+N b)+(omega*‖b‖⁻¹) • b=0 := by
  let G := ‖rho+N b‖⁻¹ • N (rho+N b)+(omega*‖b‖⁻¹) • b
  have hm : IsLocalMin (robustModelObjective N rho omega) b := Filter.Eventually.of_forall hmin
  have hd := hm.hasFDerivAt_eq_zero (robustModelObjective_hasFDerivAt N rho b omega hb hr)
  have he : (‖rho+N b‖⁻¹ • innerSL ℝ (rho+N b)).comp N+
      omega • (‖b‖⁻¹ • innerSL ℝ b)=innerSL ℝ G := by
    ext v
    have hs : inner ℝ (N (rho+N b)) v=inner ℝ (rho+N b) (N v) := hN _ _
    simp only [G,_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
      innerSL_apply_apply,inner_add_left,real_inner_smul_left,smul_eq_mul,hs]
    ring
  have hi : inner ℝ G G=0 := by
    have hh := congrArg (fun L : E →L[ℝ] ℝ=>L G) hd
    rw [he] at hh
    exact hh
  have hz : ‖G‖=0 := by rw [real_inner_self_eq_norm_sq] at hi;nlinarith only [hi]
  exact norm_eq_zero.mp hz

/-- The actual interior optimum determines a positive Tikhonov
parameter from its own residual and correction norms.
Article: main_krylov, thm:metric. -/
theorem robust_interior_regularizer (N : E →L[ℝ] E) (hN : N.toLinearMap.IsSymmetric)
    (rho b : E) (omega : ℝ) (homega : 0<omega) (hb : b≠0) (hr : rho+N b≠0)
    (hmin : ∀ z : E,robustModelObjective N rho omega b≤robustModelObjective N rho omega z) :
    ∃ lambda : ℝ,0<lambda ∧ N (rho+N b)+lambda • b=0 ∧
      lambda=omega*‖rho+N b‖/‖b‖ := by
  let lambda := omega*‖rho+N b‖/‖b‖
  have hl : 0<lambda := div_pos (mul_pos homega (norm_pos_iff.mpr hr)) (norm_pos_iff.mpr hb)
  have hg := robust_interior_balance N hN rho b omega hb hr hmin
  have hh := congrArg (fun x : E=>‖rho+N b‖ • x) hg
  simp only [smul_add,smul_smul,smul_zero,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hr),one_smul] at hh
  refine ⟨lambda,hl,?_,rfl⟩
  have hcoeff : lambda=‖rho+N b‖*(omega*‖b‖⁻¹) := by
    dsimp only [lambda]
    ring
  rw [hcoeff]
  exact hh

end
end krylov.XR
