import krylov.Functions.NativeRFCBootstrap
import krylov.Functions.MetricFCIncrementTransfer

/-!
Article: main_krylov, lem:cycle-transfer, actual ordinary RFC trajectory shadow.
Use: telescope the derived true total-step errors; the evaluated search point
also differs from the next quadratic node only by the derived quadratic
correction query. Source: actual RFC records and finite telescoping.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual native ordinary RFC nodes shadow all true CG reference nodes to
second order, with an explicit finite-prefix factor.
Article: main_krylov, lem:cycle-transfer. -/
theorem NativeRFCPrefixBounds.reference_points (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (N : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C N) :
    ∀ k≤N, ‖rfcFunctionPoint T f G fullMemory r (ε • u) k-
      ε • fcQuadraticReferencePoint Q u k‖≤(k:ℝ)*C*ε^2 := by
  let x := rfcFunctionPoint T f G fullMemory r (ε • u)
  let y := fun j=>ε • fcQuadraticReferencePoint Q u j
  have hzero : x 0=y 0 := by
    simp [x,y,rfcFunctionPoint,rfcFunctionRun,History.displacement,fcQuadraticReferencePoint,CG.displacement]
  have hys j : y (j+1)-y j=ε • referenceStep Q (Q u) j := by
    dsimp only [y]
    rw [←smul_sub,fcQuadraticReferencePoint_step]
  have hs j (hj : j<N) : ‖(x (j+1)-x j)-(y (j+1)-y j)‖≤C*ε^2 := by
    rw [hys]
    have hxs : x (j+1)-x j=(rfcFunctionRecord T f G fullMemory r (ε • u)
        (rfcFunctionRun T f G fullMemory r (ε • u) j)).step := by
      dsimp only [x]
      rw [rfcFunctionPoint_succ,add_sub_cancel_left]
    rw [hxs]
    exact (hp.2 j hj).2.2.2.2
  intro k hk
  exact (trajectory_step_error_bound x y N (C*ε^2) hzero hs k hk).trans_eq (by ring)

/-- The genuinely evaluated search endpoint shadows the next true quadratic
node, including the true correction's quadratic contribution.
Article: main_krylov, lem:cycle-transfer. -/
theorem NativeRFCPrefixBounds.reference_search_points (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (N : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C N) :
    ∀ k<N, ‖rfcFunctionLinePoint T f fullMemory r (ε • u)
      (rfcFunctionRun T f G fullMemory r (ε • u) k)-
      ε • fcQuadraticReferencePoint Q u (k+1)‖≤((k:ℝ)+2)*C*ε^2 := by
  intro k hk
  let S := rfcFunctionRun T f G fullMemory r (ε • u) k
  let U := rfcFunctionCorrectionStep T f G fullMemory r (ε • u) S
  let Y := rfcFunctionLinePoint T f fullMemory r (ε • u) S
  have he : Y-ε • fcQuadraticReferencePoint Q u (k+1)=
      (rfcFunctionPoint T f G fullMemory r (ε • u) (k+1)-ε • fcQuadraticReferencePoint Q u (k+1))-U := by
    rw [rfcFunctionPoint_succ_line]
    change Y-_=(Y+U-_)-U
    abel
  rw [show rfcFunctionLinePoint T f fullMemory r (ε • u) (rfcFunctionRun T f G fullMemory r (ε • u) k)=Y from rfl,he]
  have hb := hp.reference_points T f G H Q r u ε M D C N (k+1) (by omega)
  have hu := (hp.2 k hk).2.2.2.1
  exact (norm_sub_le _ _).trans ((add_le_add hb hu).trans_eq (by push_cast; ring))

/-- The real search midpoint has the same quadratic-reference midpoint up to
second order. Article: main_krylov, thm:Htransfer. -/
theorem NativeRFCPrefixBounds.reference_midpoints (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (N : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C N) :
    ∀ k<N,
    let X := rfcFunctionPoint T f G fullMemory r (ε • u) k
    let Y := rfcFunctionLinePoint T f fullMemory r (ε • u) (rfcFunctionRun T f G fullMemory r (ε • u) k)
    ‖(X+(1/2:ℝ) • (Y-X))-
      ε • (fcQuadraticReferencePoint Q u k+(1/2:ℝ) • referenceStep Q (Q u) k)‖≤((k:ℝ)+1)*C*ε^2 := by
  intro k hk
  have hb := midpoint_error_bound
    (rfcFunctionPoint T f G fullMemory r (ε • u) k)
    (rfcFunctionLinePoint T f fullMemory r (ε • u) (rfcFunctionRun T f G fullMemory r (ε • u) k))
    (ε • fcQuadraticReferencePoint Q u k) (ε • fcQuadraticReferencePoint Q u (k+1))
  have he : ε • (fcQuadraticReferencePoint Q u k+(1/2:ℝ) • referenceStep Q (Q u) k)=
      ε • fcQuadraticReferencePoint Q u k+(1/2:ℝ) •
        (ε • fcQuadraticReferencePoint Q u (k+1)-ε • fcQuadraticReferencePoint Q u k) := by
    rw [←smul_sub,fcQuadraticReferencePoint_step]
    module
  rw [he]
  exact hb.trans (by nlinarith only [hp.reference_points T f G H Q r u ε M D C N k hk.le,
    hp.reference_search_points T f G H Q r u ε M D C N k hk])

end
end krylov.Functions
