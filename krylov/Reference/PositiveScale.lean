import krylov.Reference.CGGeometry
import krylov.Nonlinear.ReferenceCycleScale

/-!
Article: main_krylov, s7:N, normalized nondegenerate references.
Use: remove the positive operator and initial-gradient normalizations from
the genuine CG reference. Source: direct exact-search CG recurrence, including
its totalized stopped tails, and the proved gradient homogeneity.
-/
namespace krylov.Reference
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scaling the unknown operator leaves the actual searched gradient fixed.
Article: main_krylov, s7:N, positive reference normalization. -/
theorem searchedGradient_operator_smul (g d z : E) (c : ℝ) (hc : c≠0) :
    searchedGradient g d (c • z)=searchedGradient g d z := by
  have hs : lineLength g d (c • z)=lineLength g d z/c := by
    unfold lineLength
    rw [real_inner_smul_right]
    by_cases hz : inner ℝ d z=0
    · simp [hz]
    · field_simp
  rw [searchedGradient,hs,smul_smul,div_mul_cancel₀ _ hc]
  rfl

/-- A nonzero scalar change of the true quadratic operator preserves the
whole genuine CG gradient/direction state. Article: main_krylov, s7:N. -/
theorem cgRun_operator_smul (Q : E →L[ℝ] E) (c : ℝ) (hc : c≠0) (g : E) (i : ℕ) :
    cgRun (c • Q) g i=cgRun Q g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [cgRun,ih,cgAdvance,_root_.smul_apply,
      searchedGradient_operator_smul _ _ _ c hc]

/-- The genuine CG gradient is invariant under nonzero operator scaling.
Article: main_krylov, s7:N. -/
theorem gradient_operator_smul (Q : E →L[ℝ] E) (c : ℝ) (hc : c≠0) (g : E) (i : ℕ) :
    CG.gradient (c • Q) g i=CG.gradient Q g i :=
  congrArg CGState.gradient (cgRun_operator_smul Q c hc g i)

/-- Positive rescaling of the two normalized reference coordinates preserves
every genuine preterminal CG nonzero gradient. Article: main_krylov, s7:N. -/
theorem positive_scaled_reference_nondegenerate (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (a b : ℝ) (ha : 0<a) (hb : 0<b) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient Q g i≠0) :
    ∀ i<N, CG.gradient (a • Q) (b • g) i≠0 := by
  intro i hi
  rw [gradient_operator_smul Q a ha.ne',krylov.Nonlinear.reference_gradient_smul Q hQ hpos g b hb.ne' i]
  exact smul_ne_zero hb.ne' (hpre i hi)

end
end krylov.Reference
