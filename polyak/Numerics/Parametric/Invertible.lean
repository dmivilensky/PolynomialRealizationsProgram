import polyak.Numerics.Parametric.Weighted
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
Article: Appendix B, nonsingularity from the checked norm defect.
Use: the same contraction estimate proves invertibility of the actual
unknown-coordinate derivative; no unrelated matrix is used as an IFT hypothesis.
-/
noncomputable section
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

theorem isInvertible_of_defect {n : ℕ}
    (R D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (h : ‖ContinuousLinearMap.id ℝ _-R.comp D‖<1) : D.IsInvertible := by
  have hinj : Function.Injective D := by
    intro v w he
    have hz : D (v-w)=0 := by simp only [map_sub,he,sub_self]
    have ht : (ContinuousLinearMap.id ℝ (Fin n → ℝ)-R.comp D) (v-w)=v-w := by simp [hz]
    have hb := (ContinuousLinearMap.id ℝ (Fin n → ℝ)-R.comp D).le_opNorm (v-w)
    rw [ht] at hb
    have heq : ‖v-w‖=0 := by nlinarith [norm_nonneg (v-w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp heq)
  have hsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective (f := D.toLinearMap)).mp hinj
  refine ⟨(LinearEquiv.ofBijective D.toLinearMap ⟨hinj,hsurj⟩).toContinuousLinearEquiv,?_⟩
  ext v i
  rfl

theorem newton_fderiv {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) (s : ℝ) (x : Fin n → ℝ) :
    fderiv ℝ (newton Y F s) x=ContinuousLinearMap.id ℝ _-
      (matrixCLM Y).comp (fderiv ℝ (system F s) x) := by
  have hF := (system_differentiable F h s).differentiableAt.hasFDerivAt (x := x)
  exact ((hasFDerivAt_id x).sub ((matrixCLM Y).hasFDerivAt.comp x hF)).fderiv

theorem unknown_derivative_isInvertible {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℚ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) (I : IntervalRat)
    (X : Fin n → IntervalRat) {s : ℝ} {x : Fin n → ℝ}
    (hs : s∈I) (hx : FinBoxMem x X) (cfg : EvalConfig)
    (hq : intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F I X cfg))<1) :
    (fderiv ℝ (system F s) x).IsInvertible := by
  apply isInvertible_of_defect (matrixCLM (Y.map fun q => (q : ℝ)))
  rw [← newton_fderiv _ F h]
  exact (newton_fderiv_norm_le Y F h I X hs hx cfg).trans_lt (by exact_mod_cast hq)

theorem check_derivative_isInvertible {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (X : Fin n → IntervalRat) (cert : Certificate n) (cfg : EvalConfig)
    (hc : check F I X cert cfg=true) {s : ℝ} {x : Fin n → ℝ}
    (hs : s∈I) (hx : FinBoxMem x X) : (fderiv ℝ (system F s) x).IsInvertible := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  exact unknown_derivative_isInvertible cert.preconditioner F
    (fun i => ((F i).checkADSupported_eq_true_iff).mp (hc.1.1.1.1 i)) I X hs hx cfg hc.1.2

end polyak.Numerics.Parametric
