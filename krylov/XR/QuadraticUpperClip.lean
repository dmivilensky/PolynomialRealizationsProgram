import krylov.XR.LocalSpectralBand

/-!
Article: main_krylov, prop:floor, upper clip on genuine quadratic data.
Use: apply the actual raw shifted-Schur coefficient to the actual true
quadratic curvature. Its consistency bound is proved from the true
observed images, not supplied as a premise. Source: physical Radau
completion at zero variation and scalar upper-interval projection.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Reference krylov.Secant
open krylov.Methods hiding unitWindow unitWindow_norm unitWindow_diagonal_unit
open krylov.Convergence
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The literal upper Schur clip cannot increase the true quadratic trial
error on any independent observed window and conjugate new direction. -/
theorem rawQuadratic_upper_clip_trial_error
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (hs : ∀ i, s i ≠ 0)
    (d : EuclideanSpace ℝ (Fin n)) (hd : d ≠ 0)
    (a b upper sigma : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb₀ : 0 < b)
    (hupper : b < upper) (hsigma : 0 < sigma) (hsigma₁ : sigma ≤ 1)
    (hpositive : ∀ v : EuclideanSpace ℝ (Fin n), a*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hnorm : ‖cgOperator base‖ ≤ b)
    (hgain : ∀ c : Fin p → ℝ, sigma^2*‖WithLp.toLp 2 c‖^2 ≤
      ‖combine (unitWindow s) c‖^2)
    (hconjugate : ∀ i, inner ℝ (cgOperator base (s i)) d = 0)
    (estimate : ℝ) (he : 0 < estimate) :
    |1-inner ℝ d (cgOperator base d) /
      min estimate (upperConsistencyCoefficient s
        (latest (crossGram s (fun i => cgOperator base (s i)))) d upper * ‖d‖^2)| ≤
      |1-inner ℝ d (cgOperator base d) / estimate| := by
  have hband := operator_bounds_spectral_band base hb a b hpositive hnorm
  have hhalf : 0 < a-a/2 := by linarith
  have hgap : 0 < upper-b := sub_pos.mpr hupper
  have hq := rawWindow_upper_consistency_adequate base hb.isHermitian s
    (fun i => cgOperator base (s i)) hs d hd a b upper sigma 0 ha hab hupper hb₀ hsigma hsigma₁
    (by norm_num) hband.1 hband.2 hpositive hnorm hgain
    (by intro i; simp only [sub_self, norm_zero, zero_mul]; exact le_rfl) hconjugate
    (by simpa only [mul_zero] using (by positivity : (0 : ℝ) ≤ a*sigma^2/2))
    (by simpa only [mul_zero] using (mul_pos hhalf (by positivity : 0 < a*sigma^2/(2*b))))
    (by simpa only [mul_zero] using (mul_pos hgap (by positivity : 0 < a*sigma^2/(2*b))))
  exact upper_clip_trial_error ((cgOperator_positive base hb).2 d hd) hq.2.1 he

end
end krylov.XR
