import krylov.Correction.ConstantBounds

/-!
Article: main_krylov, thm:C2(b,c), the informed-base and two-correction scalar maxima.
Use: prove the actual maximizer and exact cubic constant before constructing
the corresponding admissible matrix and information-fibre witnesses.
Source: elementary factorization of the cubic objective around its unique maximum.
-/

namespace krylov.Correction
noncomputable section

/-- The interior parameter attaining the informed-base cubic tradeoff.
Use: both the known-base information radius and the double-correction witness use it.
Article: main_krylov, thm:C2(b,c), t=1/√3. -/
def cubicMaximizer : ℝ := (Real.sqrt 3)⁻¹

/-- The cubic maximizing parameter is positive, at most one, and has square 1/3.
Use: justify the actual interior attaining witness and every reciprocal normalization.
Article: main_krylov, thm:C2(b,c), admissibility of t=1/√3.
Proof: square the positive square root, invert its nonzero value and compare squares. -/
theorem cubicMaximizer_spec : 0 < cubicMaximizer ∧ cubicMaximizer ≤ 1 ∧
    cubicMaximizer^2=1/3 := by
  have hr : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs : (Real.sqrt 3)^2=(3 : ℝ) := Real.sq_sqrt (by norm_num)
  have ha : 0 < cubicMaximizer := inv_pos.mpr hr
  have he : cubicMaximizer^2=1/3 := by rw [cubicMaximizer,inv_pow,hs]; norm_num
  exact ⟨ha,by nlinarith,he⟩

/-- The cubic objective has the sharp informed-base maximum 2/(3√3).
Use: the consistency-interval half-width produces this exact scalar constant.
Article: main_krylov, thm:C2(c), max t(1−t²)=2/(3√3).
Proof: the objective gap factors as (t−a)²(t+2a), where a²=1/3. -/
theorem cubic_tradeoff_max {t : ℝ} (ht : 0 ≤ t) :
    t*(1-t^2) ≤ 2/(3*Real.sqrt 3) := by
  -- The factored objective gap is nonnegative on the entire nonnegative half-line.
  obtain ⟨ha,_,ha₂⟩ := cubicMaximizer_spec
  have hp := mul_nonneg (sq_nonneg (t-cubicMaximizer)) (by linarith : 0 ≤ t+2*cubicMaximizer)
  have ht₂ := congrArg (fun x : ℝ => t*x) ha₂
  have ha₃ := congrArg (fun x : ℝ => cubicMaximizer*x) ha₂
  have hbound : t*(1-t^2) ≤ 2*cubicMaximizer/3 := by nlinarith
  have he : 2*cubicMaximizer/3=2/(3*Real.sqrt 3) := by
    unfold cubicMaximizer
    ring
  exact hbound.trans_eq he

/-- The explicit cubic parameter attains the printed informed-base constant.
Use: turn the scalar upper estimate into an attained maximum.
Article: main_krylov, thm:C2(b,c), equality at 1/√3.
Proof: substitute the already proved square 1/3 and normalize the inverse factor. -/
theorem cubic_tradeoff_attained :
    cubicMaximizer*(1-cubicMaximizer^2)=2/(3*Real.sqrt 3) := by
  rw [cubicMaximizer_spec.2.2]
  unfold cubicMaximizer
  ring

/-- On the nonnegative unit circle the repeated-correction coefficient has the same exact maximum.
Use: the concrete RFC₂ witness has coefficient ab² with a²+b²=1.
Article: main_krylov, thm:C2(b), ab²≤2/(3√3).
Proof: eliminate b² through the circle identity and use the proved cubic bound. -/
theorem double_correction_scalar {a b : ℝ} (ha : 0 ≤ a) (hab : a^2+b^2=1) :
    a*b^2 ≤ 2/(3*Real.sqrt 3) := by
  rw [show b^2=1-a^2 by linarith]
  exact cubic_tradeoff_max ha

end
end krylov.Correction
