import krylov.OneGradient.InformedConstant
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), actual informed constant scaling.
Use: transfer genuine physical metric budget inflation to the original
K_X(c) coefficient with a quantified vanishing common multiplicative loss.
Source: the original attained scalar variational formula and exact
nonnegative square-root scaling; no maximizing parameter is prescribed.
-/

namespace krylov.OneGradient
noncomputable section

/-- Scaling all real informed budgets scales its genuine scalar
objective quadratically, including zero scale and all endpoint parameters.
Use: actual physical budget conversion retains the sharp leading constant.
Article: main_krylov, thm:local(b), exact informed objective homogeneity.
Proof: factor the real scale squared under the true square root and use
its nonnegative square-root identity; the remaining scalar equality is exact. -/
theorem informedObjective_scale (W w c a t : ℝ) (ht : 0≤t) :
    informedObjective (t*W) (t*w) (t*c) a=t^2*informedObjective W w c a := by
  have hs : Real.sqrt (a^2*(t*W)^2+(t*c+t*W*Real.sqrt (1-a^2))^2)=
      t*Real.sqrt (a^2*W^2+(c+W*Real.sqrt (1-a^2))^2) := by
    rw [show a^2*(t*W)^2+(t*c+t*W*Real.sqrt (1-a^2))^2=
      t^2*(a^2*W^2+(c+W*Real.sqrt (1-a^2))^2) by ring,
      Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq ht]
  rw [informedObjective,informedObjective,hs]
  ring

/-- The true attained informed constant is exactly homogeneous of degree
two in all three real source budgets, with the zero-scale case included.
Use: common physical budget inflation has its exact quadratic loss.
Article: main_krylov, thm:local(b), K_X budget homogeneity.
Proof: use the genuine attained variational maxima at both profiles;
the exact objective scaling gives both inequalities. -/
theorem informedConstant_scale (W w c t : ℝ) (ht : 0≤t) :
    informedConstant (t*W) (t*w) (t*c)=t^2*informedConstant W w c := by
  apply le_antisymm
  · obtain ⟨a,ha,hmax⟩ := (informedConstant_variational (t*W) (t*w) (t*c)).1
    rw [← hmax,informedObjective_scale W w c a t ht]
    exact mul_le_mul_of_nonneg_left ((informedConstant_variational W w c).2 a ha) (sq_nonneg t)
  · obtain ⟨a,ha,hmax⟩ := (informedConstant_variational W w c).1
    rw [← hmax,← informedObjective_scale W w c a t ht]
    exact (informedConstant_variational (t*W) (t*w) (t*c)).2 a ha

/-- Increasing the nonnegative genuine prior radius cannot decrease
the informed constant, with all nonnegative query/output profiles included.
Use: compare the actual metric-inflated prior with its true source prior.
Article: main_krylov, thm:local(b), true prior monotonicity.
Proof: the real hidden diagonal radius is nonnegative. Its square and
true square root increase with the prior; maximize the actual objective. -/
theorem informedConstant_mono_prior (W w c d : ℝ)
    (hW : 0≤W) (hw : 0≤w) (hc : 0≤c) (hcd : c≤d) :
    informedConstant W w c≤ informedConstant W w d := by
  obtain ⟨a,ha,hmax⟩ := (informedConstant_variational W w c).1
  have hs : 0≤W*Real.sqrt (1-a^2) := mul_nonneg hW (Real.sqrt_nonneg _)
  have hsq : (c+W*Real.sqrt (1-a^2))^2≤(d+W*Real.sqrt (1-a^2))^2 :=
    sq_le_sq₀ (add_nonneg hc hs) (by linarith) |>.mpr (add_le_add hcd le_rfl)
  have hobj : informedObjective W w c a≤ informedObjective W w d a := by
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (add_le_add le_rfl hsq)) hw)
  rw [← hmax]
  exact hobj.trans ((informedConstant_variational W w d).2 a ha)

/-- A common genuine metric inflation of query/output budgets by s≥1
costs at most s² times the original informed source constant, retaining
the uninflated actual prior radius.
Use: source-wide known-metric budget conversion has the same leading K_X(c).
Article: main_krylov, thm:local(b), quantified physical budget inflation.
Proof: increase only the prior to s*c, then apply the exact three-budget
homogeneity. All original zero budget corners remain valid. -/
theorem informedConstant_inflated_budgets (W w c s : ℝ)
    (hW : 0≤W) (hw : 0≤w) (hc : 0≤c) (hs : 1≤s) :
    informedConstant (s*W) (s*w) c≤s^2*informedConstant W w c := by
  have hs0 : 0≤s := by linarith
  have hcs : c≤s*c := by nlinarith
  exact (informedConstant_mono_prior (s*W) (s*w) c (s*c)
    (mul_nonneg hs0 hW) (mul_nonneg hs0 hw) hc hcs).trans_eq (informedConstant_scale W w c s hs0)

end
end krylov.OneGradient
