import krylov.OneGradient.TwoModelRisk
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), finite uniform arbitrary-policy loss.
Use: remove both the unknown common residual and any assumed boundedness
or limiting regularity of a competing output before taking minimax limits.
Source: true two-model norm bounds and the triangle inequality for the
actual hidden-action/output-defect seminorm.
-/

namespace krylov.OneGradient
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The free output-defect radius controls the entire actual incoming
residual at an arbitrary common output, with a finite inverse-free loss.
Use: no finite-risk, small-output or limiting-policy hypothesis is needed
to control the reference-mismatch part of a competing execution.
Article: main_krylov, thm:local(c), finite residual control.
Proof: split the incoming residual into the true centre residual minus
the centre action. The actual game bounds control both terms after
multiplication by the positive output radius. -/
theorem twoModelRisk_residual_lower (C D : E →L[ℝ] E) (rho u : E)
    (w : ℝ) (hw : 0≤ w) :
    w*‖rho‖≤(w+‖C‖)*twoModelRisk C D rho u w := by
  let R := twoModelRisk C D rho u w
  have hb := (twoModelRisk_bounds C D rho u w).1
  have hu : w*‖u‖≤ R := by
    change w*‖u‖≤ twoModelRisk C D rho u w
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans hb
  have hv : ‖rho+C u‖≤ R := by nlinarith [norm_nonneg u]
  have hr : ‖rho‖≤‖rho+C u‖+‖C u‖ := by
    have hs : rho=(rho+C u)-C u := by abel
    calc
      ‖rho‖=‖(rho+C u)-C u‖ := congrArg norm hs
      _ ≤ _ := norm_sub_le _ _
  have hfirst := mul_le_mul_of_nonneg_left hr hw
  have hsecond := mul_le_mul_of_nonneg_left (C.le_opNorm u) hw
  have hthird := mul_le_mul_of_nonneg_left hv hw
  have hfourth := mul_le_mul_of_nonneg_left hu (norm_nonneg C)
  dsimp only [R] at *
  nlinarith

/-- Opposite observed increments retain their full hidden/output
seminorm after an arbitrary common reference residual is added.
Use: the genuine four-scenario construction removes the unknown first
and second query mismatch without assuming CG consistency.
Article: main_krylov, thm:local(c), outer-sign cancellation.
Proof: the difference of the actual two vectors is twice the increment.
Apply the triangle inequality separately to its hidden action and norm,
and combine the two inequalities before taking their common maximum. -/
theorem twoModelRisk_outer_seminorm (D : E →L[ℝ] E) (r z : E)
    (w : ℝ) (hw : 0≤ w) :
    ‖D z‖+w*‖z‖≤max (‖D (r+z)‖+w*‖r+z‖) (‖D (r-z)‖+w*‖r-z‖) := by
  have hs : (r+z)-(r-z)=(2 : ℝ) • z := by simp only [two_smul];abel
  have hz := norm_sub_le (r+z) (r-z)
  have hd := norm_sub_le (D (r+z)) (D (r-z))
  rw [← map_sub,hs,map_smul,norm_smul,Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤2)] at hd
  rw [hs,norm_smul,Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤2)] at hz
  have h1 := le_max_left (‖D (r+z)‖+w*‖r+z‖) (‖D (r-z)‖+w*‖r-z‖)
  have h2 := le_max_right (‖D (r+z)‖+w*‖r+z‖) (‖D (r-z)‖+w*‖r-z‖)
  nlinarith [mul_le_mul_of_nonneg_left hz hw]

/-- The two genuine opposite centre games give a uniform finite lower
bound for their exact hidden increment seminorm, at arbitrary separate
common-data outputs. All losses depend only on actual operator budgets.
Use: the original four-adversary minimax proof has no output-rate premise.
Article: main_krylov, thm:local(c), finite outer-sign game bound.
Proof: the actual centred game lower bound holds at both outputs. Bound
its real coefficient by the shared operator budgets, then cancel the
arbitrary reference residual by the genuine seminorm reflection bound. -/
theorem twoModelRisk_uniform_outer_lower
    (Cp Cm D : E →L[ℝ] E) (r z up um : E) (eta w : ℝ) (heta : 0≤ eta) (hw : 0< w)
    (hD : ‖D‖≤ eta)
    (hp : ‖Cp-ContinuousLinearMap.id ℝ E‖≤ eta)
    (hm : ‖Cm-ContinuousLinearMap.id ℝ E‖≤ eta) :
    ‖D z‖+w*‖z‖≤(1+(eta+w)+(eta+w)*eta/w)*
      max (twoModelRisk Cp D (r+z) up w) (twoModelRisk Cm D (r-z) um w) := by
  let K := 1+(eta+w)+(eta+w)*eta/w
  let R := max (twoModelRisk Cp D (r+z) up w) (twoModelRisk Cm D (r-z) um w)
  have hK : 0≤ K := by dsimp only [K];positivity
  have hcoef (C : E →L[ℝ] E) (hC : ‖C-ContinuousLinearMap.id ℝ E‖≤ eta) :
      1+(‖D‖+w)+(‖D‖+w)*‖C-ContinuousLinearMap.id ℝ E‖/w≤ K := by
    have hh := mul_le_mul (add_le_add hD (le_refl w)) hC (norm_nonneg _) (by positivity : 0≤ eta+w)
    have hdiv := div_le_div_of_nonneg_right hh hw.le
    dsimp only [K]
    linarith
  have hpoint (C : E →L[ℝ] E) (hC : ‖C-ContinuousLinearMap.id ℝ E‖≤ eta)
      (rho u : E) (hR : twoModelRisk C D rho u w≤ R) :
      ‖D rho‖+w*‖rho‖≤ K*R := by
    have hRn : 0≤ twoModelRisk C D rho u w :=
      (by positivity : 0≤‖D u‖+w*‖u‖).trans (twoModelRisk_bounds C D rho u w).2
    exact (twoModelRisk_centred_lower C D rho u w hw).trans
      ((mul_le_mul_of_nonneg_right (hcoef C hC) hRn).trans (mul_le_mul_of_nonneg_left hR hK))
  exact (twoModelRisk_outer_seminorm D r z w hw.le).trans
    (max_le (hpoint Cp hp (r+z) up (le_max_left _ _))
      (hpoint Cm hm (r-z) um (le_max_right _ _)))

end
end krylov.OneGradient
