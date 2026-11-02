import krylov.OneGradient.TwoModelUniformLower
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), finite reference-normalized four-model loss.
Use: absorb arbitrary query mismatch into an explicit finite lower bound,
without subsequence arguments, regular policy limits or bounded outputs.
Source: actual two-model residual control and opposite-increment
seminorm cancellation, followed by the true reference triangle inequality.
-/

namespace krylov.OneGradient
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The free output perturbation controls the arbitrary common reference
residual in the actual opposite-centre games, uniformly over both outputs.
Use: query mismatch need not already be of order omega in a lower proof.
Article: main_krylov, thm:local(c), finite reference-mismatch control.
Proof: control both actual incoming residual norms by their real games.
The triangle inequality for their sum removes the opposite increment. -/
theorem twoModelRisk_uniform_reference_residual
    (Cp Cm D : E →L[ℝ] E) (r z up um : E) (eta w : ℝ) (heta : 0≤ eta) (hw : 0≤ w)
    (hp : ‖Cp‖≤1+eta) (hm : ‖Cm‖≤1+eta) :
    w*‖r‖≤(1+eta+w)*
      max (twoModelRisk Cp D (r+z) up w) (twoModelRisk Cm D (r-z) um w) := by
  let R := max (twoModelRisk Cp D (r+z) up w) (twoModelRisk Cm D (r-z) um w)
  have hJ : 0≤1+eta+w := by positivity
  have hpoint (C : E →L[ℝ] E) (hC : ‖C‖≤1+eta) (rho u : E)
      (hR : twoModelRisk C D rho u w≤ R) : w*‖rho‖≤(1+eta+w)*R := by
    have hRn : 0≤ twoModelRisk C D rho u w :=
      (by positivity : 0≤‖D u‖+w*‖u‖).trans (twoModelRisk_bounds C D rho u w).2
    exact (twoModelRisk_residual_lower C D rho u w hw).trans
      ((mul_le_mul_of_nonneg_right (by linarith : w+‖C‖≤1+eta+w) hRn).trans
        (mul_le_mul_of_nonneg_left hR hJ))
  have hplus := hpoint Cp hp (r+z) up (le_max_left _ _)
  have hminus := hpoint Cm hm (r-z) um (le_max_right _ _)
  have hs : (r+z)+(r-z)=(2 : ℝ) • r := by simp only [two_smul];abel
  have hr := norm_add_le (r+z) (r-z)
  rw [hs,norm_smul,Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤2)] at hr
  dsimp only [R] at *
  nlinarith [mul_le_mul_of_nonneg_left hr hw]

/-- A genuine reference-length triangle bound and the exact increment
coefficient yield a finite four-model lower bound, uniformly over every
pair of arbitrary common-data outputs. Its coefficient tends to one when
eta and the output radius are proportional to omega and t to omega².
Use: original M1 minimax limits require neither CG consistency nor a
regular last-query direction, and cover even degenerate or huge queries.
Article: main_krylov, thm:local(c), finite reference-normalized obstruction.
Proof: the opposite games retain the full true increment seminorm. The
independent output radius controls their common reference mismatch. Add
both actual inequalities using the genuine reference-length triangle bound. -/
theorem twoModelRisk_uniform_reference_lower
    (Cp Cm D : E →L[ℝ] E) (r z up um : E) (eta w t q sigma : ℝ)
    (heta : 0≤ eta) (hw : 0< w) (ht : 0≤ t)
    (hD : ‖D‖≤ eta)
    (hp : ‖Cp-ContinuousLinearMap.id ℝ E‖≤ eta)
    (hm : ‖Cm-ContinuousLinearMap.id ℝ E‖≤ eta)
    (hpn : ‖Cp‖≤1+eta) (hmn : ‖Cm‖≤1+eta)
    (hgeom : sigma≤ q+‖r‖) (hlead : t*q≤‖D z‖+w*‖z‖) :
    t*sigma≤(1+(eta+w)+(eta+w)*eta/w+t/w*(1+eta+w))*
      max (twoModelRisk Cp D (r+z) up w) (twoModelRisk Cm D (r-z) um w) := by
  let R := max (twoModelRisk Cp D (r+z) up w) (twoModelRisk Cm D (r-z) um w)
  let K := 1+(eta+w)+(eta+w)*eta/w
  let J := 1+eta+w
  have hlead' : t*q≤ K*R := hlead.trans
    (twoModelRisk_uniform_outer_lower Cp Cm D r z up um eta w heta hw hD hp hm)
  have hr : w*‖r‖≤ J*R :=
    twoModelRisk_uniform_reference_residual Cp Cm D r z up um eta w heta hw.le hpn hmn
  have hr' : ‖r‖≤ J*R/w := (le_div_iff₀ hw).mpr (by nlinarith)
  have htr := mul_le_mul_of_nonneg_left hr' ht
  have htgeom := mul_le_mul_of_nonneg_left hgeom ht
  have heq : t*(J*R/w)=(t/w*J)*R := by ring
  rw [heq] at htr
  change _≤(K+t/w*J)*R
  nlinarith

end
end krylov.OneGradient
