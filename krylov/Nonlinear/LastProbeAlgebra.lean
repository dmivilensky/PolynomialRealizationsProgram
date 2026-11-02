import krylov.Nonlinear.AveragedComparison

/-!
Article: main_krylov, thm:RFCS, actual relative last-probe coefficient algebra.
Use: Preserve the original actual last-probe coefficient under genuine local function and measured-search estimates.
Source: exact actual averaged-Hessian congruence, convex query enclosure and proved scalar/norm inequalities.
-/

namespace krylov.Nonlinear
noncomputable section
open Set chebyshev1.Nonlinear
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The genuine line/probe endpoint distance factor is exactly the actual relative probe error times the true line-displacement norm.
Use: Retain the literal source factor |1-h/α| in the nonlinear leading coefficient.
Article: main_krylov, thm:RFCS, actual nonlinear last-probe leading coefficient.
Proof: Factor the true positive search length and use the actual real scalar norm.
-/
theorem line_probe_relative_norm (d : E) {α h : ℝ} (hα : 0<α) :
    |α-h| *‖d‖=|1-h/α| *‖α • d‖ := by
  have he : α-h=(1-h/α)*α := by field_simp
  rw [he,abs_mul,abs_of_pos hα,norm_smul,Real.norm_of_nonneg hα.le,mul_assoc]

omit [CompleteSpace E] in
/-- The genuine averaged full-step/probe mismatch is bounded by one half of the actual local Hessian Lipschitz constant times the real relative probe error and physical correction.
Use: Use the exact actual nonlinear last-probe factor before bounding only the cubic remainder.
Article: main_krylov, thm:RFCS, actual nonlinear last-probe leading coefficient.
Proof: Apply the proved actual segment mismatch inequality and the exact real line/probe relative-norm identity.
-/
theorem averaged_probe_relative_mismatch (A : E → E →L[ℝ] E) (x d w : E) (α h : ℝ)
    {L : ℝ≥0} {S : Set E} (hL : LipschitzOnWith L A S) (hα : 0<α)
    (ha : ∀ t∈Icc (0 : ℝ) 1, x+t • (α • d+w)∈S)
    (hh : ∀ t∈Icc (0 : ℝ) 1, x+t • (h • d)∈S) :
    ‖averagedDerivative A x (α • d+w)-averagedDerivative A x (h • d)‖≤
      (L : ℝ)/2*(|1-h/α| *‖α • d‖+‖w‖) := by
  simpa only [line_probe_relative_norm d hα] using averaged_probe_step_difference A x d w α h hL ha hh

end
end krylov.Nonlinear

namespace krylov.Nonlinear

/-- Uniformly bounded actual probe errors and reference steps preserve the exact relative-probe leading coefficient when multiplying genuine first-order Hessian and quadratic line/correction bounds.
Use: Assemble the source nonlinear leading coefficient while bounding only higher-order terms by uniform constants.
Article: main_krylov, thm:RFCS, actual nonlinear last-probe leading coefficient.
Proof: Separate the true leading product from the remaining quadratic terms and apply the given actual nonnegative uniform bounds; expand the finite real products exactly.
-/
theorem bounded_last_probe_product {m E Emax e M ℓ w a b ε : ℝ}
    (hE : 0≤E) (hEmax : E≤Emax) (he : 0≤e) (heM : e≤M) (ha : 0≤a) (hb : 0≤b)
    (hε : 0≤ε) (hε1 : ε≤1)
    (hm : m≤(1+a*ε)*(E*ℓ+w)) (hl : ℓ≤ε*e+b*ε^2) (hw : w≤b*ε^2) :
    m≤E*ε*e+(a*Emax*M+b*(Emax+1)*(1+a))*ε^2 := by
  let B := b*(Emax+1)
  have hEmax₀ : 0≤Emax := hE.trans hEmax
  have hM : 0≤M := he.trans heM
  have hB : 0≤B := by dsimp only [B]; positivity
  have hsum : E*ℓ+w≤E*ε*e+B*ε^2 := by
    have hs := add_le_add (mul_le_mul_of_nonneg_left hl hE) hw
    have hp := mul_le_mul_of_nonneg_right hEmax (show 0≤b*ε^2 by positivity)
    dsimp only [B]
    nlinarith
  have hlead : a*E*e≤a*Emax*M := by
    have hp := mul_le_mul_of_nonneg_left (mul_le_mul hEmax heM he hEmax₀) ha
    simpa only [mul_assoc] using hp
  have herr : a*B*ε≤a*B := by nlinarith [mul_le_mul_of_nonneg_left hε1 (mul_nonneg ha hB)]
  calc
    m ≤ (1+a*ε)*(E*ℓ+w) := hm
    _ ≤ (1+a*ε)*(E*ε*e+B*ε^2) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = E*ε*e+(a*E*e+B+a*B*ε)*ε^2 := by ring
    _ ≤ E*ε*e+(a*Emax*M+B+a*B)*ε^2 := by gcongr
    _ = _ := by dsimp only [B]; ring

end krylov.Nonlinear
