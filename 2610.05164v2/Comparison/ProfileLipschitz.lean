import «2610.05164v2».Comparison.ProfilePotentials
import «2610.05164v2».Comparison.Triangle
import Mathlib.Analysis.Normed.Operator.Prod

/-!
Article: 2610.05164v2, Theorem 3.4.
Closed-triangle Lipschitz potentials for every Definition 10 profile.
Use: `«2610.05164v2».Comparison.Profile.tracePotential_lipschitz` feeds
`«2610.05164v2».Comparison.Profile.traceAlong_locallyAC` (trace Along locally AC).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_trace_comparison` — 2610.05164v2, Theorem
3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Filters «2610.05164v2».Comparison
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : «2610.05164v2».Comparison.Profile κ) (hκ : 0 < κ)

/--
Defines `determinantGradientQ` of type `ℝ` by `-(r*P.rightFilter hκ s q+s*(P.amplitude q)^2)/
(P.speed q*(2+r+P.rightFilter hκ s q))`.

Use: `«2610.05164v2».Comparison.Profile.determinantGradientQ_bound` uses this definition to
establish the stated quantitative bound `‖P.determinantGradientQ hκ s q r‖ ≤
(s/κ)^2*P.C*P.amplitudeBound+s*P.C`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def determinantGradientQ (s q r : ℝ) : ℝ :=
  -(r*P.rightFilter hκ s q+s*(P.amplitude q)^2)/
    (P.speed q*(2+r+P.rightFilter hκ s q))
/--
Defines `determinantGradientR` of type `ℝ` by `1/(2+r+P.rightFilter hκ s q)`.

Use: `«2610.05164v2».Comparison.Profile.determinantGradientR_bound` uses this definition to
establish the stated quantitative bound `‖P.determinantGradientR hκ s q r‖ ≤ 1`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def determinantGradientR (s q r : ℝ) : ℝ := 1/(2+r+P.rightFilter hκ s q)
/--
Defines `determinantLipschitzConstant` of type `ℝ` by `(s/κ)^2*P.C*P.amplitudeBound+s*P.C+1`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_lipschitz` rewrites with this
definition to establish the displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal
(P.determinantLipschitzConstant s)) (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2)
(filterTriangle (s/κ))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def determinantLipschitzConstant (s : ℝ) : ℝ := (s/κ)^2*P.C*P.amplitudeBound+s*P.C+1

/--
The stated quantitative bound `‖P.determinantGradientQ hκ s q r‖ ≤
(s/κ)^2*P.C*P.amplitudeBound+s*P.C`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_lipschitz` uses this bound to
establish the displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal
(P.determinantLipschitzConstant s)) (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2)
(filterTriangle (s/κ))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.rightFilter_bounds`,
`«2610.05164v2».Comparison.Profile.speed_pos`,
`«2610.05164v2».Comparison.Profile.Q_div_speed_le_bound` with the arguments shown in the proof.
-/
theorem determinantGradientQ_bound {s q r : ℝ} (hs : 0 ≤ s)
    (hq : q ∈ Ioo (0:ℝ) 2) (hr : r ∈ Icc (0:ℝ) (s/κ*q)) :
    ‖P.determinantGradientQ hκ s q r‖ ≤ (s/κ)^2*P.C*P.amplitudeBound+s*P.C := by
  -- Use the identities/estimates `«2610.05164v2».Comparison.Profile.rightFilter_bounds`,
  -- `«2610.05164v2».Comparison.Profile.speed_pos`,
  -- `«2610.05164v2».Comparison.Profile.Q_div_speed_le_bound` with the arguments shown in the
  -- proof.
  have hR := P.rightFilter_bounds hκ hs ⟨hq.1.le,hq.2.le⟩
  have hd := P.speed_pos hq
  have ha : 0 ≤ s/κ := div_nonneg hs hκ.le
  have hprod : r*P.rightFilter hκ s q ≤ (s/κ)^2*«2610.05164v2».Calibration.Q q := by
    have h := mul_le_mul hr.2 hR.2 hR.1 (mul_nonneg ha hq.1.le)
    convert h using 1
    unfold «2610.05164v2».Calibration.Q
    ring
  have hQ := (div_le_iff₀ hd).mp (P.Q_div_speed_le_bound hq)
  have hν := (div_le_iff₀ hd).mp (P.ratio_bounds hq).1
  have h1 := mul_le_mul_of_nonneg_left hQ (sq_nonneg (s/κ))
  have h2 := mul_le_mul_of_nonneg_left hν hs
  have hsum : r*P.rightFilter hκ s q+s*(P.amplitude q)^2 ≤
      ((s/κ)^2*P.C*P.amplitudeBound+s*P.C)*P.speed q := by nlinarith
  have hK : 0 ≤ (s/κ)^2*P.C*P.amplitudeBound+s*P.C := by
    have hC := P.C_positive.le
    have hM := P.amplitudeBound_positive.le
    positivity
  unfold determinantGradientQ
  rw [norm_div,norm_neg,Real.norm_of_nonneg
    (add_nonneg (mul_nonneg hr.1 hR.1) (mul_nonneg hs (sq_nonneg _))),
      Real.norm_of_nonneg (mul_nonneg hd.le (by linarith [hr.1,hR.1]))]
  apply (div_le_iff₀ (mul_pos hd (by linarith [hr.1,hR.1]))).2
  have he := mul_nonneg (mul_nonneg hK hd.le)
    (show 0 ≤ 1+r+P.rightFilter hκ s q by linarith [hr.1,hR.1])
  exact hsum.trans (by nlinarith [he])

/--
The stated quantitative bound `‖P.determinantGradientR hκ s q r‖ ≤ 1`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_lipschitz` uses this bound to
establish the displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal
(P.determinantLipschitzConstant s)) (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2)
(filterTriangle (s/κ))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.rightFilter_bounds` with
the arguments shown in the proof.
-/
theorem determinantGradientR_bound {s q r : ℝ} (hs : 0 ≤ s)
    (hq : q ∈ Icc (0:ℝ) 2) (hr : 0 ≤ r) :
    ‖P.determinantGradientR hκ s q r‖ ≤ 1 := by
  have hR := P.rightFilter_bounds hκ hs hq
  unfold determinantGradientR
  rw [Real.norm_of_nonneg (div_nonneg (by norm_num) (by linarith [hR.1]))]
  exact (div_le_one (by linarith [hR.1])).2 (by linarith [hR.1])

/--
The actual Fréchet derivative: `HasFDerivAt (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1
p.2) (P.determinantGradientQ hκ s p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ+
P.determinantGradientR hκ s p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_lipschitz` uses this Fréchet
derivative formula to establish the displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal
(P.determinantLipschitzConstant s)) (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2)
(filterTriangle (s/κ))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem determinantPotential_fderiv {s : ℝ} (hs : 0 ≤ s) {p : ℝ × ℝ}
    (hq : p.1 ∈ Ioo (0:ℝ) 2) (hr : 0 ≤ p.2) :
    HasFDerivAt (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2)
      (P.determinantGradientQ hκ s p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ+
       P.determinantGradientR hκ s p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hR := P.rightFilter_bounds hκ hs ⟨hq.1.le,hq.2.le⟩
  have hn : 2+p.2+P.rightFilter hκ s p.1 ≠ 0 := ne_of_gt (by linarith [hR.1])
  have hL := (P.determinantL_derivative hκ hs hq).hasFDerivAt.comp p hasFDerivAt_fst
  have hF := (P.rightFilter_derivative hκ hs hq).hasFDerivAt.comp p hasFDerivAt_fst
  have hS : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have h := hL.add ((((hS.const_add (2:ℝ)).add hF).mul_const (1/2:ℝ)).log
    (mul_ne_zero hn (by norm_num)))
  convert! h using 1
  · funext z
    simp only [determinantPotential,Pi.add_apply,Function.comp_apply,div_eq_mul_inv,one_mul]
  · apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply,smul_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,
      Pi.add_apply,Function.comp_apply]
    change P.determinantGradientQ hκ s p.1 p.2*v.1+
      P.determinantGradientR hκ s p.1 p.2*v.2=_
    unfold determinantGradientQ determinantGradientR
    field_simp [(P.speed_pos hq).ne',hn]
    dsimp only [ContinuousLinearMap.fst,ContinuousLinearMap.snd,LinearMap.fst,LinearMap.snd]
    ring_nf
    rfl

/--
Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => P.determinantPotential hκ s
p.1 p.2) (filterTriangle (s/κ))`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_lipschitz` uses this continuity
result to establish the displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal
(P.determinantLipschitzConstant s)) (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2)
(filterTriangle (s/κ))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_continuous`,
`«2610.05164v2».Filters.reflected_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem determinantPotential_continuousOn {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2)
      (filterTriangle (s/κ)) := by
  -- Establish continuity hR before using the function at limits or in calculus arguments.
  have hR : Continuous (P.rightFilter hκ s) :=
    (nonlinear_continuous
      (reflected_integrable ((P.speedData hκ).density_integrable hκ))
      (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs).comp
        (P.speedData hκ).X_continuous.neg
  -- Establish continuity hL before using the function at limits or in calculus arguments.
  have hL : Continuous (P.determinantL hκ s) :=
    ((jost_c1
      (reflected_integrable ((P.speedData hκ).density_integrable hκ))
      (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs).continuous.log
        (fun x => (jost_positive
          (reflected_integrable ((P.speedData hκ).density_integrable hκ))
          (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs x).ne')).comp
            (P.speedData hκ).X_continuous.neg
  apply (hL.comp continuous_fst).continuousOn.add
  apply ContinuousOn.log
  · exact ((continuous_const.add continuous_snd).add (hR.comp continuous_fst)).div_const 2 |>.continuousOn
  · intro p hp
    have hb := P.rightFilter_bounds hκ hs hp.1
    change (2+p.2+P.rightFilter hκ s p.1)/2 ≠ 0
    exact div_ne_zero (ne_of_gt (by linarith [hp.2.1,hb.1])) (by norm_num)

/--
The displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal (P.determinantLipschitzConstant
s)) (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2) (filterTriangle (s/κ))`.

Use: `«2610.05164v2».Comparison.Profile.determinantAlong_locallyAC` uses this identity to
establish absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(determinantAlong G P (s := s)) a b`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.filterTriangle_convex`,
`«2610.05164v2».Comparison.Profile.determinantPotential_fderiv`,
`«2610.05164v2».Comparison.Profile.C_positive` with the arguments shown in the proof.
-/
theorem determinantPotential_lipschitz {s : ℝ} (hs : 0 ≤ s) :
    LipschitzOnWith (Real.toNNReal (P.determinantLipschitzConstant s))
      (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2) (filterTriangle (s/κ)) := by
  -- Use the identities/estimates `«2610.05164v2».Comparison.filterTriangle_convex`,
  -- `«2610.05164v2».Comparison.Profile.determinantPotential_fderiv`,
  -- `«2610.05164v2».Comparison.Profile.C_positive` with the arguments shown in the proof.
  let T := filterTriangle (s/κ) ∩ {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 2}
  have hT : Convex ℝ T := (filterTriangle_convex _).inter
    ((convex_Ioo (0:ℝ) 2).linear_preimage (LinearMap.fst ℝ ℝ ℝ))
  have hLip : LipschitzOnWith (Real.toNNReal (P.determinantLipschitzConstant s))
      (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2) T := by
    apply hT.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun p hp => (P.determinantPotential_fderiv hκ hs hp.2 hp.1.2.1).hasFDerivWithinAt)
    intro p hp
    apply NNReal.coe_le_coe.mp
    change ‖P.determinantGradientQ hκ s p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ+
       P.determinantGradientR hκ s p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤
      (Real.toNNReal (P.determinantLipschitzConstant s) : ℝ)
    rw [Real.toNNReal_of_nonneg (by unfold determinantLipschitzConstant; have hC := P.C_positive.le; have hM := P.amplitudeBound_positive.le; positivity)]
    calc
      _ ≤ ‖P.determinantGradientQ hκ s p.1 p.2‖+‖P.determinantGradientR hκ s p.1 p.2‖ := by
        apply (norm_add_le _ _).trans
        simp only [norm_smul,ContinuousLinearMap.norm_fst,ContinuousLinearMap.norm_snd,mul_one]
        exact le_rfl
      _ ≤ P.determinantLipschitzConstant s := add_le_add
        (P.determinantGradientQ_bound hκ hs hp.2 ⟨hp.1.2.1,hp.1.2.2⟩)
        (P.determinantGradientR_bound hκ hs hp.1.1 hp.1.2.1)
  have hcl : closure T=filterTriangle (s/κ) := filterTriangle_closure_strip (div_nonneg hs hκ.le)
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousOn (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2) (closure T) := by
    rw [hcl]
    exact P.determinantPotential_continuousOn hκ hs
  simpa only [hcl] using hLip.closure hc

end
end «2610.05164v2».Comparison.Profile

namespace «2610.05164v2».Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Comparison
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : «2610.05164v2».Comparison.Profile κ) (hκ : 0 < κ)

/--
Defines `traceGradientQ` of type `ℝ` by `(2*r*P.rightLinear hκ q-κ*(P.amplitude
q)^2*(r+P.rightLinear hκ q))/(2*P.speed q)`.

Use: `«2610.05164v2».Comparison.Profile.traceGradientQ_bound` uses this definition to establish
the stated quantitative bound `‖P.traceGradientQ hκ q r‖ ≤ P.C*P.amplitudeBound+κ*P.C`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def traceGradientQ (q r : ℝ) : ℝ :=
  (2*r*P.rightLinear hκ q-κ*(P.amplitude q)^2*(r+P.rightLinear hκ q))/(2*P.speed q)
/--
Defines `traceGradientR` of type `ℝ` by `(r+P.rightLinear hκ q)/2`.

Use: `«2610.05164v2».Comparison.Profile.traceGradientR_bound` uses this definition to establish
the stated quantitative bound `‖P.traceGradientR hκ q r‖ ≤ 1`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def traceGradientR (q r : ℝ) : ℝ := (r+P.rightLinear hκ q)/2

/--
The stated quantitative bound `‖P.traceGradientQ hκ q r‖ ≤ P.C*P.amplitudeBound+κ*P.C`.

Use: `«2610.05164v2».Comparison.Profile.tracePotential_lipschitz` uses this bound to establish
the displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal (P.C*P.amplitudeBound+κ*P.C+1))
(fun p : ℝ × ℝ => P.tracePotential hκ p.1 p.2) (filterTriangle 1)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.rightLinear_bounds`,
`«2610.05164v2».Comparison.Profile.speed_pos`,
`«2610.05164v2».Comparison.Profile.Q_div_speed_le_bound` with the arguments shown in the proof.
-/
theorem traceGradientQ_bound {q r : ℝ} (hq : q ∈ Ioo (0:ℝ) 2)
    (hr : r ∈ Icc (0:ℝ) q) : ‖P.traceGradientQ hκ q r‖ ≤ P.C*P.amplitudeBound+κ*P.C := by
  -- Use the identities/estimates `«2610.05164v2».Comparison.Profile.rightLinear_bounds`,
  -- `«2610.05164v2».Comparison.Profile.speed_pos`,
  -- `«2610.05164v2».Comparison.Profile.Q_div_speed_le_bound` with the arguments shown in the
  -- proof.
  have hR := P.rightLinear_bounds hκ ⟨hq.1.le,hq.2.le⟩
  have hd := P.speed_pos hq
  have hp : r*P.rightLinear hκ q ≤ «2610.05164v2».Calibration.Q q :=
    mul_le_mul hr.2 hR.2 hR.1 hq.1.le
  have hsum : r+P.rightLinear hκ q ≤ 2 := by linarith [hr.2,hR.2]
  have hmul := mul_le_mul_of_nonneg_left hsum (mul_nonneg hκ.le (sq_nonneg (P.amplitude q)))
  have hQ := (div_le_iff₀ hd).mp (P.Q_div_speed_le_bound hq)
  have hν := mul_le_mul_of_nonneg_left ((div_le_iff₀ hd).mp (P.ratio_bounds hq).1) hκ.le
  have hnum : 2*r*P.rightLinear hκ q+κ*(P.amplitude q)^2*(r+P.rightLinear hκ q) ≤
      2*(P.C*P.amplitudeBound+κ*P.C)*P.speed q := by nlinarith
  unfold traceGradientQ
  rw [norm_div,Real.norm_of_nonneg (by positivity : 0 ≤ 2*P.speed q)]
  calc
    _ ≤ (2*r*P.rightLinear hκ q+κ*(P.amplitude q)^2*(r+P.rightLinear hκ q))/(2*P.speed q) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (norm_sub_le _ _).trans (by
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr.1) hR.1),
          Real.norm_of_nonneg (mul_nonneg (mul_nonneg hκ.le (sq_nonneg _)) (add_nonneg hr.1 hR.1))])
    _ ≤ P.C*P.amplitudeBound+κ*P.C := (div_le_iff₀ (by positivity : 0 < 2*P.speed q)).2 (by nlinarith)

/--
The stated quantitative bound `‖P.traceGradientR hκ q r‖ ≤ 1`.

Use: `«2610.05164v2».Comparison.Profile.tracePotential_lipschitz` uses this bound to establish
the displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal (P.C*P.amplitudeBound+κ*P.C+1))
(fun p : ℝ × ℝ => P.tracePotential hκ p.1 p.2) (filterTriangle 1)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.rightLinear_bounds` with
the arguments shown in the proof.
-/
theorem traceGradientR_bound {q r : ℝ} (hq : q ∈ Icc (0:ℝ) 2)
    (hr : r ∈ Icc (0:ℝ) q) : ‖P.traceGradientR hκ q r‖ ≤ 1 := by
  have hR := P.rightLinear_bounds hκ hq
  unfold traceGradientR
  rw [Real.norm_of_nonneg (by linarith [hr.1,hR.1] : 0 ≤ (r+P.rightLinear hκ q)/2)]
  linarith [hr.2,hR.2]

/--
The actual Fréchet derivative: `HasFDerivAt (fun p : ℝ × ℝ => P.tracePotential hκ p.1 p.2)
(P.traceGradientQ hκ p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ+ P.traceGradientR hκ p.1 p.2 •
ContinuousLinearMap.snd ℝ ℝ ℝ) p`.

Use: `«2610.05164v2».Comparison.Profile.tracePotential_lipschitz` uses this Fréchet derivative
formula to establish the displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal
(P.C*P.amplitudeBound+κ*P.C+1)) (fun p : ℝ × ℝ => P.tracePotential hκ p.1 p.2) (filterTriangle
1)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem tracePotential_fderiv {p : ℝ × ℝ} (hq : p.1 ∈ Ioo (0:ℝ) 2) :
    HasFDerivAt (fun p : ℝ × ℝ => P.tracePotential hκ p.1 p.2)
      (P.traceGradientQ hκ p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ+
       P.traceGradientR hκ p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hR := (P.rightLinear_derivative hκ hq).hasFDerivAt.comp p hasFDerivAt_fst
  have hG := (P.traceG_derivative hκ hq).hasFDerivAt.comp p hasFDerivAt_fst
  have hS : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have h := (((hS.pow 2).mul_const (1/4:ℝ)).add ((hS.mul hR).mul_const (1/2:ℝ))).add hG
  convert! h using 1
  · funext z
    simp only [tracePotential,Pi.add_apply,Pi.mul_apply,Function.comp_apply,div_eq_mul_inv,one_mul]
  · apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,Function.comp_apply]
    unfold traceGradientQ traceGradientR
    field_simp [(P.speed_pos hq).ne']
    dsimp only [ContinuousLinearMap.fst,ContinuousLinearMap.snd,LinearMap.fst,LinearMap.snd]
    ring_nf

/--
The displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal (P.C*P.amplitudeBound+κ*P.C+1))
(fun p : ℝ × ℝ => P.tracePotential hκ p.1 p.2) (filterTriangle 1)`.

Use: `«2610.05164v2».Comparison.Profile.traceAlong_locallyAC` uses this identity to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (traceAlong G P)
a b`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.filterTriangle_convex`,
`«2610.05164v2».Comparison.Profile.tracePotential_fderiv`,
`«2610.05164v2».Comparison.Profile.C_positive` with the arguments shown in the proof.
-/
theorem tracePotential_lipschitz :
    LipschitzOnWith (Real.toNNReal (P.C*P.amplitudeBound+κ*P.C+1)) (fun p : ℝ × ℝ => P.tracePotential hκ p.1 p.2) (filterTriangle 1) := by
  -- Use the identities/estimates `«2610.05164v2».Comparison.filterTriangle_convex`,
  -- `«2610.05164v2».Comparison.Profile.tracePotential_fderiv`,
  -- `«2610.05164v2».Comparison.Profile.C_positive` with the arguments shown in the proof.
  let T := filterTriangle 1 ∩ {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 2}
  have hT : Convex ℝ T := (filterTriangle_convex _).inter
    ((convex_Ioo (0:ℝ) 2).linear_preimage (LinearMap.fst ℝ ℝ ℝ))
  have hLip : LipschitzOnWith (Real.toNNReal (P.C*P.amplitudeBound+κ*P.C+1)) (fun p : ℝ × ℝ => P.tracePotential hκ p.1 p.2) T := by
    apply hT.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun p hp => (P.tracePotential_fderiv hκ hp.2).hasFDerivWithinAt)
    intro p hp
    apply NNReal.coe_le_coe.mp
    change ‖P.traceGradientQ hκ p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ+
      P.traceGradientR hκ p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ (Real.toNNReal (P.C*P.amplitudeBound+κ*P.C+1) : ℝ)
    rw [Real.toNNReal_of_nonneg (by have hC := P.C_positive.le; have hM := P.amplitudeBound_positive.le; positivity)]
    have hr : p.2 ∈ Icc (0:ℝ) p.1 := ⟨hp.1.2.1,by simpa only [one_mul] using hp.1.2.2⟩
    calc
      _ ≤ ‖P.traceGradientQ hκ p.1 p.2‖+‖P.traceGradientR hκ p.1 p.2‖ := by
        apply (norm_add_le _ _).trans
        simp only [norm_smul,ContinuousLinearMap.norm_fst,ContinuousLinearMap.norm_snd,mul_one]
        exact le_rfl
      _ ≤ P.C*P.amplitudeBound+κ*P.C+1 := by linarith [P.traceGradientQ_bound hκ hp.2 hr,P.traceGradientR_bound hκ hp.1.1 hr]
  have hcl : closure T=filterTriangle 1 := filterTriangle_closure_strip (by norm_num)
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousOn (fun p : ℝ × ℝ => P.tracePotential hκ p.1 p.2) (closure T) :=
    (P.tracePotential_continuous hκ).continuousOn
  simpa only [hcl] using hLip.closure hc

end
end «2610.05164v2».Comparison.Profile
