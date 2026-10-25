import chebyshev2.Comparison.ProfileFlow
import chebyshev2.Residual.LevelSets
import chebyshev2.Filters.StateFlow

/-!
Article: chebyshev2, Theorem 3.4.
Lemma 12 for the full comparison-profile class, with both endpoint level sets.
Use: `chebyshev2.Comparison.Profile.signed_trace_comparison` feeds
`chebyshev2.Calibration.Data.signed_trace_comparison` (signed trace comparison).
-/
namespace chebyshev2.Comparison
open Set MeasureTheory chebyshev2.GroundState chebyshev2.Filters
variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x}

/--
Membership in the specified domain/enclosure: `(G.q x,nonlinear s m x) ∈ filterTriangle
(s/groundParameter hm hn)`.

Use: `chebyshev2.Comparison.Profile.determinantAlong_locallyAC` uses this assertion to
establish absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(determinantAlong G P (s := s)) a b`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.GroundWitness.coordinate_mem`,
`chebyshev2.Filters.nonlinear_bounds`, `chebyshev2.Filters.nonlinear_le_coordinate`
with the arguments shown in the proof.
-/
theorem determinantState_mem_triangle (G : GroundWitness hm hn) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    (G.q x,nonlinear s m x) ∈ filterTriangle (s/groundParameter hm hn) :=
  ⟨G.coordinate_mem x,(nonlinear_bounds hm hn hs x).1,nonlinear_le_coordinate G hs x⟩

/--
Membership in the specified domain/enclosure: `(G.q x,linear hm hn x) ∈ filterTriangle 1`.

Use: `chebyshev2.Comparison.Profile.traceAlong_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (traceAlong G P)
a b`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.GroundWitness.coordinate_mem`,
`chebyshev2.Filters.linear_nonneg`, `chebyshev2.Filters.linear_le_coordinate` with the
arguments shown in the proof.
-/
theorem traceState_mem_triangle (G : GroundWitness hm hn) (x : ℝ) :
    (G.q x,linear hm hn x) ∈ filterTriangle 1 :=
  ⟨G.coordinate_mem x,linear_nonneg G x,by simpa only [one_mul] using linear_le_coordinate G x⟩
end chebyshev2.Comparison

namespace chebyshev2.Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.GroundState chebyshev2.Filters chebyshev2.Comparison chebyshev2.Residual chebyshev2.Calibration
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {m : ℝ → ℝ} {hm : Integrable m}
  {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)
  (P : chebyshev2.Comparison.Profile (groundParameter hm hn)) {s : ℝ} (hs : 0 ≤ s)
include hs

/--
Defines `determinantAlong` of type `ℝ` by `P.determinantPotential G.coupling_positive s (G.q x)
(nonlinear s m x)`.

Use: `chebyshev2.Comparison.Profile.determinantAlong_derivative` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(determinantAlong G P (s := s)) (-nonlinear s m x+P.comparisonA G.coupling_positive s (G.q x)
(nonlinear s m x)* (m x-(P.amplitude (G.q x))^2)) x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def determinantAlong (x : ℝ) : ℝ :=
  P.determinantPotential G.coupling_positive s (G.q x) (nonlinear s m x)

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(determinantAlong G P (s := s)) a b`.

Use: `chebyshev2.Comparison.Profile.determinantAlong_derivative` uses this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(determinantAlong G P (s := s)) (-nonlinear s m x+P.comparisonA G.coupling_positive s (G.q x)
(nonlinear s m x)* (m x-(P.amplitude (G.q x))^2)) x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coupling_positive`,
`chebyshev2.Comparison.Profile.determinantPotential_lipschitz`,
`chebyshev2.Comparison.determinantState_mem_triangle` with the arguments shown in the
proof.
-/
theorem determinantAlong_locallyAC (a b : ℝ) :
    AbsolutelyContinuousOnInterval (determinantAlong G P (s := s)) a b := by
  change AbsolutelyContinuousOnInterval
    (fun x => (fun p : ℝ × ℝ => P.determinantPotential G.coupling_positive s p.1 p.2)
      (G.q x,nonlinear s m x)) a b
  exact (P.determinantPotential_lipschitz G.coupling_positive hs).comp_absolutelyContinuousOnInterval
    (fun x _ => determinantState_mem_triangle G hs x)
    (absolutelyContinuous_prod (G.coordinate_locallyAC a b) (nonlinear_locallyAC hm hn hs a b))

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(determinantAlong G P (s := s)) (-nonlinear s m x+P.comparisonA G.coupling_positive s (G.q x)
(nonlinear s m x)* (m x-(P.amplitude (G.q x))^2)) x`.

Use: `chebyshev2.Comparison.Profile.signed_determinant_comparison` uses this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `G.q x=0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Clear the denominators using the
available nonzero hypotheses, then verify the remaining algebraic identity.
-/
theorem determinantAlong_derivative : ∀ᵐ x, HasDerivAt (determinantAlong G P (s := s))
    (-nonlinear s m x+P.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)*
      (m x-(P.amplitude (G.q x))^2)) x := by
  -- Separate `G.q x=0` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  let W := determinantAlong G P (s := s)
  let Z : ℝ → ℝ := fun x => W x-log (1+nonlinear s m x/2)
  filter_upwards [determinantPotential_flow_derivative G P hs,
    locallyAC_ae_differentiable (determinantAlong_locallyAC G P hs),
    derivative_zero_on_level_ae W (P.determinantPotential G.coupling_positive s 0 0),
    derivative_zero_on_level_ae G.q 2,derivative_zero_on_level_ae Z 0,
    G.coordinate_derivative,nonlinear_derivative hm hn hs] with x hi hw h0 h2 hZ hq hr
  by_cases hx0 : G.q x=0
  · have hb := nonlinear_le_coordinate G hs x
    rw [hx0,mul_zero] at hb
    have hz : nonlinear s m x=0 := le_antisymm hb (nonlinear_bounds hm hn hs x).1
    have he : W x=P.determinantPotential G.coupling_positive s 0 0 := by
      dsimp [W,determinantAlong]; rw [hx0,hz]
    have hd := h0 he _ hw.hasDerivAt
    have ha : P.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)=0 := by
      rw [hx0,comparisonA,ite_eq_right (by simp)]
    rw [ha,hz,zero_mul,neg_zero,zero_add]
    simpa only [hd] using hw.hasDerivAt
  by_cases hx2 : G.q x=2
  · have hqd := h2 hx2 _ hq
    have hm0 : m x=0 := by
      have hk : groundParameter hm hn*m x=0 := by simpa only [hx2,sub_self,mul_zero,sub_zero] using hqd
      exact (mul_eq_zero.mp hk).resolve_left G.coupling_positive.ne'
    have hnD : 2+nonlinear s m x ≠ 0 := ne_of_gt (by linarith [(nonlinear_bounds hm hn hs x).1])
    have hl := (((hr.div_const 2).const_add 1).log
      (ne_of_gt (by linarith [(nonlinear_bounds hm hn hs x).1] : 0 < 1+nonlinear s m x/2)))
    have hl' : HasDerivAt (fun x => log (1+nonlinear s m x/2)) (-nonlinear s m x) x := by
      convert hl using 1
      rw [hm0,mul_zero]
      field_simp [hnD]
      ring
    have hz : Z x=0 := by
      dsimp [Z,W,determinantAlong]
      rw [hx2,P.determinantPotential_two G.coupling_positive hs,sub_self]
    have hd := hZ hz _ (hw.hasDerivAt.sub hl')
    have he : deriv W x= -nonlinear s m x := by linarith
    have ha : P.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)=0 := by
      rw [hx2,comparisonA,ite_eq_right (by simp)]
    rw [ha,zero_mul,add_zero]
    change HasDerivAt W (-nonlinear s m x) x
    rw [← he]
    exact hw.hasDerivAt
  · exact hi ⟨lt_of_le_of_ne (G.coordinate_mem x).1 (Ne.symm hx0),
      lt_of_le_of_ne (G.coordinate_mem x).2 hx2⟩

/--
The precise assertion is `chebyshev2.Continuum.logDeterminant
(chebyshev2.Continuum.kernelEigenvalue hm hn) s- chebyshev2.Continuum.logDeterminant
(chebyshev2.Continuum.kernelEigenvalue ((P.speedData
G.coupling_positive).density_integrable G.coupling_positive) ((P.speedData
G.coupling_positive).density_nonneg G.coupling_positive)) s= ∫ x, P.comparisonA
G.coupling_positive s (G.q x) (nonlinear s m x)* (m x-(P.amplitude (G.q x))^2)`.

Use: `chebyshev2.Calibration.Data.signed_determinant_comparison` uses this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem signed_determinant_comparison :
    chebyshev2.Continuum.logDeterminant (chebyshev2.Continuum.kernelEigenvalue hm hn) s-
      chebyshev2.Continuum.logDeterminant
        (chebyshev2.Continuum.kernelEigenvalue
          ((P.speedData G.coupling_positive).density_integrable G.coupling_positive)
          ((P.speedData G.coupling_positive).density_nonneg G.coupling_positive)) s=
      ∫ x, P.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)*
        (m x-(P.amplitude (G.q x))^2) := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have hc := P.determinantPotential_continuousOn G.coupling_positive hs
  -- Record the convergence hl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hl : Tendsto (determinantAlong G P (s := s)) atBot
      (𝓝 (P.determinantPotential G.coupling_positive s 0 0)) := by
    -- Record the convergence hy with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hy : Tendsto (fun x => (G.q x,nonlinear s m x)) atBot
        (𝓝[filterTriangle (s/groundParameter hm hn)] (0,0)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨G.coordinate_limits.1.prodMk_nhds (nonlinear_limits hm hn hs).1,
          Eventually.of_forall (determinantState_mem_triangle G hs)⟩
    exact (hc (0,0) ⟨by norm_num,by norm_num,by norm_num⟩).tendsto.comp
      (f := fun x => (G.q x,nonlinear s m x)) hy
  -- Record the convergence hr with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hr : Tendsto (determinantAlong G P (s := s)) atTop (𝓝 0) := by
    -- Record the convergence hy with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hy : Tendsto (fun x => (G.q x,nonlinear s m x)) atTop
        (𝓝[filterTriangle (s/groundParameter hm hn)] (2,0)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨G.coordinate_limits.2.prodMk_nhds (nonlinear_limits hm hn hs).2,
          Eventually.of_forall (determinantState_mem_triangle G hs)⟩
    -- Record the convergence ht with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have ht : Tendsto (determinantAlong G P (s := s)) atTop
        (𝓝 (P.determinantPotential G.coupling_positive s 2 0)) :=
      (hc (2,0) ⟨by norm_num,by norm_num,
        mul_nonneg (div_nonneg hs G.coupling_positive.le) (by norm_num)⟩).tendsto.comp
        (f := fun x => (G.q x,nonlinear s m x)) hy
    simpa only [P.determinantPotential_two G.coupling_positive hs,zero_div,add_zero,log_one] using ht
  have h := integral_derivative_eq_limits (determinantAlong_locallyAC G P hs)
    (determinantAlong_derivative G P hs)
    ((nonlinear_integrable hm hn hs).neg.add (comparisonA_integrable G P hs)) hl hr
  have he : (∫ x, -nonlinear s m x+P.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)*
      (m x-(P.amplitude (G.q x))^2))=
    (∫ x, -nonlinear s m x)+∫ x, P.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)*
      (m x-(P.amplitude (G.q x))^2) :=
    integral_add (nonlinear_integrable hm hn hs).neg (comparisonA_integrable G P hs)
  rw [he,
    integral_neg,nonlinear_mass_eq_logDeterminant hm hn hs,
    P.determinantPotential_zero G.coupling_positive hs] at h
  linarith

end
end chebyshev2.Comparison.Profile

namespace chebyshev2.Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.GroundState chebyshev2.Filters chebyshev2.Comparison chebyshev2.Residual chebyshev2.Calibration
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {m : ℝ → ℝ} {hm : Integrable m}
  {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)
  (P : chebyshev2.Comparison.Profile (groundParameter hm hn))

/--
Defines `traceAlong` of type `ℝ` by `P.tracePotential G.coupling_positive (G.q x) (linear hm hn
x)`.

Use: `chebyshev2.Comparison.Profile.signed_trace_comparison` uses this definition to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def traceAlong (x : ℝ) : ℝ :=
  P.tracePotential G.coupling_positive (G.q x) (linear hm hn x)

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (traceAlong G P)
a b`.

Use: `chebyshev2.Comparison.Profile.signed_trace_comparison` uses this assertion to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coupling_positive`,
`chebyshev2.Comparison.Profile.tracePotential_lipschitz`,
`chebyshev2.Comparison.traceState_mem_triangle` with the arguments shown in the proof.
-/
theorem traceAlong_locallyAC (a b : ℝ) :
    AbsolutelyContinuousOnInterval (traceAlong G P) a b := by
  change AbsolutelyContinuousOnInterval
    (fun x => (fun p : ℝ × ℝ => P.tracePotential G.coupling_positive p.1 p.2)
      (G.q x,linear hm hn x)) a b
  exact (P.tracePotential_lipschitz G.coupling_positive).comp_absolutelyContinuousOnInterval
    (fun x _ => traceState_mem_triangle G x)
    (absolutelyContinuous_prod (G.coordinate_locallyAC a b) (linear_locallyAC a b))

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (traceAlong G
P) (-(linear hm hn x)^2+P.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)* (m
x-(P.amplitude (G.q x))^2)) x`.

Use: `chebyshev2.Comparison.Profile.signed_trace_comparison` uses this assertion to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `G.q x=0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Clear the denominators using the
available nonzero hypotheses, then verify the remaining algebraic identity.
-/
theorem traceAlong_derivative : ∀ᵐ x, HasDerivAt (traceAlong G P)
    (-(linear hm hn x)^2+P.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)*
      (m x-(P.amplitude (G.q x))^2)) x := by
  -- Separate `G.q x=0` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  let W := traceAlong G P
  let Z : ℝ → ℝ := fun x => W x-(linear hm hn x)^2/4
  filter_upwards [locallyAC_ae_differentiable (traceAlong_locallyAC G P),
    derivative_zero_on_level_ae W (P.tracePotential G.coupling_positive 0 0),
    derivative_zero_on_level_ae G.q 2,derivative_zero_on_level_ae Z 0,
    G.coordinate_derivative,linear_derivative_ae (hm := hm) (hn := hn)] with x hw h0 h2 hZ hq hr
  by_cases hx0 : G.q x=0
  · have hb := linear_le_coordinate G x
    rw [hx0] at hb
    have hz : linear hm hn x=0 := le_antisymm hb (linear_nonneg G x)
    have he : W x=P.tracePotential G.coupling_positive 0 0 := by
      dsimp [W,traceAlong]; rw [hx0,hz]
    have hd := h0 he _ hw.hasDerivAt
    have ha : P.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)=0 := by
      rw [hx0,comparisonA0,ite_eq_right (by simp)]
    rw [ha,hz,zero_mul,zero_pow (by decide : 2 ≠ 0),neg_zero,zero_add]
    simpa only [hd] using hw.hasDerivAt
  by_cases hx2 : G.q x=2
  · have hqd := h2 hx2 _ hq
    have hm0 : m x=0 := by
      have hk : groundParameter hm hn*m x=0 := by simpa only [hx2,sub_self,mul_zero,sub_zero] using hqd
      exact (mul_eq_zero.mp hk).resolve_left G.coupling_positive.ne'
    have hl : HasDerivAt (fun x => (linear hm hn x)^2/4) (-(linear hm hn x)^2) x := by
      convert (hr.pow 2).div_const 4 using 1
      rw [hm0,mul_zero]
      ring
    have hz : Z x=0 := by
      dsimp [Z,W,traceAlong]
      rw [hx2,P.tracePotential_two G.coupling_positive,sub_self]
    have hd := hZ hz _ (hw.hasDerivAt.sub hl)
    have he : deriv W x= -(linear hm hn x)^2 := by linarith
    have ha : P.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)=0 := by
      rw [hx2,comparisonA0,ite_eq_right (by simp)]
    rw [ha,zero_mul,add_zero]
    change HasDerivAt W (-(linear hm hn x)^2) x
    rw [← he]
    exact hw.hasDerivAt
  · have hx : G.q x ∈ Ioo (0:ℝ) 2 :=
      ⟨lt_of_le_of_ne (G.coordinate_mem x).1 (Ne.symm hx0),lt_of_le_of_ne (G.coordinate_mem x).2 hx2⟩
    have hp := P.tracePotential_path_derivative G.coupling_positive hx hq hr
    convert hp using 1
    · rfl
    · rw [comparisonA0,ite_eq_left hx]
      unfold traceCoefficient
      field_simp [(P.speed_pos hx).ne']
      rw [P.speed_eq ⟨hx.1.le,hx.2.le⟩]
      unfold chebyshev2.Calibration.Q
      ring

/--
The precise assertion is `(∫ x, (linear hm hn x)^2)- (∫ x, (linear ((P.speedData
G.coupling_positive).density_integrable G.coupling_positive) ((P.speedData
G.coupling_positive).density_nonneg G.coupling_positive) x)^2)= ∫ x, P.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(P.amplitude (G.q x))^2)`.

Use: `chebyshev2.Calibration.Data.signed_trace_comparison` uses this identity to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem signed_trace_comparison :
    (∫ x, (linear hm hn x)^2)-
      (∫ x, (linear ((P.speedData G.coupling_positive).density_integrable G.coupling_positive)
        ((P.speedData G.coupling_positive).density_nonneg G.coupling_positive) x)^2)=
      ∫ x, P.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)*
        (m x-(P.amplitude (G.q x))^2) := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have hc := P.tracePotential_continuous G.coupling_positive
  -- Record the convergence hl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hl : Tendsto (traceAlong G P) atBot (𝓝 (P.tracePotential G.coupling_positive 0 0)) :=
    hc.continuousAt.tendsto.comp
      (f := fun x => (G.q x,linear hm hn x)) (G.coordinate_limits.1.prodMk_nhds linear_limits.1)
  -- Record the convergence hr with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hr : Tendsto (traceAlong G P) atTop (𝓝 0) := by
    -- Record the convergence ht with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have ht : Tendsto (traceAlong G P) atTop (𝓝 (P.tracePotential G.coupling_positive 2 0)) :=
      hc.continuousAt.tendsto.comp
        (f := fun x => (G.q x,linear hm hn x)) (G.coordinate_limits.2.prodMk_nhds linear_limits.2)
    simpa only [P.tracePotential_two G.coupling_positive,zero_pow (by decide : 2 ≠ 0),zero_div] using ht
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (fun x => (linear hm hn x)^2) := by
    simpa only [linear,mul_pow] using (causal_square_integrable hm hn).const_mul ((groundParameter hm hn)^2)
  have h := integral_derivative_eq_limits (traceAlong_locallyAC G P) (traceAlong_derivative G P)
    (hi.neg.add (comparisonA0_integrable G P)) hl hr
  have he : (∫ x, -(linear hm hn x)^2+P.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)*
      (m x-(P.amplitude (G.q x))^2))=
    (∫ x, -(linear hm hn x)^2)+∫ x, P.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)*
      (m x-(P.amplitude (G.q x))^2) :=
    integral_add hi.neg (comparisonA0_integrable G P)
  rw [he,integral_neg,P.tracePotential_zero G.coupling_positive] at h
  linarith

end
end chebyshev2.Comparison.Profile
