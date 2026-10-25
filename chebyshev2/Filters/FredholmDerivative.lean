import chebyshev2.Filters.FredholmCurve
import chebyshev2.Filters.DerivativeTransfer

/-!
Article: chebyshev2, Proposition 3.
Nuclear linearization of the spatial determinant.
Use: `chebyshev2.Filters.leftLogDeterminant_hasDerivAt` feeds
`chebyshev2.Filters.leftLogDeterminant_eq_log_truncatedTransmission` (The two spatial logarithms
have identical AE derivatives and the same normalization at the left endpoint).
Proof chain: `chebyshev2.Comparison.Profile.signed_determinant_comparison` — chebyshev2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.HalfLine
open scoped InnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 600000 in
/--
Nuclear linearization of the spatial determinant. Positivity is only needed on the right, where
the frozen rank-one increment is positive.

The stated quantitative bound `|leftLogDeterminant hm hn s y-leftLogDeterminant hm hn s x- log
(1+(y-x)*(s*m x/(2+nonlinear s m x)))| ≤ s/2*‖leftTraceClass m y-leftTraceClass m x-(y-x) • (m
x • traceClassFeature x)‖`.

Use: `chebyshev2.Filters.leftLogDeterminant_hasDerivAt` uses this bound to establish the
actual derivative at the stated point: `HasDerivAt (leftLogDeterminant hm hn s) (s*m
x/(2+nonlinear s m x)) x`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.leftDensity_integrable`,
`chebyshev2.HalfLine.leftDensity_nonneg`,
`chebyshev2.Continuum.densityOperator_isCompact` with the arguments shown in the proof.
-/
theorem leftLogDeterminant_increment {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) {x y : ℝ} (hxy : x ≤ y) :
    |leftLogDeterminant hm hn s y-leftLogDeterminant hm hn s x-
      log (1+(y-x)*(s*m x/(2+nonlinear s m x)))| ≤
      s/2*‖leftTraceClass m y-leftTraceClass m x-(y-x) • (m x • traceClassFeature x)‖ := by
  -- Use the identities/estimates `chebyshev2.HalfLine.leftDensity_integrable`,
  -- `chebyshev2.HalfLine.leftDensity_nonneg`,
  -- `chebyshev2.Continuum.densityOperator_isCompact` with the arguments shown in the
  -- proof.
  let T := densityOperator (leftDensity m x)
  let D := densitySpectralData (leftDensity_integrable hm x) (leftDensity_nonneg hn x)
  let u := (y-x)*m x
  have hu : 0 ≤ u := mul_nonneg (sub_nonneg.mpr hxy) (hn x)
  let U := u • InnerProductSpace.rankOne ℝ (feature x) (feature x)
  have hTc : IsCompactOperator T := densityOperator_isCompact (leftDensity_integrable hm x)
  have hTp : T.IsPositive := densityOperator_positive (leftDensity_integrable hm x) (leftDensity_nonneg hn x)
  have hUc : IsCompactOperator U := (rankOne_isCompact _ _).smul u
  have hUp : U.IsPositive := (InnerProductSpace.isPositive_rankOne_self (feature x)).smul_of_nonneg hu
  let DU := positiveSpectralData (T+U) (hTc.add hUc) (hTp.add hUp)
    (D.traceBound.isTraceClass.add ((rankOne_isTraceClass _ _).smul u))
  have hupdate := rankOne_logDeterminant hTc hTp D hu hs (feature x) DU
  change logDeterminant DU.eigenvalue s=leftLogDeterminant hm hn s x+
    log (1+s/2*u*inner ℝ (feature x) (featureResolvent hm hn x s hs (feature x))) at hupdate
  rw [featureResolvent_quadratic hm hn hs x] at hupdate
  have hscalar : 1+s/2*u*(2/(2+nonlinear s m x)) =
      1+(y-x)*(s*m x/(2+nonlinear s m x)) := by dsimp [u]; ring
  rw [hscalar] at hupdate
  let W := leftTraceClass m y-leftTraceClass m x-(y-x) • (m x • traceClassFeature x)
  have hW := W.property.traceBound
  change TraceBound W.val ‖W‖ at hW
  have hval : W.val=densityOperator (leftDensity m y)-(T+U) := by
    dsimp only [W,U,T,u]
    simp only [TraceClassOperator.val_sub,TraceClassOperator.val_smul,leftTraceClass_val hm,
      traceClassFeature_val,featureProjection,smul_smul]
    abel
  rw [hval] at hW
  have hb := logDeterminant_traceBound (densityOperator_isCompact (leftDensity_integrable hm y))
    (hTc.add hUc) (densityOperator_positive (leftDensity_integrable hm y) (leftDensity_nonneg hn y))
    (hTp.add hUp) (densitySpectralData (leftDensity_integrable hm y) (leftDensity_nonneg hn y)) DU hW hs
  rw [hupdate] at hb
  simpa only [sub_add_eq_sub_sub,W,leftLogDeterminant] using hb

/--
The actual derivative at the stated point: `HasDerivAt (leftLogDeterminant hm hn s) (s*m
x/(2+nonlinear s m x)) x`.

Use: `chebyshev2.Filters.leftLogDeterminant_eq_log_truncatedTransmission` uses this
derivative formula to establish the identity `leftLogDeterminant hm hn s x=log
(truncatedTransmission s m x)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates
`chebyshev2.Filters.hasDerivAt_of_right_increment_bound`,
`chebyshev2.Filters.leftLogDeterminant_increment` with the arguments shown in the proof.
-/
theorem leftLogDeterminant_hasDerivAt {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) {x : ℝ}
    (hD : HasDerivAt (leftTraceClass m) (m x • traceClassFeature x) x)
    (hH : DifferentiableAt ℝ (leftLogDeterminant hm hn s) x) :
    HasDerivAt (leftLogDeterminant hm hn s) (s*m x/(2+nonlinear s m x)) x := by
  -- Use the identities/estimates `chebyshev2.Filters.hasDerivAt_of_right_increment_bound`,
  -- `chebyshev2.Filters.leftLogDeterminant_increment` with the arguments shown in the
  -- proof.
  let c := s*m x/(2+nonlinear s m x)
  let F : ℝ → ℝ := fun y => log (1+(y-x)*c)
  have hF : HasDerivAt F c x := by
    have h := ((((hasDerivAt_id x).sub_const x).mul_const c).const_add 1).log
      (show 1+(x-x)*c ≠ 0 by simp)
    simpa only [id_eq,sub_self,zero_mul,add_zero,one_mul,div_one] using h
  apply hasDerivAt_of_right_increment_bound hH hF hD
  intro y hy
  have h := leftLogDeterminant_increment hm hn hs hy.le
  simpa only [F,sub_self,zero_mul,add_zero,log_one,sub_zero,Real.norm_eq_abs] using h

end
end chebyshev2.Filters
