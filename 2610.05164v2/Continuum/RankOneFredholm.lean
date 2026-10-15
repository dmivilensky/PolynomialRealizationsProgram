import «2610.05164v2».Continuum.FiniteRankUpdate
import «2610.05164v2».Continuum.SpectralTruncation
import «2610.05164v2».HalfLine.Resolvent

/-!
Article: 2610.05164v2, Proposition 3.
The Fredholm matrix determinant lemma for the already defined spectral logarithm of the actual
compact operator.
Use: `«2610.05164v2».Continuum.rankOne_logDeterminant` feeds
`«2610.05164v2».Filters.leftLogDeterminant_increment` (Nuclear linearization of the spatial
determinant).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Real Filter «2610.05164v2».HalfLine
open scoped InnerProductSpace BigOperators Classical Topology
set_option backward.isDefEq.respectTransparency false

variable {T : FeatureSpace →L[ℝ] FeatureSpace}

/--
The precise assertion is `TraceBound T (∑' i, D.eig i)`.

Use: `«2610.05164v2».Continuum.rankOne_logDeterminant` uses this assertion to establish exact
identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log (1+s/2*u*inner ℝ
v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v))`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.eigenbasis_traceBound` with the
arguments shown in the proof.
-/
theorem PositiveSpectralData.traceBound (D : PositiveSpectralData T) :
    TraceBound T (∑' i, D.eig i) := by
  simpa only [abs_of_nonneg (D.nonneg _)] using eigenbasis_traceBound D.basis T D.equation
    (by simpa only [abs_of_nonneg (D.nonneg _)] using D.summable)

/--
The remainder in the finite Schur formula converges to the actual resolvent quadratic form,
including the zero eigenspace.

Convergence along the specified source filter to the specified limit: `Tendsto (fun F : Finset
D.Index => ‖v‖^2- ∑ i ∈ F, a*D.eig i/(1+a*D.eig i)*(inner ℝ (D.basis i) v)^2) atTop (𝓝 (inner ℝ
v (inverseOfUnit _ (positive_pencil_unit hp ha) v)))`.

Use: `«2610.05164v2».Continuum.rankOne_logDeterminant` uses this limit to establish exact
identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log (1+s/2*u*inner ℝ
v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v))`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem resolvent_remainder_tendsto (D : PositiveSpectralData T) (hp : T.IsPositive)
    {a : ℝ} (ha : 0 ≤ a) (v : FeatureSpace) :
    Tendsto (fun F : Finset D.Index => ‖v‖^2-
      ∑ i ∈ F, a*D.eig i/(1+a*D.eig i)*(inner ℝ (D.basis i) v)^2) atTop
      (𝓝 (inner ℝ v (inverseOfUnit _ (positive_pencil_unit hp ha) v))) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hden (i : D.Index) : 0 < 1+a*D.eig i := by nlinarith [D.nonneg i]
  have h1 : HasSum (fun i => (inner ℝ (D.basis i) v)^2) (‖v‖^2) := by
    simpa only [real_inner_comm v (D.basis _),← pow_two,real_inner_self_eq_norm_sq]
      using D.basis.hasSum_inner_mul_inner v v
  have h2 := resolvent_quadratic_hasSum D hp a (positive_pencil_unit hp ha)
    (fun i => (hden i).ne') v
  have h3 : HasSum (fun i => a*D.eig i/(1+a*D.eig i)*(inner ℝ (D.basis i) v)^2)
      (‖v‖^2-inner ℝ v (inverseOfUnit _ (positive_pencil_unit hp ha) v)) := by
    convert h1.sub h2 using 1
    funext i
    field_simp [(hden i).ne']
    ring
  have h := h3.const_sub (‖v‖^2)
  simpa only [sub_sub_cancel,SummationFilter.unconditional_filter] using h

set_option maxHeartbeats 800000 in
/--
The Fredholm matrix determinant lemma for the already defined spectral logarithm of the actual
compact operator. Its proof passes through finite Schur complements and the nuclear spectral
perturbation bound.

Exact identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log
(1+s/2*u*inner ℝ v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity))
v))`.

Use: `«2610.05164v2».Filters.leftLogDeterminant_increment` uses this identity to establish the
stated quantitative bound `|leftLogDeterminant hm hn s y-leftLogDeterminant hm hn s x- log
(1+(y-x)*(s*m x/(2+nonlinear s m x)))| ≤ s/2*‖leftTraceClass m y-leftTraceClass m x-(y-x) • (m
x • traceClassFeature x)‖`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Apply the finite rank-one Schur-complement formula to spectral truncations of the base
operator. The trace-class spectral tail tends to zero and bounds both the base and updated
log-determinant errors. Parseval and the actual resolvent series identify the finite quadratic
remainder, including the zero eigenspace. Its nonnegativity keeps the logarithm argument
strictly positive. Passing to the limit in the finite identity gives the actual
compact-operator determinant lemma.
-/
theorem rankOne_logDeterminant (hc : IsCompactOperator T) (hp : T.IsPositive)
    (D : PositiveSpectralData T) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s)
    (v : FeatureSpace) (D' : PositiveSpectralData (T+u • InnerProductSpace.rankOne ℝ v v)) :
    logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+
      log (1+s/2*u*inner ℝ v (inverseOfUnit _
        (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v)) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  let U := u • InnerProductSpace.rankOne ℝ v v
  have hUc : IsCompactOperator U := (rankOne_isCompact v v).smul u
  have hUp : U.IsPositive := (InnerProductSpace.isPositive_rankOne_self v).smul_of_nonneg hu
  have hUt : IsTraceClass U := (rankOne_isTraceClass v v).smul u
  -- Use actual positive spectral data for each finite truncation plus the fixed rank-one
  -- update.
  let DF (F : Finset D.Index) : PositiveSpectralData (spectralTruncation D F+U) :=
    positiveSpectralData _ ((spectralTruncation_compact D F).add hUc)
      ((spectralTruncation_positive D F).add hUp)
      (((truncationSpectralData D F).traceBound.isTraceClass).add hUt)
  -- This is the already proved finite Schur-complement identity, expressed in the truncation
  -- eigenbasis.
  have he (F : Finset D.Index) : logDeterminant (DF F).eigenvalue s =
      logDeterminant (truncationSpectralData D F).eigenvalue s+
        log (1+s/2*u*(‖v‖^2-
          ∑ i ∈ F, (s/2)*D.eig i/(1+s/2*D.eig i)*(inner ℝ (D.basis i) v)^2)) := by
    have h := finite_rankOne_logDeterminant (fun i : F => D.basis i)
      (D.basis.orthonormal.comp Subtype.val Subtype.val_injective)
      (fun i : F => D.eig i) (fun i => D.nonneg i) hu hs v
    have hsum : (∑ i : F, D.eig i • InnerProductSpace.rankOne ℝ (D.basis i) (D.basis i)) =
        spectralTruncation D F := by
      dsimp only [spectralTruncation]
      exact Finset.sum_coe_sort F (fun i : D.Index =>
        D.eig i • InnerProductSpace.rankOne ℝ (D.basis i) (D.basis i))
    rw [hsum] at h
    have h' := h (DF F)
    rw [spectralTruncation_logDeterminant D F hs]
    rw [Finset.sum_coe_sort F (fun i : D.Index => log (1+s/2*D.eig i)),
      Finset.sum_coe_sort F (fun i : D.Index =>
        (s/2)*D.eig i/(1+s/2*D.eig i)*(inner ℝ (D.basis i) v)^2)] at h'
    exact h'
  -- Summability of the full spectrum makes the discarded trace tail vanish, supplying a
  -- quantitative convergence budget.
  have htail : Tendsto (fun F : Finset D.Index => (∑' i, D.eig i)-∑ i ∈ F, D.eig i)
      atTop (𝓝 0) := by
    simpa only [sub_self,SummationFilter.unconditional_filter] using
      D.summable.hasSum.const_sub (∑' i, D.eig i)
  have htail' := htail.const_mul (s/2)
  simp only [mul_zero] at htail'
  -- Record the convergence hbase with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hbase : Tendsto (fun F : Finset D.Index =>
      logDeterminant (truncationSpectralData D F).eigenvalue s) atTop
      (𝓝 (logDeterminant D.eigenvalue s)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun F => ?_) htail'
    have h := logDeterminant_traceBound hc (spectralTruncation_compact D F) hp
      (spectralTruncation_positive D F) D (truncationSpectralData D F)
      (spectralTruncation_error D F) hs
    rw [norm_sub_rev,Real.norm_eq_abs]
    exact h
  -- The same rank-one update appears on both sides, so it cancels from their difference; the
  -- original truncation tail still bounds the updated error.
  have hupdated : Tendsto (fun F : Finset D.Index => logDeterminant (DF F).eigenvalue s)
      atTop (𝓝 (logDeterminant D'.eigenvalue s)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun F => ?_) htail'
    have herror : TraceBound ((T+U)-(spectralTruncation D F+U))
        ((∑' i, D.eig i)-∑ i ∈ F, D.eig i) := by
      simpa only [add_sub_add_right_eq_sub] using spectralTruncation_error D F
    have h := logDeterminant_traceBound (hc.add hUc) ((spectralTruncation_compact D F).add hUc)
      (hp.add hUp) ((spectralTruncation_positive D F).add hUp) D' (DF F) herror hs
    rw [norm_sub_rev,Real.norm_eq_abs]
    exact h
  have hquad := resolvent_remainder_tendsto D hp (a := s/2) (div_nonneg hs (by norm_num)) v
  -- Pass finite resolvent positivity to the limit. This ensures the logarithm is taken at a
  -- positive, nonzero argument.
  have hqpos : 0 ≤ inner ℝ v (inverseOfUnit _
      (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v) := by
    apply ge_of_tendsto hquad
    exact Eventually.of_forall (fun F => by
      have h := finite_resolvent_remainder_nonneg
        (fun i : F => D.basis i) (D.basis.orthonormal.comp Subtype.val Subtype.val_injective)
        (fun i : F => D.eig i) (fun i => D.nonneg i) (a := s/2)
        (div_nonneg hs (by norm_num)) v
      rw [Finset.sum_coe_sort F (fun i : D.Index =>
        (s/2)*D.eig i/(1+s/2*D.eig i)*(inner ℝ (D.basis i) v)^2)] at h
      exact h)
  have hden : 1+s/2*u*inner ℝ v (inverseOfUnit _
      (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v) ≠ 0 := by
    have ha : 0 ≤ s/2*u := mul_nonneg (div_nonneg hs (by norm_num)) hu
    nlinarith [mul_nonneg ha hqpos]
  -- Continuity of log is used only after its nonzero-argument hypothesis has been established.
  have hlog := ((hquad.const_mul (s/2*u)).const_add 1).log hden
  have hright := hbase.add hlog
  have hupdated' := hupdated.congr he
  exact tendsto_nhds_unique hupdated' hright

end
end «2610.05164v2».Continuum
