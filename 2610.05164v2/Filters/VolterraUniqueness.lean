import «2610.05164v2».Filters.VolterraEquation

/-!
Article: 2610.05164v2, Theorem 6.1.
Uniqueness in the full bounded, integrable-forcing solution class.
Use: `«2610.05164v2».Filters.jost_unique_of_bounded_measurable` feeds
`«2610.05164v2».LocalObstruction.signedJost_actual` (signed Jost actual).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `‖volterra s m f x‖ ≤ s/2*∫ t in Iic x, m t*‖f t‖`.

Use: `«2610.05164v2».Filters.volterra_fixedPoint_zero` uses this bound to establish exact
identity `f=0`.

Article: 2610.05164v2, Lemma 14 via
`«2610.05164v2».Comparison.symmetric_logDeterminant_support_at`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem volterra_norm_le {m f : ℝ → ℝ} (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (hf : Integrable (fun t => m t*f t)) (x : ℝ) :
    ‖volterra s m f x‖ ≤ s/2*∫ t in Iic x, m t*‖f t‖ := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [volterra_integral hf, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ s/2)]
  apply mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_) (by positivity)
  apply integral_mono_of_nonneg (Eventually.of_forall (fun t => norm_nonneg _))
    (hf.norm.integrableOn.congr (Eventually.of_forall (fun t => by
      change ‖m t*f t‖ = m t*‖f t‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn t)])))
  filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
  have he : exp (-2*(x-t)) ≤ 1 := exp_le_one_iff.mpr (by change t ≤ x at ht; linarith)
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr he),
    Real.norm_eq_abs, abs_of_nonneg (hn t)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (hn t) (sub_le_self _ (exp_pos _).le)) (norm_nonneg _)

/--
Factorial decay forces every bounded solution of the homogeneous Volterra equation to vanish.
No positivity of the solution is assumed.

Exact identity `f=0`.

Use: `«2610.05164v2».Filters.jost_unique` uses this identity to establish the identity
`w=jost s m`.

Article: 2610.05164v2, Lemma 14 via
`«2610.05164v2».Comparison.symmetric_logDeterminant_support_at`.

Proof: Induct on `n` while keeping `x` arbitrary; the recursive step uses the
previous-stage assertion. Pass the established inequalities to the limit using the displayed
filter convergence. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem volterra_fixedPoint_zero {m f : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (hf : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : ∀ t, ‖f t‖ ≤ C) (he : ∀ x, f x=volterra s m f x) : f=0 := by
  -- Induct on `n` while keeping `x` arbitrary; the recursive step uses the previous-stage
  -- assertion.
  have hF := bounded_forcing_integrable hm hf hC
  -- Iterate the homogeneous equation. Each integration of a cumulative-mass
  -- power contributes the next factorial denominator, without needing f ≥ 0.
  have hb (n : ℕ) (x : ℝ) : ‖f x‖ ≤ C*factorialBound s (cumulative m x) n := by
    induction n generalizing x with
    | zero => simpa [factorialBound] using hC x
    | succ n ih =>
      rw [he x]
      apply (volterra_norm_le hn hs hF x).trans
      calc
        _ ≤ s/2*∫ t in Iic x, C*((s/2)^n/(n.factorial))*(m t*(cumulative m t)^n) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          apply integral_mono_ae
            (hF.norm.integrableOn.congr (Eventually.of_forall (fun t => by
              change ‖m t*f t‖ = m t*‖f t‖
              rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn t)])))
            (((cumulative_power_integrable hm hn n).const_mul _).integrableOn)
          exact Eventually.of_forall (fun t => by
            convert mul_le_mul_of_nonneg_left (ih t) (hn t) using 1; dsimp [factorialBound]; ring)
        _ = C*factorialBound s (cumulative m x) (n+1) := by
          rw [integral_const_mul, cumulative_power_integral hm hn]
          rw [← factorialBound_step s (cumulative m x) n]
          ring
  funext x
  -- The factorial bound tends to zero at every fixed x. Hence the norm of the
  -- solution vanishes; this is stronger than a small-parameter contraction argument.
  have ht : Tendsto (fun n => C*factorialBound s (cumulative m x) n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((factorialBound_hasSum s (cumulative m x)).summable.tendsto_atTop_zero.const_mul C)
  have hz : ‖f x‖ ≤ 0 := ge_of_tendsto ht (Eventually.of_forall (fun n => hb n x))
  exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))

/--
Uniqueness in the full bounded, integrable-forcing solution class. Continuity is a consequence
of the integral equation, not a hypothesis.

Exact identity `w=jost s m`.

Use: `«2610.05164v2».Filters.jost_unique_of_bounded_measurable` uses this identity to establish
exact identity `w=jost s m`.

Article: 2610.05164v2, Lemma 14 via
`«2610.05164v2».Comparison.symmetric_logDeterminant_support_at`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem jost_unique {m w : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (hw : Integrable (fun t => m t*w t))
    {C : ℝ} (hC : ∀ t, ‖w t‖ ≤ C) (he : ∀ x, w x=1+volterra s m w x) : w=jost s m := by
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous w := by
    -- Continuity is derived from the integral equation rather than imposed on w.
    have h : Continuous (fun x => (1:ℝ)+volterra s m w x) := continuous_const.add (volterra_continuous hw s)
    exact h.congr (fun x => (he x).symm)
  have hj := jost_forcing_integrable hm hn hs
  have hvsub (x : ℝ) : volterra s m (fun t => w t-jost s m t) x=
      volterra s m w x-volterra s m (jost s m) x := by
    unfold volterra cumulative causal
    have hmul : (fun t => m t*(w t-jost s m t))=
        (fun t => m t*w t-m t*jost s m t) := by funext t; ring
    rw [hmul, integral_sub hw.integrableOn hj.integrableOn]
    have hmul' : (fun t => exp (2*t)*((fun t => m t*w t-m t*jost s m t)) t)=
        (fun t => exp (2*t)*(m t*w t)-exp (2*t)*(m t*jost s m t)) := by
      funext t; ring
    rw [hmul', integral_sub (forcing_integrable (by norm_num : (0:ℝ) ≤ 2) hw x)
      (forcing_integrable (by norm_num : (0:ℝ) ≤ 2) hj x)]
    ring
  have hz := volterra_fixedPoint_zero hm hn hs
    -- Subtract the canonical Jost solution. Linearity makes the difference a
    -- bounded homogeneous fixed point, which the preceding factorial argument kills.
    (hc.sub (jost_continuous hm hn hs)).aestronglyMeasurable
    (C := C+exp (s*(∫ t, m t)/2))
    (fun t => (norm_sub_le _ _).trans (add_le_add (hC t) (by
      rw [Real.norm_eq_abs, abs_of_pos (jost_positive hm hn hs t)]
      exact jost_uniform_bound hm hn hs t)))
    (fun x => by
      change w x-jost s m x=volterra s m (fun t => w t-jost s m t) x
      rw [hvsub, he x, jost_equation hm hn hs x]; ring)
  funext x
  have h := congrFun hz x
  exact sub_eq_zero.mp h

/--
Exact identity `w=jost s m`.

Use: `«2610.05164v2».LocalObstruction.signedJost_actual` uses this identity to establish exact
identity `signedJost hm s=jostBCF hm hn hs`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_unique`,
`«2610.05164v2».Filters.bounded_forcing_integrable` with the arguments shown in the proof.
-/
theorem jost_unique_of_bounded_measurable {m w : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ t, 0 ≤ m t) {s : ℝ} (hs : 0 ≤ s) (hw : AEStronglyMeasurable w volume)
    {C : ℝ} (hC : ∀ t, ‖w t‖ ≤ C) (he : ∀ x, w x=1+volterra s m w x) : w=jost s m :=
  jost_unique hm hn hs (bounded_forcing_integrable hm hw hC) hC he

end
end «2610.05164v2».Filters
