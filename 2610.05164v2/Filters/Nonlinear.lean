import «2610.05164v2».Filters.JostRegularity
import «2610.05164v2».Filters.RiccatiUniqueness
import «2610.05164v2».Filters.GroundComparison

/-!
Article: 2610.05164v2, Lemma 11.
Nonlinear.
Use: `«2610.05164v2».Filters.nonlinear_le_coordinate` feeds
`«2610.05164v2».Comparison.determinantState_mem_triangle` (determinant State mem triangle).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `nonlinear` of type `ℝ` by `jostSlope s m x/jost s m x`.

Use: `«2610.05164v2».Filters.nonlinear_unique` uses this definition to establish the identity
`r=nonlinear s m`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.
-/
def nonlinear (s : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ := jostSlope s m x/jost s m x

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (nonlinear s m)
a b`.

Use: `«2610.05164v2».Filters.nonlinear_continuous` uses this assertion to establish continuity
of the displayed function: `Continuous (nonlinear s m)`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_c1`,
`«2610.05164v2».Filters.jost_positive`, `«2610.05164v2».Filters.jostSlope_locallyAC` with the
arguments shown in the proof.
-/
theorem nonlinear_locallyAC {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (a b : ℝ) : AbsolutelyContinuousOnInterval (nonlinear s m) a b := by
  have hi := (jost_c1 hm hn hs).inv (fun x => (jost_positive hm hn hs x).ne')
  apply ((jostSlope_locallyAC hm hn hs a b).mul hi.contDiffOn.absolutelyContinuousOnInterval).congr
  intro x _
  exact (div_eq_mul_inv _ _).symm

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (nonlinear s
m) (s*m x-2*nonlinear s m x-(nonlinear s m x)^2) x`.

Use: `«2610.05164v2».Filters.nonlinear_unique` uses this assertion to establish the identity
`r=nonlinear s m`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem nonlinear_derivative {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ x, HasDerivAt (nonlinear s m) (s*m x-2*nonlinear s m x-(nonlinear s m x)^2) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [jost_second_derivative hm hn hs] with x hx
  have h := hx.div (jost_hasDerivAt hm hn hs x) (jost_positive hm hn hs x).ne'
  convert h using 1
  · rfl
  · dsimp only [nonlinear]
    field_simp [(jost_positive hm hn hs x).ne']

/--
Membership in the specified domain/enclosure: `nonlinear s m x ∈ Icc (0:ℝ) (s*causal 2 m x)`.

Use: `«2610.05164v2».Filters.nonlinear_integrable` rewrites with this assertion to establish
integrability of the displayed function: `Integrable (nonlinear s m)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem nonlinear_bounds {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : nonlinear s m x ∈ Icc (0:ℝ) (s*causal 2 m x) := by
  -- Separate `t ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  constructor
  · exact div_nonneg (jostSlope_nonneg hm hn hs x) (jost_positive hm hn hs x).le
  · have hj := jost_forcing_integrable hm hn hs
    have hi : causal 2 (fun t => m t*jost s m t) x ≤ causal 2 m x*jost s m x := by
      rw [causal_integral,causal_integral,← integral_mul_const]
      apply integral_mono (kernel_mul_integrable (by norm_num : (0:ℝ) ≤ 2) hj x)
        ((kernel_mul_integrable (by norm_num : (0:ℝ) ≤ 2) hm x).mul_const _)
      intro t
      by_cases ht : t ≤ x
      · exact (show kernel 2 x t*(m t*jost s m t) ≤ kernel 2 x t*m t*jost s m x from by
          have h := mul_le_mul_of_nonneg_left (jost_monotone hm hn hs ht)
            (mul_nonneg (kernel_nonneg 2 x t) (hn t))
          simpa only [mul_assoc] using h)
      · simp [kernel,ht]
    apply (div_le_iff₀ (jost_positive hm hn hs x)).mpr
    change s*causal 2 (fun t => m t*jost s m t) x ≤ (s*causal 2 m x)*jost s m x
    exact (mul_le_mul_of_nonneg_left hi hs).trans_eq (by ring)

/--
Continuity of the displayed function: `Continuous (nonlinear s m)`.

Use: `«2610.05164v2».Filters.nonlinear_integrable` uses this continuity result to establish
integrability of the displayed function: `Integrable (nonlinear s m)`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.locallyAC_continuous`,
`«2610.05164v2».Filters.nonlinear_locallyAC` with the arguments shown in the proof.
-/
theorem nonlinear_continuous {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Continuous (nonlinear s m) :=
  locallyAC_continuous (nonlinear_locallyAC hm hn hs)

/--
Integrability of the displayed function: `Integrable (nonlinear s m)`.

Use: `«2610.05164v2».Calibration.Data.calibrationFilter_integrable` uses this integrability
result to establish integrability of the displayed function: `Integrable (C.calibrationFilter
hm hn)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_integrable`,
`«2610.05164v2».Filters.nonlinear_continuous`, `«2610.05164v2».Filters.nonlinear_bounds` with
the arguments shown in the proof.
-/
theorem nonlinear_integrable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Integrable (nonlinear s m) := by
  apply ((causal_integrable (by norm_num : (0:ℝ) < 2) hm).const_mul s).mono'
    (nonlinear_continuous hm hn hs).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (nonlinear_bounds hm hn hs x).1]
    exact (nonlinear_bounds hm hn hs x).2)

/--
Convergence along the specified source filter to the specified limit: `Tendsto (nonlinear s m)
atBot (𝓝 0) ∧ Tendsto (nonlinear s m) atTop (𝓝 0)`.

Use: `«2610.05164v2».Filters.nonlinear_unique` uses this limit to establish the identity
`r=nonlinear s m`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_tendsto_atBot`,
`«2610.05164v2».Filters.causal_tendsto_atTop`, `«2610.05164v2».Filters.nonlinear_bounds` with
the arguments shown in the proof.
-/
theorem nonlinear_limits {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Tendsto (nonlinear s m) atBot (𝓝 0) ∧
      Tendsto (nonlinear s m) atTop (𝓝 0) := by
  -- Record the convergence hleft with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hleft : Tendsto (fun x => s*causal 2 m x) atBot (𝓝 0) := by
    simpa only [mul_zero] using (causal_tendsto_atBot (by norm_num : (0:ℝ) ≤ 2) hm).const_mul s
  -- Record the convergence hright with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hright : Tendsto (fun x => s*causal 2 m x) atTop (𝓝 0) := by
    simpa only [mul_zero] using (causal_tendsto_atTop (by norm_num : (0:ℝ) < 2) hm).const_mul s
  exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hleft
      (fun x => (nonlinear_bounds hm hn hs x).1) (fun x => (nonlinear_bounds hm hn hs x).2),
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hright
      (fun x => (nonlinear_bounds hm hn hs x).1) (fun x => (nonlinear_bounds hm hn hs x).2)⟩

/--
Exact identity `r=nonlinear s m`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Proposition 3.

Proof: Use the identities/estimates `«2610.05164v2».Filters.riccati_unique`,
`«2610.05164v2».Filters.nonlinear_locallyAC`, `«2610.05164v2».Filters.nonlinear_derivative`
with the arguments shown in the proof.
-/
theorem nonlinear_unique {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) {r : ℝ → ℝ}
    (hac : ∀ a b, AbsolutelyContinuousOnInterval r a b)
    (hd : ∀ᵐ x, HasDerivAt r (s*m x-2*r x-(r x)^2) x)
    (hl : Tendsto r atBot (𝓝 0)) : r=nonlinear s m :=
  riccati_unique hac (nonlinear_locallyAC hm hn hs) hd (nonlinear_derivative hm hn hs)
    hl (nonlinear_limits hm hn hs).1

/--
The stated quantitative bound `nonlinear s m x ≤ s/groundParameter hm hn*G.q x`.

Use: `«2610.05164v2».Calibration.Data.calibrationFilter_bounds` uses this bound to establish
membership in the specified domain/enclosure: `C.calibrationFilter hm hn x ∈ Icc (0:ℝ) (G.q
x)`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem nonlinear_le_coordinate {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    nonlinear s m x ≤ s/groundParameter hm hn*G.q x := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  calc
    _ ≤ s*causal 2 m x := (nonlinear_bounds hm hn hs x).2
    _ = s/groundParameter hm hn*linear hm hn x := by
      dsimp [linear]
      field_simp [G.coupling_positive.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (linear_le_coordinate G x) (div_nonneg hs G.coupling_positive.le)

end
end «2610.05164v2».Filters
