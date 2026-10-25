import chebyshev2.HalfLine.GreenEnergy

/-!
Article: chebyshev2, Theorem 3.3.
The literal half-line energy formula of C.1, for arbitrary signed L1 data.
Use: `chebyshev2.HalfLine.greenSolution_energy` feeds
`chebyshev2.HalfLine.greenSolution_energy_of_integrableOn` (green Solution energy of integrable
On).
-/
namespace chebyshev2.HalfLine
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.Sobolev chebyshev2.GroundState
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Smoothness to the stated order: `ContDiff ℝ 1 (greenSolution x j)`.

Use: `chebyshev2.HalfLine.greenSolution_regular_of_integrableOn` uses this assertion to
establish smoothness to the stated order: `ContDiff ℝ 1 (greenSolution x j) ∧ (∀ a b,
AbsolutelyContinuousOnInterval (greenSlope x j) a b)`.

Article: chebyshev2, Theorem 3.3.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem greenSolution_c1 {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    ContDiff ℝ 1 (greenSolution x j) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (greenSolution_hasDerivAt hj x t).differentiableAt,?_⟩
  have he : deriv (greenSolution x j)=greenSlope x j :=
    funext (fun t => (greenSolution_hasDerivAt hj x t).deriv)
  rw [he]
  exact locallyAC_continuous (greenSlope_locallyAC hj x)

/--
Exact identity `H1.slope (greenElement x j)=ᵐ[volume] (Iio x).indicator (greenSlope x j)`.

Use: `chebyshev2.HalfLine.greenSlope_square_integrable` uses this identity to establish
integrability on the stated domain: `IntegrableOn (fun t => (greenSlope x j t)^2) (Iio x)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem greenElement_slope {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    H1.slope (greenElement x j)=ᵐ[volume] (Iio x).indicator (greenSlope x j) := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hn : ∀ᵐ t ∂volume, t ≠ x := by simp [ae_iff]
  filter_upwards [(H1.regular (greenElement x j)).derivative_ae,hn] with t ht hne
  by_cases htx : t < x
  · rw [indicator_of_mem (show t ∈ Iio x from htx)]
    have he : H1.rep (greenElement x j)=ᶠ[𝓝 t] greenSolution x j := by
      filter_upwards [Iio_mem_nhds htx] with z hz
      exact greenElement_rep_left j hz.le
    exact ht.unique ((greenSolution_hasDerivAt hj x t).congr_of_eventuallyEq he)
  · rw [indicator_of_notMem (show t ∉ Iio x from htx)]
    have hxt : x < t := lt_of_le_of_ne (le_of_not_gt htx) (Ne.symm hne)
    have he : H1.rep (greenElement x j)=ᶠ[𝓝 t] (fun _ => (0:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hxt] with z hz
      exact greenElement_rep_right hj hz.le
    exact ht.unique ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he)

/--
Integrability on the stated domain: `IntegrableOn (fun t => (greenSolution x j t)^2) (Iio x)`.

Use: `chebyshev2.HalfLine.greenSolution_energy` rewrites with this integrability result to
establish the precise assertion is `(∫ t in Iio x, j t*greenSolution x j t)= ∫ t in Iio x,
(greenSlope x j t)^2+(greenSolution x j t)^2`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem greenSolution_square_integrable {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    IntegrableOn (fun t => (greenSolution x j t)^2) (Iio x) := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have h := (H1.regular (greenElement x j)).value_memLp.integrable_sq
  rw [greenElement_rep hj x] at h
  have he : (fun t => ((Iio x).indicator (greenSolution x j) t)^2)=
      (Iio x).indicator (fun t => (greenSolution x j t)^2) := by
    funext t
    by_cases ht : t < x <;> simp [ht]
  rw [he] at h
  exact (integrable_indicator_iff measurableSet_Iio).mp h

/--
Integrability on the stated domain: `IntegrableOn (fun t => (greenSlope x j t)^2) (Iio x)`.

Use: `chebyshev2.HalfLine.greenSolution_energy` rewrites with this integrability result to
establish the precise assertion is `(∫ t in Iio x, j t*greenSolution x j t)= ∫ t in Iio x,
(greenSlope x j t)^2+(greenSolution x j t)^2`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem greenSlope_square_integrable {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    IntegrableOn (fun t => (greenSlope x j t)^2) (Iio x) := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have h := (H1.regular (greenElement x j)).derivative_memLp.integrable_sq
  have he : (fun t => (H1.slope (greenElement x j) t)^2)=ᵐ[volume]
      (Iio x).indicator (fun t => (greenSlope x j t)^2) := by
    filter_upwards [greenElement_slope hj x] with t ht
    rw [ht]
    by_cases hz : t < x <;> simp [hz]
  exact (integrable_indicator_iff measurableSet_Iio).mp (h.congr he)

/--
The literal half-line energy formula of C.1, for arbitrary signed L1 data.

The precise assertion is `(∫ t in Iio x, j t*greenSolution x j t)= ∫ t in Iio x, (greenSlope x
j t)^2+(greenSolution x j t)^2`.

Use: `chebyshev2.HalfLine.greenSolution_energy_of_integrableOn` uses this identity to
establish the precise assertion is `(∫ t in Iio x, j t*greenSolution x j t)= ∫ t in Iio x,
(greenSlope x j t)^2+(greenSolution x j t)^2`.

Article: chebyshev2, Theorem 3.3.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Identify the summands/integrands
on their required domain before replacing the sum or integral.
-/
theorem greenSolution_energy {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    (∫ t in Iio x, j t*greenSolution x j t)=
      ∫ t in Iio x, (greenSlope x j t)^2+(greenSolution x j t)^2 := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [← greenElement_energy hj x,H1.norm_sq_energy]
  have hs : (∫ t, (H1.slope (greenElement x j) t)^2)=∫ t in Iio x, (greenSlope x j t)^2 := by
    rw [← integral_indicator measurableSet_Iio]
    apply integral_congr_ae
    filter_upwards [greenElement_slope hj x] with t ht
    rw [ht]
    by_cases hz : t < x <;> simp [hz]
  have hv : (∫ t, (H1.rep (greenElement x j) t)^2)=∫ t in Iio x, (greenSolution x j t)^2 := by
    rw [greenElement_rep hj x, ← integral_indicator measurableSet_Iio]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by by_cases ht : t < x <;> simp [ht])
  rw [hs,hv,integral_add (greenSlope_square_integrable hj x) (greenSolution_square_integrable hj x)]

end
end chebyshev2.HalfLine
