import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Article: chebyshev2, Lemma 5.
The inverse is division by the same multiplier; null endpoint zeros do not weaken the unitary
statement.
Use: `chebyshev2.Continuum.L2Weight.equiv` feeds
`chebyshev2.SineContinuum.affineLegendreUnitary_ae` (affine Legendre Unitary ae).
Proof chain: `chebyshev2.SineContinuum.legendreV_domain` — chebyshev2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
-/
namespace chebyshev2.Continuum
noncomputable section
open MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [MeasurableSpace α]

/--
A real measurable multiplier, nonzero almost everywhere. The weight need not be bounded or
bounded away from zero.

Use: `chebyshev2.Continuum.L2Weight.base_ac` uses this record of data and proof obligations
to establish `μ ≪ W.measure`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
structure L2Weight (μ : Measure α) where
  /-- Measurable weight multiplying representatives of L² classes. -/
  w : α → ℝ
  /-- Measurability needed to define the weighted measure and multiplication map. -/
  measurable : Measurable w
  /-- The weight is nonzero almost everywhere, allowing the reciprocal map to invert multiplication on equivalence classes. -/
  nonzero : ∀ᵐ x ∂μ, w x ≠ 0

namespace L2Weight
variable {μ : Measure α} (W : L2Weight μ)

/--
Defines `density` of type `ℝ≥0∞` by `ENNReal.ofReal (W.w x^2)`.

Use: `chebyshev2.Continuum.L2Weight.measure` uses this definition in the displayed
construction of `measure`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def density (x : α) : ℝ≥0∞ := ENNReal.ofReal (W.w x^2)
/--
Defines `measure` of type `Measure α` by `μ.withDensity W.density`.

Use: `chebyshev2.Continuum.L2Weight.memLp_div` uses this definition to establish the stated
quantitative bound `MemLp (fun x => g x/W.w x) 2 W.measure`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def measure : Measure α := μ.withDensity W.density

/--
Measurability of the displayed map: `Measurable W.density`.

Use: `chebyshev2.Continuum.L2Weight.base_ac` uses this measurability result to establish
the precise assertion is `μ ≪ W.measure`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem measurable_density : Measurable W.density := W.measurable.pow_const 2 |>.ennreal_ofReal

/--
The precise assertion is `μ ≪ W.measure`.

Use: `chebyshev2.Continuum.L2Weight.isometry_surjective` uses this assertion to establish
the precise assertion is `Function.Surjective W.isometry`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem base_ac : μ ≪ W.measure := by
  apply withDensity_absolutelyContinuous' W.measurable_density.aemeasurable
  filter_upwards [W.nonzero] with x hx
  exact (ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hx)).ne'

/--
The precise assertion is `W.measure ≪ μ`.

Use: `chebyshev2.Continuum.L2Weight.memLp_div` uses this assertion to establish the stated
quantitative bound `MemLp (fun x => g x/W.w x) 2 W.measure`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem weight_ac : W.measure ≪ μ := withDensity_absolutelyContinuous _ _

/--
The stated quantitative bound `MemLp (fun x => W.w x*f x) 2 μ`.

Use: `chebyshev2.Continuum.L2Weight.mul` uses this identity in the displayed construction
of `mul`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Use the identities/estimates `chebyshev2.Continuum.L2Weight.base_ac`,
`chebyshev2.Continuum.L2Weight.measurable_density` with the arguments shown in the proof.
-/
theorem memLp_mul (f : Lp ℝ 2 W.measure) : MemLp (fun x => W.w x*f x) 2 μ := by
  have hm : AEStronglyMeasurable f μ := (Lp.aestronglyMeasurable f).mono_ac W.base_ac
  apply (memLp_two_iff_integrable_sq (W.measurable.aestronglyMeasurable.mul hm)).mpr
  have hi := (integrable_withDensity_iff_integrable_smul' W.measurable_density
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp (Lp.memLp f).integrable_sq
  simpa only [density,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul,Pi.mul_apply,mul_pow] using hi

/--
Defines `mul` of type `Lp ℝ 2 μ` by `(W.memLp_mul f).toLp _`.

Use: `chebyshev2.Continuum.L2Weight.isometry` uses this definition in the displayed
construction of `isometry`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def mul (f : Lp ℝ 2 W.measure) : Lp ℝ 2 μ := (W.memLp_mul f).toLp _

/--
Exact identity `W.mul f=ᵐ[μ] (fun x => W.w x*f x)`.

Use: `chebyshev2.Continuum.L2Weight.isometry_surjective` uses this identity to establish
the precise assertion is `Function.Surjective W.isometry`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Use the identities/estimates `chebyshev2.Continuum.L2Weight.memLp_mul` with the
arguments shown in the proof.
-/
theorem mul_ae (f : Lp ℝ 2 W.measure) : W.mul f=ᵐ[μ] (fun x => W.w x*f x) :=
  (W.memLp_mul f).coeFn_toLp

/--
Multiplication by the square root of a density is a genuine L² isometry.

Use: `chebyshev2.Continuum.L2Weight.equiv` uses this definition in the displayed
construction of `equiv`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def isometry : Lp ℝ 2 W.measure →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toFun := W.mul
  map_add' f g := by
    apply Lp.ext
    have hf := W.mul_ae f
    have hg := W.mul_ae g
    have hfg := W.mul_ae (f+g)
    have ha := W.base_ac.ae_eq (Lp.coeFn_add f g)
    filter_upwards [hf,hg,hfg,ha,Lp.coeFn_add (W.mul f) (W.mul g)] with x hf hg hfg ha hb
    rw [hfg,ha,hb]
    simp only [Pi.add_apply]
    rw [hf,hg,mul_add]
  map_smul' c f := by
    apply Lp.ext
    have hf := W.mul_ae f
    have hcf := W.mul_ae (c • f)
    have ha := W.base_ac.ae_eq (Lp.coeFn_smul c f)
    filter_upwards [hf,hcf,ha,Lp.coeFn_smul c (W.mul f)] with x hf hcf ha hb
    simp only [RingHom.id_apply] at hb ⊢
    rw [hcf,ha,hb]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hf]
    ring
  norm_map' f := by
    change ‖W.mul f‖=‖f‖
    have hi : inner ℝ (W.mul f) (W.mul f)=inner ℝ f f := by
      rw [L2.inner_def,L2.inner_def]
      have hm := W.mul_ae f
      have he : (fun x => inner ℝ (W.mul f x) (W.mul f x))=ᵐ[μ]
          (fun x => W.w x^2*(f x)^2) := by
        filter_upwards [hm] with x hx
        rw [hx]
        change (W.w x*f x)*(W.w x*f x)=W.w x^2*(f x)^2
        ring
      rw [integral_congr_ae he]
      change _=(∫ x, inner ℝ (f x) (f x) ∂μ.withDensity W.density)
      rw [integral_withDensity_eq_integral_toReal_smul
        W.measurable_density (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with x
      change W.w x^2*(f x)^2=(ENNReal.ofReal (W.w x^2)).toReal*(f x*f x)
      rw [ENNReal.toReal_ofReal (sq_nonneg _)]
      ring
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg (W.mul f),norm_nonneg f]

/--
The stated quantitative bound `MemLp (fun x => g x/W.w x) 2 W.measure`.

Use: `chebyshev2.Continuum.L2Weight.isometry_surjective` uses this identity to establish
the precise assertion is `Function.Surjective W.isometry`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity. Prove equality of functions by
evaluating both sides at an arbitrary argument.
-/
theorem memLp_div (g : Lp ℝ 2 μ) : MemLp (fun x => g x/W.w x) 2 W.measure := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hm : AEStronglyMeasurable (fun x => g x/W.w x) W.measure :=
    by
      convert ((Lp.aestronglyMeasurable g).mul W.measurable.inv.aestronglyMeasurable).mono_ac W.weight_ac using 1
      funext x
      exact div_eq_mul_inv _ _
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (integrable_withDensity_iff_integrable_smul' W.measurable_density
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  apply (Lp.memLp g).integrable_sq.congr
  filter_upwards [W.nonzero] with x hx
  simp only [density,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]
  field_simp

/--
The precise assertion is `Function.Surjective W.isometry`.

Use: `chebyshev2.Continuum.L2Weight.equiv` uses this assertion in the displayed
construction of `equiv`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem isometry_surjective : Function.Surjective W.isometry := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  intro g
  let f := (W.memLp_div g).toLp (fun x => g x/W.w x)
  refine ⟨f,?_⟩
  apply Lp.ext
  have hf := W.base_ac.ae_eq (W.memLp_div g).coeFn_toLp
  filter_upwards [W.mul_ae f,hf,W.nonzero] with x hm hf hx
  change W.mul f x=g x
  rw [hm,hf]
  field_simp

/--
The inverse is division by the same multiplier; null endpoint zeros do not weaken the unitary
statement.

Use: `chebyshev2.SineContinuum.affineLegendreUnitary` uses this definition in the displayed
construction of `affineLegendreUnitary`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def equiv : Lp ℝ 2 W.measure ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective W.isometry W.isometry_surjective

end L2Weight
end
end chebyshev2.Continuum
