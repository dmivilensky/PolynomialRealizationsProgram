import chebyshev2.Continuum.MeasureOperator

/-!
Article: chebyshev2, Lemma 4.
Lemma 4(v), with the article's transport constant.
Use: `chebyshev2.Continuum.measureOperator_transport` feeds
`chebyshev2.Continuum.measureOperator_transport_extended` (Lemma 4(v) for every finite positive
coupling, including infinite transport cost).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Continuum
noncomputable section
open MeasureTheory Real Set
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Cauchy--Schwarz against the constant function, including zero mass.

The stated quantitative bound `(∫ x, f x ∂μ)^2 ≤ μ.real univ * ∫ x, f x^2 ∂μ`.

Use: `chebyshev2.Continuum.measureOperator_transport` uses this bound to establish the
precise assertion is `TraceBound (measureOperator (μ.map Prod.fst) - measureOperator (μ.map
Prod.snd)) (2 * sqrt (2 * μ.real univ * ∫ z, |z.1-z.2| ∂μ))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem integral_sq_le_mass_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) : (∫ x, f x ∂μ)^2 ≤ μ.real univ * ∫ x, f x^2 ∂μ := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let a := hf.toLp f
  have hc : MemLp (fun _ : α => (1 : ℝ)) 2 μ := memLp_const 1
  let b := hc.toLp (fun _ => (1 : ℝ))
  have he : inner ℝ a b = ∫ x, f x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hc.coeFn_toLp] with x hx hy
    change inner ℝ (a x) (b x) = f x
    rw [hx,hy]
    simp [RCLike.inner_apply]
  have ha : ‖a‖^2 = ∫ x, f x^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    change inner ℝ (a x) (a x) = f x^2
    rw [hx]
    simp [pow_two]
  have hb : ‖b‖^2 = μ.real univ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    have ht : (fun x => inner ℝ (b x) (b x)) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
      filter_upwards [hc.coeFn_toLp] with x hx
      rw [hx]
      norm_num [RCLike.inner_apply]
    rw [integral_congr_ae ht, integral_const]
    simp
  have h := norm_inner_le_norm (𝕜 := ℝ) a b
  have hs := mul_self_le_mul_self (norm_nonneg _) h
  rw [← pow_two, ← pow_two, Real.norm_eq_abs, sq_abs, mul_pow, he, ha, hb] at hs
  simpa only [mul_comm] using hs

/--
Lemma 4(v), with the article's transport constant.

The precise assertion is `TraceBound (measureOperator (μ.map Prod.fst) - measureOperator (μ.map
Prod.snd)) (2 * sqrt (2 * μ.real univ * ∫ z, |z.1-z.2| ∂μ))`.

Use: `chebyshev2.Continuum.measureOperator_transport_extended` uses this assertion to
establish the stated quantitative bound `nuclearNorm (measureOperator (μ.map
Prod.fst)-measureOperator (μ.map Prod.snd)) ≤ ENNReal.ofReal 2 * (ENNReal.ofReal 2 * μ univ *
∫⁻ z, ENNReal.ofReal |z.1-z.2| ∂μ)^(1/2 : ℝ)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_continuous`,
`chebyshev2.Continuum.feature_norm`, `chebyshev2.Continuum.integral_sq_le_mass_mul`
with the arguments shown in the proof.
-/
theorem measureOperator_transport (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hc : Integrable (fun z => |z.1-z.2|) μ) :
    TraceBound (measureOperator (μ.map Prod.fst) - measureOperator (μ.map Prod.snd))
      (2 * sqrt (2 * μ.real univ * ∫ z, |z.1-z.2| ∂μ)) := by
  -- Use the identities/estimates `chebyshev2.Continuum.feature_continuous`,
  -- `chebyshev2.Continuum.feature_norm`,
  -- `chebyshev2.Continuum.integral_sq_le_mass_mul` with the arguments shown in the proof.
  let f : ℝ × ℝ → ℝ := fun z => ‖feature z.1-feature z.2‖
  have hf : MemLp f 2 μ := by
    apply (memLp_const (2 : ℝ)).mono'
    · exact ((feature_continuous.comp continuous_fst).sub
        (feature_continuous.comp continuous_snd)).norm.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun z => by
        have h := norm_sub_le (feature z.1) (feature z.2)
        rw [feature_norm, feature_norm] at h
        simpa only [f, norm_norm, Real.norm_ofNat] using h.trans_eq (by norm_num : (1:ℝ)+1=2))
  have hs := integral_sq_le_mass_mul μ hf
  have hi : (∫ z, f z^2 ∂μ) ≤ 2 * ∫ z, |z.1-z.2| ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hf.integrable_sq (hc.const_mul 2)
    exact Filter.Eventually.of_forall (fun z => feature_distance_bound z.1 z.2)
  have hm : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
  have hcost : 0 ≤ ∫ z, |z.1-z.2| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  have hh := hs.trans (mul_le_mul_of_nonneg_left hi hm)
  have hg : 0 ≤ ∫ z, f z ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hroot := sqrt_nonneg (2 * μ.real univ * ∫ z, |z.1-z.2| ∂μ)
  have harg : 0 ≤ 2 * μ.real univ * ∫ z, |z.1-z.2| ∂μ := by positivity
  have hsqrt := sq_sqrt harg
  have hle : (∫ z, f z ∂μ) ≤ sqrt (2 * μ.real univ * ∫ z, |z.1-z.2| ∂μ) := by nlinarith
  apply (measureOperator_transport_integral μ).mono
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hle (by norm_num)

end
end chebyshev2.Continuum
