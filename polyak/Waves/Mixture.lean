import polyak.Waves.Complex
import polyak.Spectral.Feasibility
import Mathlib.MeasureTheory.Function.L2Space

/-!
Article: Lemma spectralinterp, arbitrary probability spectra.
Use: actual real Hilbert-space realization, including nonatomic spectra and infinite tables.
Proof: continuous maps on the compact frequency carrier are in L²; its inner product is
exactly the integral of the planar inner products. All interpolation slacks commute with averaging.
Source: mathlib ContinuousMap.toLp and L2.inner_def.
-/

noncomputable section

open MeasureTheory

namespace polyak.Waves

open Interpolation Spectral

/-- Article: L²(ν;ℂ), regarded as a real Hilbert space. Use: realize every probability spectrum. -/
abbrev WaveSpace (ν : Spectrum) := Lp ℂ 2 (ν : Measure Frequency)

/-- Article: continuous planar data in L². Use: a real linear realization map. -/
def lift (ν : Spectrum) : C(Frequency, ℂ) →L[ℝ] WaveSpace ν :=
  ContinuousMap.toLp 2 (ν : Measure Frequency) ℝ

/-- Article: averaged inner products. Proof: the L² definition and the a.e. toLp representatives. -/
theorem inner_lift (ν : Spectrum) (f g : C(Frequency, ℂ)) :
    inner ℝ (lift ν f) (lift ν g) = ∫ c, inner ℝ (f c) (g c) ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℝ) (ν : Measure Frequency),
    g.coeFn_toLp (p := 2) (𝕜 := ℝ) (ν : Measure Frequency)] with c hf hg
  dsimp only [lift]
  rw [hf, hg]

/-- Article: averaged squared norms. Proof: specialize the inner-product identity to f=f. -/
theorem norm_sq_lift (ν : Spectrum) (f : C(Frequency, ℂ)) :
    ‖lift ν f‖ ^ 2 = ∫ c, ‖f c‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, inner_lift]
  simp only [real_inner_self_eq_norm_sq]

/-- Article: averaging R. Use: the exact radius for an infinite-dimensional orthogonal sum. -/
theorem datumR_lift {I : Type*} (ν : Spectrum) (x σ : I → C(Frequency, ℂ)) (i j : I) :
    datumR (fun k => lift ν (x k)) (fun k => lift ν (σ k)) i j =
      ∫ c, datumR (fun k => x k c) (fun k => σ k c) i j ∂ν := by
  have hx := integrable_continuous ν (show Continuous (fun c => ‖x j c - x i c‖ ^ 2) by
    fun_prop)
  have hσ := integrable_continuous ν (show Continuous (fun c => ‖σ j c - σ i c‖ ^ 2) by
    fun_prop)
  unfold datumR
  rw [← map_sub, ← map_sub, norm_sq_lift, norm_sq_lift, integral_const_mul,
    integral_sub hx hσ]
  rfl

/-- Article: averaging T. Use: exact discrepancies for an arbitrary probability spectrum. -/
theorem datumT_lift {I : Type*} (ν : Spectrum) (x σ : I → C(Frequency, ℂ))
    (values : I → C(Frequency, ℝ)) (i j : I) :
    datumT (fun k => lift ν (x k)) (fun k => lift ν (σ k))
      (fun k => ∫ c, values k c ∂ν) i j =
      ∫ c, datumT (fun k => x k c) (fun k => σ k c) (fun k => values k c) i j ∂ν := by
  have hvj := integrable_continuous ν (values j).continuous
  have hvi := integrable_continuous ν (values i).continuous
  have hi := integrable_continuous ν
    (show Continuous (fun c => inner ℝ (σ i c + σ j c) (x j c - x i c)) by fun_prop)
  unfold datumT
  rw [← map_add, ← map_sub, inner_lift]
  have hs := integral_sub (hvj.sub hvi) (hi.const_mul (1 / 2 : ℝ))
  dsimp only [Pi.sub_apply] at hs
  dsimp only
  rw [hs, integral_sub hvj hvi, integral_const_mul]
  rfl

/-- Article: continuous positions in cosine coordinates. Use: pass every wave into L². -/
def positionMap (t : ℝ) (i : Option ℕ) : C(Frequency, ℂ) where
  toFun c := position t (Real.arccos c) i
  continuous_toFun := by
    cases i with
    | none => exact continuous_const
    | some k =>
      dsimp [position, z]
      fun_prop

/-- Article: continuous gradient data. Use: arbitrary continuous planar multipliers. -/
def gradientMap (m : C(Frequency, ℂ)) (t : ℝ) (i : Option ℕ) : C(Frequency, ℂ) :=
  m * positionMap t i

/-- Article: continuous function values. Use: one shared C across all frequencies. -/
def valueMap (m : C(Frequency, ℂ)) (C t : ℝ) (i : Option ℕ) : C(Frequency, ℝ) where
  toFun c := value (m c) C t (Real.arccos c) i
  continuous_toFun := by
    cases i with
    | none => exact continuous_const
    | some k =>
      change Continuous (fun c => (C + 2 * (m c).re) / 4 *
        Complex.normSq (positionMap t (some k) c))
      exact ((continuous_const.add (continuous_const.mul (Complex.continuous_re.comp
        m.continuous))).div_const _).mul
        (Complex.continuous_normSq.comp (positionMap t (some k)).continuous)

/-- Article: realized wave positions. Use: one Hilbert-space sequence for all k. -/
def mixturePosition (ν : Spectrum) (t : ℝ) (i : Option ℕ) : WaveSpace ν :=
  lift ν (positionMap t i)

/-- Article: realized wave gradients. Use: the interpolation table on that same space. -/
def mixtureGradient (ν : Spectrum) (m : C(Frequency, ℂ)) (t : ℝ) (i : Option ℕ) : WaveSpace ν :=
  lift ν (gradientMap m t i)

/-- Article: realized wave values. Use: exact integration of the planar values. -/
def mixtureValue (ν : Spectrum) (m : C(Frequency, ℂ)) (C t : ℝ) (i : Option ℕ) : ℝ :=
  ∫ c, valueMap m C t i c ∂ν

/-- Article: averaged g for a general tuning. Use: minimizer constraints. -/
def spectrumG (ν : Spectrum) (m : C(Frequency, ℂ)) : ℝ :=
  ∫ c, 1 - Complex.normSq (m c) ∂ν

/-- Article: averaged aₙ for a general tuning. Use: symmetric lag constraints. -/
def spectrumA (ν : Spectrum) (m : C(Frequency, ℂ)) (t : ℝ) (n : ℕ) : ℝ :=
  ∫ c, (1 - Complex.normSq (m c)) *
    (Real.cosh (n * t) - Real.cos (n * Real.arccos c)) ∂ν

/-- Article: averaged bₙ for a general tuning. Use: skew lag constraints. -/
def spectrumB (ν : Spectrum) (m : C(Frequency, ℂ)) (n : ℕ) : ℝ :=
  ∫ c, 2 * (m c).im * Real.sin (n * Real.arccos c) ∂ν



/-- Article: exact signed slacks commute with orthogonal sums. Proof: integrate R and T separately. -/
theorem datum_slack_lift {I : Type*} (ν : Spectrum) (x σ : I → C(Frequency, ℂ))
    (values : I → C(Frequency, ℝ)) (δ : ℝ) (i j : I) :
    datumR (fun k => lift ν (x k)) (fun k => lift ν (σ k)) i j +
      δ * datumT (fun k => lift ν (x k)) (fun k => lift ν (σ k))
        (fun k => ∫ c, values k c ∂ν) i j =
      ∫ c, datumR (fun k => x k c) (fun k => σ k c) i j +
        δ * datumT (fun k => x k c) (fun k => σ k c) (fun k => values k c) i j ∂ν := by
  have hr := integrable_continuous ν (show Continuous (fun c =>
      datumR (fun k => x k c) (fun k => σ k c) i j) by
    unfold datumR; fun_prop)
  have ht := integrable_continuous ν (show Continuous (fun c =>
      datumT (fun k => x k c) (fun k => σ k c) (fun k => values k c) i j) by
    unfold datumT; fun_prop)
  rw [datumR_lift, datumT_lift, integral_add hr (ht.const_mul δ), integral_const_mul]

/-- Article: integration of a signed spectral slack. Proof: real linearity and unit mass. -/
theorem integral_spectral_slack (ν : Spectrum) (m : C(Frequency, ℂ)) (C t δ : ℝ) (n : ℕ) :
    (∫ c, (1 - Complex.normSq (m c)) *
        (Real.cosh (n * t) - Real.cos (n * Real.arccos c)) -
      δ * (2 * (m c).im * Real.sin (n * Real.arccos c)) +
        δ * C * Real.sinh (n * t) ∂ν) =
    spectrumA ν m t n - δ * spectrumB ν m n + δ * C * Real.sinh (n * t) := by
  have ha := integrable_continuous ν (show Continuous (fun c : Frequency =>
      (1 - Complex.normSq (m c)) *
        (Real.cosh (n * t) - Real.cos (n * Real.arccos c))) by fun_prop)
  have hb := integrable_continuous ν (show Continuous (fun c : Frequency =>
      2 * (m c).im * Real.sin (n * Real.arccos c)) by fun_prop)
  have hs := integral_add (ha.sub (hb.const_mul δ))
    (integrable_const (δ * C * Real.sinh (n * t)))
  dsimp only [Pi.sub_apply] at hs
  rw [hs, integral_sub ha (hb.const_mul δ), integral_const_mul]
  simp [spectrumA, spectrumB]

/-- Article: exact spectral lag formula, both signs at once. Proof: integrate the planar formula. -/
theorem mixture_slack (ν : Spectrum) (m : C(Frequency, ℂ)) (C t δ : ℝ) (j n : ℕ) :
    datumR (mixturePosition ν t) (mixtureGradient ν m t) (some j) (some (j + n)) +
      δ * datumT (mixturePosition ν t) (mixtureGradient ν m t) (mixtureValue ν m C t)
        (some j) (some (j + n)) =
      (1 / 2 : ℝ) * Real.exp ((2 * j + n) * t) *
        (spectrumA ν m t n - δ * spectrumB ν m n + δ * C * Real.sinh (n * t)) := by
  unfold mixturePosition mixtureGradient mixtureValue
  rw [datum_slack_lift ν (positionMap t) (gradientMap m t) (valueMap m C t) δ]
  calc
    _ = ∫ c, (1 / 2 : ℝ) * Real.exp ((2 * j + n) * t) *
        ((1 - Complex.normSq (m c)) *
          (Real.cosh (n * t) - Real.cos (n * Real.arccos c)) -
          δ * (2 * (m c).im * Real.sin (n * Real.arccos c)) +
            δ * C * Real.sinh (n * t)) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun c => datum_slack (m c) C t (Real.arccos c) δ j n)
    _ = _ := by rw [integral_const_mul, integral_spectral_slack]

/-- Article: exact spectral minimizer formula, both signs at once. Proof: integrate the origin pair. -/
theorem mixture_star_slack (ν : Spectrum) (m : C(Frequency, ℂ)) (C t δ : ℝ) (j : ℕ) :
    datumR (mixturePosition ν t) (mixtureGradient ν m t) none (some j) +
      δ * datumT (mixturePosition ν t) (mixtureGradient ν m t) (mixtureValue ν m C t)
        none (some j) =
      (1 / 4 : ℝ) * Real.exp (2 * j * t) * (spectrumG ν m + δ * C) := by
  unfold mixturePosition mixtureGradient mixtureValue
  rw [datum_slack_lift ν (positionMap t) (gradientMap m t) (valueMap m C t) δ]
  calc
    _ = ∫ c, (1 / 4 : ℝ) * Real.exp (2 * j * t) *
        ((1 - Complex.normSq (m c)) + δ * C) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun c => datum_star_slack (m c) C t (Real.arccos c) δ j)
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_continuous ν (by fun_prop))
        (integrable_const _)]
      simp [spectrumG]

/-- Article: exact growth of an orthogonal mixture. Proof: its squared norm integrates a constant. -/
theorem norm_mixturePosition (ν : Spectrum) (t : ℝ) (k : ℕ) :
    ‖mixturePosition ν t (some k)‖ = Real.exp (k * t) := by
  have hsq : ‖mixturePosition ν t (some k)‖ ^ 2 = Real.exp (k * t) ^ 2 := by
    rw [mixturePosition, norm_sq_lift]
    have heq : (fun c : Frequency => ‖positionMap t (some k) c‖ ^ 2) =
        (fun _ => Real.exp (k * t) ^ 2) := by
      funext c
      rw [show positionMap t (some k) c = z t (Real.arccos c) ^ k from rfl, norm_z_pow]
    rw [heq]
    simp
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsq



/-- Article: prescribed common function values in Lemma spectralinterp.
Proof: the squared radial factor is independent of frequency and the spectrum has unit mass. -/
theorem mixtureValue_some (ν : Spectrum) (m : C(Frequency, ℂ)) (C t : ℝ) (k : ℕ) :
    mixtureValue ν m C t (some k) =
      (C + 2 * avg ν (fun c => (m c).re)) / 4 * Real.exp (2 * k * t) := by
  unfold mixtureValue
  have heq : (fun c : Frequency => valueMap m C t (some k) c) =
      (fun c => (C + 2 * (m c).re) / 4 * Real.exp (2 * k * t)) := by
    funext c
    change (C + 2 * (m c).re) / 4 * Complex.normSq (z t (Real.arccos c) ^ k) = _
    rw [normSq_z_pow]
  have hi : Integrable (fun c : Frequency => (m c).re) (ν : Measure Frequency) :=
    integrable_continuous ν (by fun_prop)
  rw [heq, integral_mul_const, integral_div,
    integral_add (integrable_const C) (hi.const_mul 2), integral_const_mul]
  simp [avg]

end polyak.Waves
