import polyak.Waves.Interpolation
import polyak.Waves.Dynamics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Article: (polyakwave), (abg), and the Chebyshev-coordinate spectral formulation.
Use: exact passage from the complex planar wave to independent parameters (v,t).
Proof: Euler's formula, cosh²-sinh²=1, and division-free Chebyshev identities.
-/

noncomputable section

open MeasureTheory

namespace polyak.Waves

open Spectral

/-- Article: m=cosh(v+iω). Use: continuous planar gradient multiplier in cosine coordinates. -/
def polyakMultiplier (v : ℝ) : C(Frequency, ℂ) where
  toFun c := Complex.ofReal (Real.cosh v * (c : ℝ)) +
    Complex.ofReal (Real.sinh v * Real.sin (Real.arccos c)) * Complex.I
  continuous_toFun := by fun_prop

/-- Article: real part of the Polyak multiplier. Proof: its explicit coordinate definition. -/
@[simp] theorem polyakMultiplier_re (v : ℝ) (c : Frequency) :
    (polyakMultiplier v c).re = Real.cosh v * c := by
  simp only [polyakMultiplier, ContinuousMap.coe_mk, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero]

/-- Article: imaginary part of the Polyak multiplier. Proof: its explicit coordinate definition. -/
@[simp] theorem polyakMultiplier_im (v : ℝ) (c : Frequency) :
    (polyakMultiplier v c).im = Real.sinh v * Real.sin (Real.arccos c) := by
  simp only [polyakMultiplier, ContinuousMap.coe_mk, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    add_zero, zero_add]

/-- Article: g=1-c²-sinh²v. Proof: hyperbolic and trigonometric Pythagorean identities. -/
theorem polyakMultiplier_normSq (v : ℝ) (c : Frequency) :
    Complex.normSq (polyakMultiplier v c) = (c : ℝ) ^ 2 + Real.sinh v ^ 2 := by
  have hs := Real.sin_sq_add_cos_sq (Real.arccos (c : ℝ))
  rw [Real.cos_arccos c.property.1 c.property.2] at hs
  have hsin : Real.sin (Real.arccos (c : ℝ)) ^ 2 = 1 - (c : ℝ) ^ 2 := by linarith
  calc
    _ = Real.cosh v ^ 2 * (c : ℝ) ^ 2 +
        Real.sinh v ^ 2 * Real.sin (Real.arccos (c : ℝ)) ^ 2 := by
      simp only [Complex.normSq_apply, polyakMultiplier_re, polyakMultiplier_im]
      ring
    _ = _ := by rw [Real.cosh_sq, hsin]; ring

/-- Article: complex g and cosine-coordinate g agree. Proof: the norm-square identity. -/
theorem spectrumG_polyak (ν : Spectrum) (v : ℝ) :
    spectrumG ν (polyakMultiplier v) = meanG ν (Real.sinh v) := by
  rw [meanG_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun c => by
    simp only [polyakMultiplier_normSq, Spectral.g]
    ring)

/-- Article: first Chebyshev bridge in the lag constraints. Proof: c=cos(arccos c). -/
theorem chebT_arccos (n : ℕ) (c : Frequency) :
    chebT n c = Real.cos (n * Real.arccos c) := by
  have hh := chebT_cos n (Real.arccos (c : ℝ))
  rwa [Real.cos_arccos c.property.1 c.property.2] at hh

/-- Article: complex aₙ and polynomial aₙ agree. Proof: the g and T identities. -/
theorem spectrumA_polyak (ν : Spectrum) (v t : ℝ) (n : ℕ) :
    spectrumA ν (polyakMultiplier v) t n = meanA ν (Real.sinh v) t n := by
  rw [meanA_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun c => by
    dsimp only [lagA, g, lagD]
    rw [polyakMultiplier_normSq, chebT_arccos]
    ring)

/-- Article: second Chebyshev bridge, including the endpoints c=±1. Proof: multiply the
sine identity by sin ω, avoiding every division by sin ω. -/
theorem polyak_skew (v : ℝ) (n : ℕ) (hn : 1 ≤ n) (c : Frequency) :
    2 * (polyakMultiplier v c).im * Real.sin (n * Real.arccos c) =
      lagB (Real.sinh v) n c := by
  have he : chebU (n - 1) c * Real.sin (Real.arccos c) =
      Real.sin (n * Real.arccos c) := by
    have hh := chebU_sin (n - 1) (Real.arccos c)
    rw [Real.cos_arccos c.property.1 c.property.2] at hh
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      exact_mod_cast Nat.sub_add_cancel hn
    rwa [hcast] at hh
  have hs := Real.sin_sq_add_cos_sq (Real.arccos (c : ℝ))
  rw [Real.cos_arccos c.property.1 c.property.2] at hs
  rw [← he, polyakMultiplier_im]
  unfold lagB
  have hsin : Real.sin (Real.arccos (c : ℝ)) ^ 2 = 1 - (c : ℝ) ^ 2 := by linarith
  calc
    _ = 2 * Real.sinh v * Real.sin (Real.arccos (c : ℝ)) ^ 2 * chebU (n - 1) c := by ring
    _ = _ := by rw [hsin]

/-- Article: complex bₙ and polynomial bₙ agree. Proof: integrate the division-free identity. -/
theorem spectrumB_polyak (ν : Spectrum) (v : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    spectrumB ν (polyakMultiplier v) n = meanB ν (Real.sinh v) n := by
  rw [meanB_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun c => polyak_skew v n hn c)



/-- Article: m=cosh(v+iω). Proof: the complex addition formulas and real cosine inversion. -/
theorem polyakMultiplier_eq_cosh (v : ℝ) (c : Frequency) :
    polyakMultiplier v c = Complex.cosh ((v : ℂ) + (Real.arccos c : ℂ) * Complex.I) := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_arccos c.property.1 c.property.2]
  simp only [polyakMultiplier, ContinuousMap.coe_mk, Complex.ofReal_mul]
  ring

/-- Article: Polyak multiplier from the actual recurrence. Proof: z=q exp(v+iω), with v=t-log q. -/
theorem multiplier_polyak (q t ω : ℝ) (hq : 0 < q) :
    multiplier 0 (2 * q) (q ^ 2) t ω =
      Complex.cosh (((t - Real.log q : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
  let s : ℂ := ((t - Real.log q : ℝ) : ℂ) + (ω : ℂ) * Complex.I
  have hqexp : Complex.exp (Real.log q : ℂ) = (q : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hq]
  have hz : z t ω = Complex.exp s * (q : ℂ) := by
    rw [← hqexp, ← Complex.exp_add]
    unfold z
    congr 1
    dsimp [s]
    push_cast
    ring
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hs := Complex.exp_ne_zero s
  change (z t ω + (q ^ 2 : ℝ) / z t ω - (0 : ℂ)) / (2 * q : ℝ) = Complex.cosh s
  rw [hz]
  simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_zero,
    Complex.cosh, Complex.exp_neg]
  field_simp

/-- Article: independent (v,t) feasibility is precisely interpolation of the Polyak wave.
Proof: substitute the exact g, a, b moment identities, preserving every lag. -/
theorem mixtureFeasible_polyak_iff (ν : Spectrum) (v C t : ℝ) :
    MixtureFeasible ν (polyakMultiplier v) C t ↔ Feasible v t ν C := by
  simp only [MixtureFeasible, Feasible, FeasibleU, spectrumG_polyak, spectrumA_polyak]
  constructor
  · rintro ⟨hC, h⟩
    refine ⟨hC, fun n hn => ?_⟩
    simpa only [spectrumB_polyak ν v n hn] using h n hn
  · rintro ⟨hC, h⟩
    refine ⟨hC, fun n hn => ?_⟩
    simpa only [spectrumB_polyak ν v n hn] using h n hn

/-- Article: exact spectral interpolation for independent Polyak parameters. Use: one function
for the whole infinite wave table, including unbounded data and the minimizer.
Proof: general Hilbert interpolation and the exact moment bridge. -/
theorem polyak_interpolation_iff (ν : Spectrum) (v C t : ℝ) :
    (∃ ψ : WaveSpace ν → ℝ, NormalizedSmooth ψ ∧ ∀ i,
      ψ (mixturePosition ν t i) = mixtureValue ν (polyakMultiplier v) C t i ∧
      _root_.gradient ψ (mixturePosition ν t i) = mixtureGradient ν (polyakMultiplier v) t i) ↔
      Feasible v t ν C := by
  rw [mixture_interpolation_iff, mixtureFeasible_polyak_iff]



/-- Article: actual Polyak tuning in cosine coordinates. Proof: pointwise multiplier identity. -/
theorem multiplierMap_polyak (q t : ℝ) (hq : 0 < q) :
    multiplierMap 0 (2 * q) (q ^ 2) t = polyakMultiplier (t - Real.log q) := by
  ext c
  change multiplier 0 (2 * q) (q ^ 2) t (Real.arccos c) = _
  rw [multiplier_polyak q t (Real.arccos c) hq, polyakMultiplier_eq_cosh]

/-- Article: Polyak normalized recurrence of the realized spectrum.
Proof: the general L² recurrence and the actual multiplier bridge. -/
theorem mixture_polyak_recurrence (ν : Spectrum) (q t : ℝ) (hq : 0 < q) (k : ℕ) :
    mixturePosition ν t (some (k + 2)) =
      (2 * q) • mixtureGradient ν (polyakMultiplier (t - Real.log q)) t (some (k + 1)) -
      q ^ 2 • mixturePosition ν t (some k) := by
  have h := mixture_recurrence ν 0 (2 * q) (q ^ 2) t (by positivity) k
  simpa only [multiplierMap_polyak q t hq, zero_smul, zero_add] using h



/-- Article: feasible Polyak spectra give actual normalized wave trajectories.
Use: one function for every time index and every probability spectrum; the recurrence uses its
actual gradient. This is the wave initialization, before the separate startup construction.
Proof: arbitrary-set interpolation, the multiplier bridge, and the exact L² recurrence. -/
theorem exists_polyak_wave (ν : Spectrum) (q C t : ℝ) (hq : 0 < q)
    (h : Feasible (t - Real.log q) t ν C) :
    ∃ ψ : WaveSpace ν → ℝ, NormalizedSmooth ψ ∧
      (∀ i, ψ (mixturePosition ν t i) = mixtureValue ν (polyakMultiplier (t - Real.log q)) C t i ∧
        _root_.gradient ψ (mixturePosition ν t i) =
          mixtureGradient ν (polyakMultiplier (t - Real.log q)) t i) ∧
      (∀ k : ℕ, mixturePosition ν t (some (k + 2)) =
        (2 * q) • _root_.gradient ψ (mixturePosition ν t (some (k + 1))) -
          q ^ 2 • mixturePosition ν t (some k)) ∧
      (∀ k : ℕ, ‖mixturePosition ν t (some k)‖ = Real.exp (k * t)) := by
  obtain ⟨ψ, hψ, hi⟩ := (polyak_interpolation_iff ν (t - Real.log q) C t).mpr h
  refine ⟨ψ, hψ, hi, fun k => ?_, fun k => norm_mixturePosition ν t k⟩
  rw [(hi (some (k + 1))).2]
  exact mixture_polyak_recurrence ν q t hq k

end polyak.Waves
