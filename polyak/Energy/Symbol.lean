import polyak.Energy.Kernel
import polyak.Energy.Circle
import polyak.Waves.Dynamics

/-!
Article: Appendix A, the exact quadratic-symbol identity in Lemma energy.
Use: the same finite quadratic kernel acts in every real Hilbert space and has
the strict certificate symbol on the frequency circle.
Proof: eliminate the gradient by the discounted recurrence, expand finite
filter outer products, and evaluate on a single exponential wave.
-/

noncomputable section

namespace polyak.Energy

open Duality Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: the discounted gradient forced by the actual recurrence. -/
def gradientFilter (A B β t : ℝ) : LinearFilter :=
  [(Real.exp t / B,1),(-A/B,0),(β*Real.exp (-t)/B,-1)]

/-- Article: the difference of two filters. -/
def filterDifference (Y X : LinearFilter) : LinearFilter := Y ++ filterScale (-1) X

/-- Article: finite kernel of the quadratic part of one signed pair inequality. -/
def pairKernel (δ : ℝ) (X Y S T : LinearFilter) : Kernel :=
  kernelScale (1/4) (filterOuter (filterDifference Y X) (filterDifference Y X)) ++
  kernelScale (-1/4) (filterOuter (filterDifference T S) (filterDifference T S)) ++
  kernelScale (-δ/2) (filterOuter (S++T) (filterDifference Y X))

/-- Article: finite kernel of the quadratic part of one minimizer inequality. -/
def starKernel (δ : ℝ) (X S : LinearFilter) : Kernel :=
  kernelScale (1/4) (filterOuter X X) ++ kernelScale (-1/4) (filterOuter S S) ++
  kernelScale (-δ/2) (filterOuter S X)

/-- Article: the difference filter evaluates to the actual vector difference. -/
@[simp] theorem filterEval_difference (Y X : LinearFilter) (f : ℤ → E) (k : ℤ) :
    filterEval (filterDifference Y X) f k = filterEval Y f k - filterEval X f k := by
  simp [filterDifference, sub_eq_add_neg]

/-- Article: exact pair quadratic kernel. Proof: finite outer-product identities. -/
@[simp] theorem kernelEval_pair (δ : ℝ) (X Y S T : LinearFilter) (f : ℤ → E) (k : ℤ) :
    kernelEval (pairKernel δ X Y S T) f k =
      pairQuadratic δ (filterEval X f k) (filterEval Y f k)
        (filterEval S f k) (filterEval T f k) := by
  simp only [pairKernel, kernelEval_append, kernelEval_scale, kernelEval_outer,
    filterEval_difference, filterEval_append, real_inner_self_eq_norm_sq]
  unfold pairQuadratic
  ring

/-- Article: exact minimizer quadratic kernel. Proof: finite outer-product identities. -/
@[simp] theorem kernelEval_star (δ : ℝ) (X S : LinearFilter) (f : ℤ → E) (k : ℤ) :
    kernelEval (starKernel δ X S) f k = starQuadratic δ (filterEval X f k) (filterEval S f k) := by
  simp only [starKernel, kernelEval_append, kernelEval_scale, kernelEval_outer,
    real_inner_self_eq_norm_sq]
  unfold starQuadratic
  ring

/-- Article: the lag-n pair kernel after recurrence elimination and discounting. -/
def lagKernel (A B β t : ℝ) (n : ℕ) (δ : ℝ) : Kernel :=
  pairKernel δ unitFilter (filterScale (Real.exp (n*t)) (filterShift n unitFilter))
    (gradientFilter A B β t)
    (filterScale (Real.exp (n*t)) (filterShift n (gradientFilter A B β t)))

/-- Article: the full finite quadratic kernel, with its actual certificate multipliers. -/
def certificateKernel (A B β t : ℝ) {m : C(Frequency, ℂ)} (cert : StrictCertificate m t) : Kernel :=
  (cert.lags.toList.flatMap fun (n : ℕ) => kernelScale (2*Real.exp (-(n*t)))
    (kernelScale (cert.α n) (lagKernel A B β t n 1) ++
      kernelScale (cert.β n) (lagKernel A B β t n (-1)))) ++
  kernelScale (4*cert.γplus) (starKernel 1 unitFilter (gradientFilter A B β t)) ++
  kernelScale (4*cert.γminus) (starKernel (-1) unitFilter (gradientFilter A B β t))

/-- Article: the discounted gradient filter has exactly the recurrence coefficients. -/
theorem filterEval_gradient (A B β t : ℝ) (f : ℤ → E) (k : ℤ) :
    filterEval (gradientFilter A B β t) f k =
      (Real.exp t / B) • f (k+1) - (A/B) • f k +
        (β*Real.exp (-t)/B) • f (k-1) := by
  simp [gradientFilter, filterEval, sub_eq_add_neg, add_assoc, neg_div]

/-- Article: actual recurrence-filtered evaluation of each lag kernel. -/
theorem kernelEval_lag (A B β t : ℝ) (n : ℕ) (δ : ℝ) (f : ℤ → E) (k : ℤ) :
    kernelEval (lagKernel A B β t n δ) f k =
      pairQuadratic δ (f k) (Real.exp (n*t) • f (k+n))
        (filterEval (gradientFilter A B β t) f k)
        (Real.exp (n*t) • filterEval (gradientFilter A B β t) f (k+n)) := by
  simp [lagKernel]

/-- Article: the complete finite kernel equals the quadratic part of Z.
Use: no spectral assumption on f; this identity holds for every real Hilbert sequence. -/
theorem kernelEval_certificate (A B β t : ℝ) {m : C(Frequency, ℂ)}
    (cert : StrictCertificate m t) (f : ℤ → E) (k : ℤ) :
    kernelEval (certificateKernel A B β t cert) f k =
      (∑ n ∈ cert.lags, 2*Real.exp (-(n*t)) *
        (cert.α n * pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
          (filterEval (gradientFilter A B β t) f k)
          (Real.exp (n*t) • filterEval (gradientFilter A B β t) f (k+n)) +
        cert.β n * pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
          (filterEval (gradientFilter A B β t) f k)
          (Real.exp (n*t) • filterEval (gradientFilter A B β t) f (k+n)))) +
      4*cert.γplus * starQuadratic 1 (f k) (filterEval (gradientFilter A B β t) f k) +
      4*cert.γminus * starQuadratic (-1) (f k) (filterEval (gradientFilter A B β t) f k) := by
  simp only [certificateKernel, kernelEval_append, kernelEval_scale, kernelEval_star,
    filterEval_unit, kernelEval_flatMap, Finset.sum_map_toList]
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  simp [kernelEval_lag]

/-- Article: Fourier characters use radian frequencies for the period 2π. -/
theorem character_coe (k : ℤ) (ω : ℝ) :
    character k (ω : FrequencyCircle) = Complex.exp ((k : ℂ) * (ω : ℂ) * Complex.I) := by
  rw [character, fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- Article: a nonnegative character frequency is a unit wave power. -/
theorem character_nat_eq_wave (n : ℕ) (ω : ℝ) :
    character n (ω : FrequencyCircle) = Waves.z 0 ω ^ n := by
  rw [character_coe, Waves.z_pow]
  congr 1
  simp
  ring

/-- Article: discounting a geometric wave leaves exactly its unit-frequency wave. -/
theorem exp_mul_unit_wave (t ω : ℝ) (n : ℕ) :
    (Real.exp (n*t) : ℂ) * Waves.z 0 ω ^ n = Waves.z t ω ^ n := by
  rw [Waves.z_pow, Waves.z_pow, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Article: every finite filter multiplies a Fourier character by its value at the origin. -/
theorem filterEval_character (L : LinearFilter) (θ : FrequencyCircle) (k : ℤ) :
    filterEval L (fun j => character j θ) k =
      character k θ * filterEval L (fun j => character j θ) 0 := by
  induction L with
  | nil => simp [filterEval]
  | cons p L ih =>
    change p.1 • character (k+p.2) θ + filterEval L (fun j => character j θ) k =
      character k θ * (p.1 • character (0+p.2) θ + filterEval L (fun j => character j θ) 0)
    rw [ih]
    simp only [character, fourier_add, zero_add, Complex.real_smul]
    ring

/-- Article: the recurrence gradient filter has exactly the genuine heavy-ball multiplier. -/
theorem filterEval_gradient_character_zero (A B β t ω : ℝ) (hB : B ≠ 0) :
    filterEval (gradientFilter A B β t) (fun j => character j (ω : FrequencyCircle)) 0 =
      Waves.multiplier A B β t ω := by
  rw [filterEval_gradient]
  simp only [zero_add, zero_sub, character, fourier_zero, Complex.real_smul, mul_one]
  have h1 : fourier (1 : ℤ) (ω : FrequencyCircle) = Waves.z 0 ω := by
    simpa using character_nat_eq_wave 1 ω
  have hneg : fourier (-1 : ℤ) (ω : FrequencyCircle) = (Waves.z 0 ω)⁻¹ := by
    have hn : Complex.normSq (Waves.z 0 ω) = 1 := by
      simpa using Waves.normSq_z_pow 0 ω 1
    rw [fourier_neg, h1, Complex.inv_def, hn]
    simp
  rw [h1, hneg]
  have hz := exp_mul_unit_wave t ω 1
  simp only [pow_one, Nat.cast_one, one_mul] at hz
  unfold Waves.multiplier
  rw [← hz]
  push_cast
  rw [Complex.exp_neg]
  field_simp [hB, Waves.z_ne_zero 0 ω, Complex.exp_ne_zero (t : ℂ)]
  ring

/-- Article: the original signed wave-pair slack, with its actual function-value term.
Proof: specialize the already proved planar interpolation identity at the zeroth position. -/
theorem pairQuadratic_wave_slack (M : ℂ) (t ω δ : ℝ) (n : ℕ) :
    pairQuadratic δ 1 (Waves.z t ω ^ n) M (M * Waves.z t ω ^ n) +
      δ * (M.re / 2 * Real.exp (2*n*t) - M.re / 2) =
      (1/2 : ℝ) * Real.exp (n*t) *
        ((1 - Complex.normSq M) * (Real.cosh (n*t) - Real.cos (n*ω)) -
          δ * (2*M.im*Real.sin (n*ω))) := by
  have h := Waves.datum_slack M 0 t ω δ 0 n
  rw [pair_slack_eq] at h
  simp only [Waves.position, Waves.gradient, Waves.value, pow_zero, mul_one,
    Nat.cast_zero, mul_zero, zero_add, Complex.normSq_one,
    zero_mul, add_zero, Waves.normSq_z_pow] at h
  convert h using 1
  ring

/-- Article: the original signed minimizer wave slack, with its actual value term. -/
theorem starQuadratic_wave_slack (M : ℂ) (δ : ℝ) :
    starQuadratic δ 1 M + δ * (M.re/2) = (1/4 : ℝ) * (1 - Complex.normSq M) := by
  simp only [starQuadratic, norm_one, one_pow, Complex.sq_norm, Complex.inner,
    one_mul, Complex.conj_re]
  ring

/-- Article: Q on a unit-frequency wave is precisely Φ after exact value cancellation.
Use: the complete symbol is identified before recurrence-filter substitution. -/
theorem certificateQuadratic_unit_wave {m : C(Frequency, ℂ)} {t : ℝ}
    (cert : StrictCertificate m t) (c : Frequency) :
    certificateQuadratic cert
      (fun n => Waves.z 0 (Real.arccos c) ^ n)
      (fun n => m c * Waves.z 0 (Real.arccos c) ^ n) 0 =
      symbol m t cert.lags cert.α cert.β cert.γplus cert.γminus c := by
  have hsplit := certificateSlack_eq cert
    (fun n => Waves.z 0 (Real.arccos c) ^ n)
    (fun n => m c * Waves.z 0 (Real.arccos c) ^ n) (fun _ => (m c).re/2) 0
  rw [certificateValue_const, add_zero] at hsplit
  rw [← hsplit]
  unfold certificateSlack symbol
  simp only [Nat.zero_add, pow_zero, mul_one, Complex.real_smul]
  have hlag (n : ℕ) :
      (Real.exp (n*t) : ℂ) * Waves.z 0 (Real.arccos c) ^ n =
        Waves.z t (Real.arccos c) ^ n := exp_mul_unit_wave _ _ _
  have hgrad (n : ℕ) :
      (Real.exp (n*t) : ℂ) * (m c * Waves.z 0 (Real.arccos c) ^ n) =
        m c * Waves.z t (Real.arccos c) ^ n := by rw [← mul_assoc, mul_comm _ (m c), mul_assoc, hlag]
  simp_rw [hlag, hgrad]
  have hpair (n : ℕ) (δ : ℝ) := pairQuadratic_wave_slack (m c) t (Real.arccos c) δ n
  have h1 (n : ℕ) :
      pairQuadratic 1 1 (Waves.z t (Real.arccos c) ^ n) (m c)
          (m c * Waves.z t (Real.arccos c) ^ n) +
        (Real.exp (2*n*t) * ((m c).re/2) - (m c).re/2) =
      (1/2 : ℝ) * Real.exp (n*t) * (a m t n c - b m n c) := by
    dsimp only [Duality.a, Duality.b, Duality.g]
    convert hpair n 1 using 1 <;> ring
  have hneg (n : ℕ) :
      pairQuadratic (-1) 1 (Waves.z t (Real.arccos c) ^ n) (m c)
          (m c * Waves.z t (Real.arccos c) ^ n) -
        (Real.exp (2*n*t) * ((m c).re/2) - (m c).re/2) =
      (1/2 : ℝ) * Real.exp (n*t) * (a m t n c + b m n c) := by
    dsimp only [Duality.a, Duality.b, Duality.g]
    convert hpair n (-1) using 1 <;> ring
  simp_rw [h1, hneg]
  have hcancel (n : ℕ) : Real.exp (-(n*t)) * Real.exp (n*t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsum : (∑ n ∈ cert.lags, 2 * Real.exp (-(n*t)) *
      (cert.α n * ((1/2 : ℝ) * Real.exp (n*t) * (a m t n c - b m n c)) +
        cert.β n * ((1/2 : ℝ) * Real.exp (n*t) * (a m t n c + b m n c)))) =
      ∑ n ∈ cert.lags, (cert.α n * (a m t n c - b m n c) +
        cert.β n * (a m t n c + b m n c)) := by
    apply Finset.sum_congr rfl
    intro n _
    calc
      _ = (Real.exp (-(n*t)) * Real.exp (n*t)) *
        (cert.α n * (a m t n c - b m n c) + cert.β n * (a m t n c + b m n c)) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [hsum]
  have hsp := starQuadratic_wave_slack (m c) 1
  have hsm := starQuadratic_wave_slack (m c) (-1)
  dsimp only [Duality.g]
  simp only [one_mul] at hsp
  simp only [neg_one_mul, ← sub_eq_add_neg] at hsm
  rw [hsp, hsm]
  ring

/-- Article: exact identification of the actual recurrence-filtered kernel symbol with Φ.
Proof: evaluate the kernel on one unit character, eliminate its gradient through
the genuine multiplier, and invoke the exact signed wave-slack computation. -/
theorem kernelSymbol_certificate (A B β t : ℝ) (hB : B ≠ 0)
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) (c : Frequency) :
    kernelSymbol (certificateKernel A B β t cert) ((Real.arccos c : ℝ) : FrequencyCircle) =
      symbol (Waves.multiplierMap A B β t) t cert.lags cert.α cert.β
        cert.γplus cert.γminus c := by
  let ω : ℝ := Real.arccos c
  let M : ℂ := Waves.multiplier A B β t ω
  have hgrad (k : ℤ) : filterEval (gradientFilter A B β t)
      (fun j => character j (ω : FrequencyCircle)) k = M * character k (ω : FrequencyCircle) := by
    rw [filterEval_character, filterEval_gradient_character_zero A B β t ω hB]
    exact mul_comm _ _
  have hzero : character 0 (ω : FrequencyCircle) = 1 := by simp [character]
  have hchar (n : ℕ) : character n (ω : FrequencyCircle) = Waves.z 0 ω ^ n :=
    character_nat_eq_wave n ω
  dsimp only [ω] at hgrad hzero hchar
  rw [kernelSymbol_eq_eval, kernelEval_certificate]
  simp_rw [hgrad]
  simp only [zero_add, hzero, mul_one]
  simp_rw [hchar]
  have h := certificateQuadratic_unit_wave cert c
  unfold certificateQuadratic at h
  simp only [Nat.zero_add, pow_zero, mul_one] at h
  exact h

/-- Article: a strict certificate gives a strictly negative complete quadratic symbol
on the entire Fourier circle. Proof: the exact symbol identity on [0,π] and evenness. -/
theorem certificateKernel_symbol_le (A B β t : ℝ) (hB : B ≠ 0)
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) (θ : FrequencyCircle) :
    kernelSymbol (certificateKernel A B β t cert) θ ≤ -cert.ε := by
  apply kernelSymbol_le_of_halfCircle _ cert.ε
  intro ω hω0 hωπ
  let c : Frequency := ⟨Real.cos ω, Real.neg_one_le_cos ω, Real.cos_le_one ω⟩
  have hc : Real.arccos c = ω := Real.arccos_cos hω0 hωπ
  rw [← hc, kernelSymbol_certificate A B β t hB cert c]
  exact cert.strict c

end polyak.Energy
