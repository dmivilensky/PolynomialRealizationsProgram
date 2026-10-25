import polyak.Energy.Symbol
import polyak.Growth.HorizonCertificate

/-!
Article: Appendix C, raw finite interpolation combinations before charge cancellation.
Use: affine equality separation may leave a nonzero value charge in the raw
combination. Its exact kernel, value coefficients and source slacks are retained
until the added window price cancels that charge.
-/
noncomputable section
namespace polyak.Energy
open Interpolation Duality Spectral Growth Growth.FiniteHorizon
open scoped BigOperators

structure FiniteCombination (t : ℝ) where
  /-- Article: finite lag support. -/
  lags : Finset ℕ
  /-- Article: only positive lags are interpolation constraints. -/
  positive_lag : ∀ n ∈ lags, 1 ≤ n
  /-- Article: lower lag weights. -/
  α : ℕ → ℝ
  /-- Article: upper lag weights. -/
  β : ℕ → ℝ
  /-- Article: nonnegative lower weights. -/
  α_nonneg : ∀ n ∈ lags, 0 ≤ α n
  /-- Article: nonnegative upper weights. -/
  β_nonneg : ∀ n ∈ lags, 0 ≤ β n
  /-- Article: positive minimizer slack weight. -/
  γplus : ℝ
  /-- Article: negative minimizer slack weight. -/
  γminus : ℝ
  /-- Article: nonnegative minimizer multiplier. -/
  γplus_nonneg : 0 ≤ γplus
  /-- Article: nonnegative minimizer multiplier. -/
  γminus_nonneg : 0 ≤ γminus

def FiniteCombination.charge {t : ℝ} (comb : FiniteCombination t) : ℝ :=
  (∑ n∈comb.lags,(comb.α n-comb.β n)*Real.sinh (n*t))+comb.γplus-comb.γminus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {t : ℝ}

/-- Article: Q after discounting the trajectory. Use: a translation invariant quadratic expression.
The second vector sequence is the discounted gradient, subsequently eliminated by the recurrence. -/
def combinationQuadratic (comb : FiniteCombination t) (f σ : ℕ → E) (k : ℕ) : ℝ :=
  (∑ n ∈ comb.lags, 2 * Real.exp (-(n * t)) *
    (comb.α n * pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n)) +
    comb.β n * pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n)))) +
    4 * comb.γplus * starQuadratic 1 (f k) (σ k) +
    4 * comb.γminus * starQuadratic (-1) (f k) (σ k)

/-- Article: H after discounting the sampled function values. -/
def combinationValue (comb : FiniteCombination t) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ n ∈ comb.lags, 2 * Real.exp (-(n*t)) * (comb.α n - comb.β n) *
    (Real.exp (2*n*t) * h (k+n) - h k)) +
    4 * (comb.γplus - comb.γminus) * h k

/-- Article: discounted signed slacks comprising Z.
Use: an exact expression before separating its quadratic and sampled-value parts. -/
def combinationSlack (comb : FiniteCombination t)
    (f σ : ℕ → E) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ n ∈ comb.lags, 2 * Real.exp (-(n*t)) *
    (comb.α n * (pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n)) +
        (Real.exp (2*n*t) * h (k+n) - h k)) +
     comb.β n * (pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n)) -
        (Real.exp (2*n*t) * h (k+n) - h k)))) +
    4 * comb.γplus * (starQuadratic 1 (f k) (σ k) + h k) +
    4 * comb.γminus * (starQuadratic (-1) (f k) (σ k) - h k)

/-- Article: e^(-2kt) Z = Q + H. Proof: distribute the finite nonnegative combination. -/
theorem combinationSlack_eq (comb : FiniteCombination t)
    (f σ : ℕ → E) (h : ℕ → ℝ) (k : ℕ) :
    combinationSlack comb f σ h k =
      combinationQuadratic comb f σ k + combinationValue comb h k := by
  unfold combinationSlack combinationQuadratic combinationValue
  have hs : (∑ n ∈ comb.lags, 2 * Real.exp (-(n*t)) *
      (comb.α n * (pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
        (σ k) (Real.exp (n*t) • σ (k+n)) +
          (Real.exp (2*n*t) * h (k+n) - h k)) +
       comb.β n * (pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
        (σ k) (Real.exp (n*t) • σ (k+n)) -
          (Real.exp (2*n*t) * h (k+n) - h k)))) =
      (∑ n ∈ comb.lags, 2 * Real.exp (-(n*t)) *
        (comb.α n * pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
          (σ k) (Real.exp (n*t) • σ (k+n)) +
        comb.β n * pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
          (σ k) (Real.exp (n*t) • σ (k+n)))) +
      (∑ n ∈ comb.lags, 2 * Real.exp (-(n*t)) * (comb.α n - comb.β n) *
        (Real.exp (2*n*t) * h (k+n) - h k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hs]
  ring

/-- Article: every discounted interpolation slack is nonnegative, hence so is Z.
Use: a local theorem applicable directly to every actual segment.
Proof: all multipliers, including exponential weights, are nonnegative. -/
theorem combinationSlack_nonneg (comb : FiniteCombination t)
    (f σ : ℕ → E) (h : ℕ → ℝ) (k : ℕ)
    (hp : ∀ n ∈ comb.lags,
      0 ≤ pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
        (σ k) (Real.exp (n*t) • σ (k+n)) +
          (Real.exp (2*n*t) * h (k+n) - h k))
    (hn : ∀ n ∈ comb.lags,
      0 ≤ pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
        (σ k) (Real.exp (n*t) • σ (k+n)) -
          (Real.exp (2*n*t) * h (k+n) - h k))
    (hstarplus : 0 ≤ starQuadratic 1 (f k) (σ k) + h k)
    (hstarminus : 0 ≤ starQuadratic (-1) (f k) (σ k) - h k) :
    0 ≤ combinationSlack comb f σ h k := by
  unfold combinationSlack
  apply add_nonneg
  · apply add_nonneg
    · apply Finset.sum_nonneg
      intro n hn'
      exact mul_nonneg (by positivity) (add_nonneg
        (mul_nonneg (comb.α_nonneg n hn') (hp n hn'))
        (mul_nonneg (comb.β_nonneg n hn') (hn n hn')))
    · exact mul_nonneg (mul_nonneg (by norm_num) comb.γplus_nonneg) hstarplus
  · exact mul_nonneg (mul_nonneg (by norm_num) comb.γminus_nonneg) hstarminus

theorem combinationValue_eq_differences (comb : FiniteCombination t)
    (h : ℕ → ℝ) (k : ℕ) :
    combinationValue comb h k =
      (∑ n ∈ comb.lags, 2 * Real.exp (n*t) * (comb.α n - comb.β n) *
        (h (k+n) - h k)) + 4 * comb.charge * h k := by
  have heach (n : ℕ) :
      2 * Real.exp (-(n*t)) * (comb.α n - comb.β n) *
        (Real.exp (2*n*t) * h (k+n) - h k) =
      2 * Real.exp (n*t) * (comb.α n - comb.β n) * (h (k+n) - h k) +
      4 * h k * ((comb.α n - comb.β n) * Real.sinh (n*t)) := by
    have he := exp_neg_mul_exp_two (n*t)
    have hh : Real.exp (n*t) - Real.exp (-(n*t)) = 2 * Real.sinh (n*t) := by
      rw [Real.sinh_eq]
      ring
    rw [show 2 * (n : ℝ) * t = 2 * ((n : ℝ)*t) by ring]
    calc
      _ = 2 * (comb.α n - comb.β n) *
          ((Real.exp (-(n*t)) * Real.exp (2*(n*t))) * h (k+n) -
            Real.exp (-(n*t)) * h k) := by ring
      _ = _ := by
        rw [he]
        rw [show Real.sinh (n*t) =
          (Real.exp (n*t) - Real.exp (-(n*t))) / 2 by linarith [hh]]
        ring
  unfold combinationValue
  simp_rw [heach]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold FiniteCombination.charge
  ring

theorem combinationValue_const (comb : FiniteCombination t) (h : ℝ) (k : ℕ) :
    combinationValue comb (fun _ => h) k=4*comb.charge*h := by
  rw [combinationValue_eq_differences]
  simp

def combinationKernel (A B β t : ℝ) (comb : FiniteCombination t) : Kernel :=
  (comb.lags.toList.flatMap fun (n : ℕ) => kernelScale (2*Real.exp (-(n*t)))
    (kernelScale (comb.α n) (lagKernel A B β t n 1) ++
      kernelScale (comb.β n) (lagKernel A B β t n (-1)))) ++
  kernelScale (4*comb.γplus) (starKernel 1 unitFilter (gradientFilter A B β t)) ++
  kernelScale (4*comb.γminus) (starKernel (-1) unitFilter (gradientFilter A B β t))

theorem kernelEval_combination (A B β t : ℝ)
    (comb : FiniteCombination t) (f : ℤ → E) (k : ℤ) :
    kernelEval (combinationKernel A B β t comb) f k =
      (∑ n ∈ comb.lags, 2*Real.exp (-(n*t)) *
        (comb.α n * pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
          (filterEval (gradientFilter A B β t) f k)
          (Real.exp (n*t) • filterEval (gradientFilter A B β t) f (k+n)) +
        comb.β n * pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
          (filterEval (gradientFilter A B β t) f k)
          (Real.exp (n*t) • filterEval (gradientFilter A B β t) f (k+n)))) +
      4*comb.γplus * starQuadratic 1 (f k) (filterEval (gradientFilter A B β t) f k) +
      4*comb.γminus * starQuadratic (-1) (f k) (filterEval (gradientFilter A B β t) f k) := by
  simp only [combinationKernel, kernelEval_append, kernelEval_scale, kernelEval_star,
    filterEval_unit, kernelEval_flatMap, Finset.sum_map_toList]
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  simp [kernelEval_lag]

theorem combinationSlack_unit_wave {m : C(Frequency, ℂ)} {t : ℝ}
    (comb : FiniteCombination t) (c : Frequency) :
    combinationSlack comb
      (fun n => Waves.z 0 (Real.arccos c)^n)
      (fun n => m c*Waves.z 0 (Real.arccos c)^n) (fun _ => (m c).re/2) 0 =
      symbol m t comb.lags comb.α comb.β comb.γplus comb.γminus c := by
  unfold combinationSlack symbol
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
  have hsum : (∑ n ∈ comb.lags, 2 * Real.exp (-(n*t)) *
      (comb.α n * ((1/2 : ℝ) * Real.exp (n*t) * (a m t n c - b m n c)) +
        comb.β n * ((1/2 : ℝ) * Real.exp (n*t) * (a m t n c + b m n c)))) =
      ∑ n ∈ comb.lags, (comb.α n * (a m t n c - b m n c) +
        comb.β n * (a m t n c + b m n c)) := by
    apply Finset.sum_congr rfl
    intro n _
    calc
      _ = (Real.exp (-(n*t)) * Real.exp (n*t)) *
        (comb.α n * (a m t n c - b m n c) + comb.β n * (a m t n c + b m n c)) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [hsum]
  have hsp := starQuadratic_wave_slack (m c) 1
  have hsm := starQuadratic_wave_slack (m c) (-1)
  dsimp only [Duality.g]
  simp only [one_mul] at hsp
  simp only [neg_one_mul, ← sub_eq_add_neg] at hsm
  rw [hsp, hsm]
  ring


theorem combinationQuadratic_unit_wave {m : C(Frequency,ℂ)} (comb : FiniteCombination t)
    (c : Frequency) :
    combinationQuadratic comb (fun n => Waves.z 0 (Real.arccos c)^n)
      (fun n => m c*Waves.z 0 (Real.arccos c)^n) 0=
      symbol m t comb.lags comb.α comb.β comb.γplus comb.γminus c-
        2*comb.charge*(m c).re := by
  have hs:=combinationSlack_unit_wave (m:=m) comb c
  rw [combinationSlack_eq,combinationValue_const] at hs
  nlinarith

theorem kernelSymbol_combination (A B β t : ℝ) (hB : B≠0)
    (comb : FiniteCombination t) (c : Frequency) :
    kernelSymbol (combinationKernel A B β t comb) (Real.arccos c : FrequencyCircle)=
      symbol (Waves.multiplierMap A B β t) t comb.lags comb.α comb.β
        comb.γplus comb.γminus c-2*comb.charge*(Waves.multiplierMap A B β t c).re := by
  let ω : ℝ:=Real.arccos c
  let M : ℂ:=Waves.multiplier A B β t ω
  have hgrad (k : ℤ) : filterEval (gradientFilter A B β t)
      (fun j => character j (ω : FrequencyCircle)) k=M*character k (ω : FrequencyCircle) := by
    rw [filterEval_character,filterEval_gradient_character_zero A B β t ω hB]
    exact mul_comm _ _
  have hzero : character 0 (ω : FrequencyCircle)=1:=by simp [character]
  have hchar (n : ℕ) : character n (ω : FrequencyCircle)=Waves.z 0 ω^n:=
    character_nat_eq_wave n ω
  dsimp only [ω] at hgrad hzero hchar
  rw [kernelSymbol_eq_eval,kernelEval_combination]
  simp_rw [hgrad]
  simp only [zero_add,hzero,mul_one]
  simp_rw [hchar]
  have he:=combinationQuadratic_unit_wave (m:=Waves.multiplierMap A B β t) comb c
  unfold combinationQuadratic at he
  simp only [Nat.zero_add,pow_zero,mul_one] at he
  exact he

def combinationShiftCoefficient (comb : FiniteCombination t) (n : ℕ) : ℝ :=
  2*Real.exp (n*t)*(comb.α n-comb.β n)

def combinationValueCoefficient (comb : FiniteCombination t) (n : ℕ) : ℝ :=
  if n=0 then 4*comb.charge-∑ j∈comb.lags,combinationShiftCoefficient comb j
  else if n∈comb.lags then combinationShiftCoefficient comb n else 0

theorem combination_zero_not_mem (comb : FiniteCombination t) : 0∉comb.lags := by
  intro h
  have hh:=comb.positive_lag 0 h
  omega

theorem sum_combinationValueCoefficient (comb : FiniteCombination t) :
    (∑ n∈insert 0 comb.lags,combinationValueCoefficient comb n)=4*comb.charge := by
  rw [Finset.sum_insert (combination_zero_not_mem comb)]
  have hs : (∑ n∈comb.lags,combinationValueCoefficient comb n)=
      ∑ n∈comb.lags,combinationShiftCoefficient comb n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [combinationValueCoefficient,ite_eq_right (show n≠0 by have := comb.positive_lag n hn; omega),ite_eq_left hn]
  rw [hs]
  simp [combinationValueCoefficient]

theorem combinationValue_eq_coefficients (comb : FiniteCombination t) (h : ℕ → ℝ) (k : ℕ) :
    combinationValue comb h k=
      ∑ n∈insert 0 comb.lags,combinationValueCoefficient comb n*h (k+n) := by
  rw [combinationValue_eq_differences,Finset.sum_insert (combination_zero_not_mem comb)]
  have hs : (∑ n∈comb.lags,combinationValueCoefficient comb n*h (k+n))=
      ∑ n∈comb.lags,combinationShiftCoefficient comb n*h (k+n) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [combinationValueCoefficient,ite_eq_right (show n≠0 by have := comb.positive_lag n hn; omega),ite_eq_left hn]
  rw [hs]
  change (∑ n∈comb.lags,combinationShiftCoefficient comb n*(h (k+n)-h k))+
    4*comb.charge*h k=_
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,←Finset.sum_mul]
  simp only [combinationValueCoefficient,Nat.add_zero,ite_true]
  ring

theorem sum_combinationValueCoefficient_Icc {H : ℕ} (comb : FiniteCombination t)
    (hmem : ∀ n∈comb.lags,n≤H) (f : ℕ → ℝ) :
    (∑ n∈Finset.Icc 0 H,combinationValueCoefficient comb n*f n)=
      ∑ n∈insert 0 comb.lags,combinationValueCoefficient comb n*f n := by
  have hsub : insert 0 comb.lags⊆Finset.Icc 0 H := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl|hn
    · exact Finset.mem_Icc.mpr ⟨le_rfl,Nat.zero_le _⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,hmem n hn⟩
  symm
  apply Finset.sum_subset hsub
  intro n _ hn
  have h0 : n≠0:=by intro he; subst n; exact hn (Finset.mem_insert_self _ _)
  have hlag : n∉comb.lags:=by intro he; exact hn (Finset.mem_insert_of_mem he)
  simp only [combinationValueCoefficient,ite_eq_right h0,ite_eq_right hlag,zero_mul]

theorem hRun_combinationSlack_nonneg {A B β : ℝ} {H : ℕ} (r : HRun E A B β H)
    (comb : FiniteCombination t) (hmem : ∀ n∈comb.lags,n≤H) (k : ℕ) (hk : 1≤k) :
    0≤combinationSlack comb (discountedPosition r.x t) (discountedPosition r.σ t)
      (discountedValue (sampleValue r) t) k := by
  apply combinationSlack_nonneg
  · intro n hn
    simpa only [one_mul] using r.discounted_pair_nonneg t 1 (Or.inl rfl) k n hk (hmem n hn)
  · intro n hn
    simpa only [neg_one_mul,←sub_eq_add_neg] using
      r.discounted_pair_nonneg t (-1) (Or.inr rfl) k n hk (hmem n hn)
  · simpa only [one_mul] using r.discounted_star_nonneg t 1 (Or.inl rfl) k hk
  · simpa only [neg_one_mul,←sub_eq_add_neg] using
      r.discounted_star_nonneg t (-1) (Or.inr rfl) k hk

theorem hRun_kernelEval_combination {A B β : ℝ} {H : ℕ} (r : HRun E A B β H)
    (comb : FiniteCombination t) (hB : B≠0) (k : ℕ) (hk : 1≤k) :
    kernelEval (combinationKernel A B β t comb) (discountedInteger r.x t) k=
      combinationQuadratic comb (discountedPosition r.x t) (discountedPosition r.σ t) k := by
  rw [kernelEval_combination]
  have hgrad (n : ℕ) :
      filterEval (gradientFilter A B β t) (discountedInteger r.x t) ((k : ℤ)+n)=
        discountedPosition r.σ t (k+n) := by
    simpa only [Nat.cast_add] using r.filterEval_discountedGradient t hB (k+n) (by omega)
  simp only [r.filterEval_discountedGradient t hB k hk,hgrad,discountedInteger,
    Int.toNat_natCast,Int.toNat_add_nat (by omega : (0 : ℤ)≤k),combinationQuadratic]

end polyak.Energy
