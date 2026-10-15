import «2610.05164v2».SineContinuum.ThetaTruncation

/-!
Article: 2610.05164v2, Proposition 10.
The power-product estimate used in Lemma 7, independent of theta identities.
Use: `«2610.05164v2».SineContinuum.sixth_product_difference` feeds
`«2610.05164v2».SineContinuum.energy_integrand_error` (The integrable two-exponential error majorant
of Lemma 7).
Proof chain: `«2610.05164v2».SineContinuum.energyFiniteSum_error` — 2610.05164v2, Proposition 10;
Exact sine-energy integral, finite sums and truncation/convergence bounds.
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency true

/--
A single summable majorant controls the full and every truncated first series.

The stated quantitative bound `0 ≤ sigma₁Partial K q ∧ sigma₁Partial K q ≤ 1/(1-q₀^2) ∧ 0 ≤
sigma₁ q ∧ sigma₁ q ≤ 1/(1-q₀^2)`.

Use: `«2610.05164v2».SineContinuum.energy_series_majorants` uses this bound to establish the
stated quantitative bound `|sigma₁ (exp (-π*t))| ≤ energyM₁ ∧ |sigma₁Partial K (exp (-π*t))| ≤
energyM₁ ∧ |sigma₂ (exp (-π*t))| ≤ energyM₂ ∧ |sigma₂Partial K (exp (-π*t))| ≤ energyM₂`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₁_summable` with the
arguments shown in the proof.
-/
theorem sigma₁_majorants {q q₀ : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q₀) (h₀ : q₀ < 1) (K : ℕ) :
    0 ≤ sigma₁Partial K q ∧ sigma₁Partial K q ≤ 1/(1-q₀^2) ∧
      0 ≤ sigma₁ q ∧ sigma₁ q ≤ 1/(1-q₀^2) := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₁_summable` with the
  -- arguments shown in the proof.
  have hqp := hq.trans hqq
  have hr : q₀^2 < 1 := pow_lt_one₀ hqp h₀ (by norm_num)
  have hs := summable_geometric_of_lt_one (sq_nonneg q₀) hr
  have hmajor (j : ℕ) : q^(j*(j+1)) ≤ (q₀^2)^j := by
    calc
      _ ≤ q₀^(j*(j+1)) := pow_le_pow_left₀ hq hqq _
      _ ≤ q₀^(2*j) := pow_le_pow_of_le_one hqp h₀.le (by nlinarith [Nat.le_mul_self j])
      _ = _ := pow_mul _ _ _
  have hfull := (sigma₁_summable hq (hqq.trans_lt h₀)).tsum_le_tsum hmajor hs
  have hfinite : sigma₁Partial K q ≤ ∑' j : ℕ, (q₀^2)^j := by
    apply (Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (K+1)) => hmajor j)).trans
    exact hs.sum_le_tsum _ (fun j _ => pow_nonneg (sq_nonneg q₀) j)
  rw [tsum_geometric_of_lt_one (sq_nonneg q₀) hr] at hfull hfinite
  exact ⟨Finset.sum_nonneg (fun j _ => pow_nonneg hq _),by simpa [one_div] using hfinite,
    tsum_nonneg (fun j => pow_nonneg hq _),by simpa [sigma₁,one_div] using hfull⟩

/--
The sharper second-series bound uses j^2 >= 3j-2, including every partial sum.

The stated quantitative bound `|sigma₂Partial K q| ≤ 1+2*q₀/(1-q₀^3) ∧ |sigma₂ q| ≤
1+2*q₀/(1-q₀^3)`.

Use: `«2610.05164v2».SineContinuum.energy_series_majorants` uses this bound to establish the
stated quantitative bound `|sigma₁ (exp (-π*t))| ≤ energyM₁ ∧ |sigma₁Partial K (exp (-π*t))| ≤
energyM₁ ∧ |sigma₂ (exp (-π*t))| ≤ energyM₂ ∧ |sigma₂Partial K (exp (-π*t))| ≤ energyM₂`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₂_absolute` with the
arguments shown in the proof.
-/
theorem sigma₂_majorants {q q₀ : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q₀) (h₀ : q₀ < 1) (K : ℕ) :
    |sigma₂Partial K q| ≤ 1+2*q₀/(1-q₀^3) ∧ |sigma₂ q| ≤ 1+2*q₀/(1-q₀^3) := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₂_absolute` with the
  -- arguments shown in the proof.
  have hqp := hq.trans hqq
  have hr : q₀^3 < 1 := pow_lt_one₀ hqp h₀ (by norm_num)
  have hs := (summable_geometric_of_lt_one (pow_nonneg hqp 3) hr).mul_left q₀
  have hmajor (j : ℕ) : |(-1:ℝ)^(j+1)*q^((j+1)^2)| ≤ q₀*(q₀^3)^j := by
    simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_nonneg (pow_nonneg hq _)]
    calc
      _ ≤ q₀^((j+1)^2) := pow_le_pow_left₀ hq hqq _
      _ ≤ q₀^(1+3*j) := pow_le_pow_of_le_one hqp h₀.le (by nlinarith [Nat.le_mul_self j])
      _ = _ := by rw [pow_add,pow_one,pow_mul]
  have he : (∑' j : ℕ, q₀*(q₀^3)^j) = q₀/(1-q₀^3) := by
    rw [tsum_mul_left,tsum_geometric_of_lt_one (pow_nonneg hqp 3) hr]
    ring
  have hfull := (sigma₂_absolute hq (hqq.trans_lt h₀)).tsum_le_tsum hmajor hs
  have hfinite : (∑ j ∈ Finset.range K, |(-1:ℝ)^(j+1)*q^((j+1)^2)|) ≤ q₀/(1-q₀^3) := by
    rw [← he]
    apply (Finset.sum_le_sum (fun j (_ : j ∈ Finset.range K) => hmajor j)).trans
    exact hs.sum_le_tsum _ (fun j _ => mul_nonneg hqp (pow_nonneg (pow_nonneg hqp _) _))
  rw [he] at hfull
  have hn := norm_tsum_le_tsum_norm
    (f := fun j : ℕ => (-1:ℝ)^(j+1)*q^((j+1)^2))
    (by simpa only [Real.norm_eq_abs] using sigma₂_absolute hq (hqq.trans_lt h₀))
  simp only [Real.norm_eq_abs] at hn
  constructor
  · unfold sigma₂Partial
    calc
      _ ≤ |(1:ℝ)| +|2*(∑ j ∈ Finset.range K, (-1:ℝ)^(j+1)*q^((j+1)^2))| := abs_add_le _ _
      _ = 1+2*|∑ j ∈ Finset.range K, (-1:ℝ)^(j+1)*q^((j+1)^2)| := by norm_num [abs_mul]
      _ ≤ 1+2*(q₀/(1-q₀^3)) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans hfinite
      _ = _ := by ring
  · unfold sigma₂
    calc
      _ ≤ |(1:ℝ)| +|2*(∑' j : ℕ, (-1:ℝ)^(j+1)*q^((j+1)^2))| := abs_add_le _ _
      _ = 1+2*|∑' j : ℕ, (-1:ℝ)^(j+1)*q^((j+1)^2)| := by norm_num [abs_mul]
      _ ≤ 1+2*(q₀/(1-q₀^3)) := by gcongr; exact hn.trans hfull
      _ = _ := by ring

/--
The power-product estimate used in Lemma 7, independent of theta identities.

The stated quantitative bound `|X^6*Y^6-x^6*y^6| ≤ 6*A^5*B^6*|X-x| +6*A^6*B^5*|Y-y|`.

Use: `«2610.05164v2».SineContinuum.energy_integrand_error` uses this bound to establish the
stated quantitative bound `|thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤
energyErrorMajorant K t`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem sixth_product_difference {X x Y y A B : ℝ}
    (hX : |X| ≤ A) (hx : |x| ≤ A) (hY : |Y| ≤ B) (hy : |y| ≤ B) :
    |X^6*Y^6-x^6*y^6| ≤ 6*A^5*B^6*|X-x| +6*A^6*B^5*|Y-y| := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hA := (abs_nonneg X).trans hX
  have hB := (abs_nonneg Y).trans hY
  have hdX : |X^6-x^6| ≤ 6*A^5*|X-x| := by
    have h := abs_pow_sub_pow_le (a := X) (b := x) (n := 6)
    norm_num only [Nat.cast_ofNat,Nat.reduceSub] at h
    apply h.trans
    calc
      _ ≤ |X-x| *6*A^5 := by gcongr; exact max_le hX hx
      _ = _ := by ring
  have hdY : |Y^6-y^6| ≤ 6*B^5*|Y-y| := by
    have h := abs_pow_sub_pow_le (a := Y) (b := y) (n := 6)
    norm_num only [Nat.cast_ofNat,Nat.reduceSub] at h
    apply h.trans
    calc
      _ ≤ |Y-y| *6*B^5 := by gcongr; exact max_le hY hy
      _ = _ := by ring
  calc
    _ = |(X^6-x^6)*Y^6+x^6*(Y^6-y^6)| := by congr 1; ring
    _ ≤ |(X^6-x^6)*Y^6| +|x^6*(Y^6-y^6)| := abs_add_le _ _
    _ = |X^6-x^6| *|Y| ^6+|x| ^6*|Y^6-y^6| := by rw [abs_mul,abs_mul,abs_pow,abs_pow]
    _ ≤ (6*A^5*|X-x|)*B^6+A^6*(6*B^5*|Y-y|) := by gcongr
    _ = _ := by ring

end
end «2610.05164v2».SineContinuum
