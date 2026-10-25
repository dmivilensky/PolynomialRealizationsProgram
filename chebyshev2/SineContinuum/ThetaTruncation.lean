import chebyshev2.SineContinuum.ThetaSeries

/-!
Article: chebyshev2, Proposition 10.
Uniform denominators: the omitted numerator retains the actual nome.
Use: `chebyshev2.SineContinuum.theta_remainder_bounds` feeds
`chebyshev2.SineContinuum.energy_integrand_error` (The integrable two-exponential error majorant
of Lemma 7).
Proof chain: `chebyshev2.SineContinuum.energyFiniteSum_error` — chebyshev2, Proposition 10;
Exact sine-energy integral, finite sums and truncation/convergence bounds.
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency true

/--
The two finite series of Lemma 7, with exactly its indexing.

Use: `chebyshev2.SineContinuum.sigma₁_remainder` rewrites with this definition to establish
exact identity `sigma₁ q-sigma₁Partial K q = ∑' j : ℕ, q^((j+K+1)*(j+K+2))`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def sigma₁Partial (K : ℕ) (q : ℝ) : ℝ := ∑ j ∈ Finset.range (K+1), q^(j*(j+1))
/--
Defines `sigma₂Partial` of type `ℝ` by `1+2*∑ j ∈ Finset.range K, (-1:ℝ)^(j+1)*q^((j+1)^2)`.

Use: `chebyshev2.SineContinuum.sigma₂_remainder` uses this definition to establish exact
identity `sigma₂ q-sigma₂Partial K q = 2*∑' j : ℕ, (-1:ℝ)^(j+K+1)*q^((j+K+1)^2)`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def sigma₂Partial (K : ℕ) (q : ℝ) : ℝ :=
  1+2*∑ j ∈ Finset.range K, (-1:ℝ)^(j+1)*q^((j+1)^2)

/--
Summability of the displayed sequence: `Summable (fun j : ℕ => q^a*(q^d)^j) ∧ (∑' j : ℕ,
q^a*(q^d)^j) = q^a/(1-q^d)`.

Use: `chebyshev2.SineContinuum.sigma₁_remainder_bound` uses this summability result to
establish the stated quantitative bound `|sigma₁ q-sigma₁Partial K q| ≤
q^((K+1)*(K+2))/(1-q^(2*(K+2)))`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem geometric_majorant {q : ℝ} (hq : 0 ≤ q) (hl : q < 1)
    (a d : ℕ) (hd : 0 < d) :
    Summable (fun j : ℕ => q^a*(q^d)^j) ∧
      (∑' j : ℕ, q^a*(q^d)^j) = q^a/(1-q^d) := by
  have hr : q^d < 1 := pow_lt_one₀ hq hl (by omega)
  exact ⟨(summable_geometric_of_lt_one (pow_nonneg hq d) hr).mul_left _,by
    rw [tsum_mul_left,tsum_geometric_of_lt_one (pow_nonneg hq d) hr]
    ring⟩

/--
The exact omitted series, before estimating it.

Exact identity `sigma₁ q-sigma₁Partial K q = ∑' j : ℕ, q^((j+K+1)*(j+K+2))`.

Use: `chebyshev2.SineContinuum.sigma₁_remainder_bound` rewrites with this identity to
establish the stated quantitative bound `|sigma₁ q-sigma₁Partial K q| ≤
q^((K+1)*(K+2))/(1-q^(2*(K+2)))`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sigma₁_remainder {q : ℝ} (hq : 0 ≤ q) (hl : q < 1) (K : ℕ) :
    sigma₁ q-sigma₁Partial K q = ∑' j : ℕ, q^((j+K+1)*(j+K+2)) := by
  have h := (sigma₁_summable hq hl).sum_add_tsum_nat_add (K+1)
  simp only [sigma₁,sigma₁Partial] at ⊢
  simp only [show (fun j : ℕ => q^((j+(K+1))*((j+(K+1))+1))) =
    (fun j : ℕ => q^((j+K+1)*(j+K+2))) by funext j; congr 1] at h
  linarith

/--
The geometric tail bound printed in Lemma 7 for the first series.

The stated quantitative bound `|sigma₁ q-sigma₁Partial K q| ≤ q^((K+1)*(K+2))/(1-q^(2*(K+2)))`.

Use: `chebyshev2.SineContinuum.theta_remainder_bounds` uses this bound to establish the
stated quantitative bound `|sigma₁ q-sigma₁Partial K q| ≤ q^((K+1)*(K+2))/(1-q₀^(2*(K+2))) ∧
|sigma₂ q-sigma₂Partial K q| ≤ 2*q^((K+1)^2)/(1-q₀^(2*K+3))`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sigma₁_remainder`,
`_private.chebyshev2.SineContinuum.ThetaTruncation.0.chebyshev2.SineContinuum.geometric_majorant`,
`chebyshev2.SineContinuum.sigma₁_summable` with the arguments shown in the proof.
-/
theorem sigma₁_remainder_bound {q : ℝ} (hq : 0 ≤ q) (hl : q < 1) (K : ℕ) :
    |sigma₁ q-sigma₁Partial K q| ≤ q^((K+1)*(K+2))/(1-q^(2*(K+2))) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.sigma₁_remainder`,
  -- `_private.chebyshev2.SineContinuum.ThetaTruncation.0.chebyshev2.SineContinuum.geometric_majorant`,
  -- `chebyshev2.SineContinuum.sigma₁_summable` with the arguments shown in the proof.
  rw [sigma₁_remainder hq hl K,abs_of_nonneg (tsum_nonneg (fun j => pow_nonneg hq _))]
  obtain ⟨hs,he⟩ := geometric_majorant hq hl ((K+1)*(K+2)) (2*(K+2)) (by omega)
  rw [← he]
  apply ((summable_nat_add_iff (K+1)).mpr (sigma₁_summable hq hl)).tsum_le_tsum _ hs
  intro j
  rw [← pow_mul,← pow_add]
  exact pow_le_pow_of_le_one hq hl.le (by nlinarith [Nat.le_mul_self j] :
    (K+1)*(K+2)+(2*(K+2))*j ≤ (j+(K+1))*(j+(K+1)+1))

/--
The exact signed remainder of the second series.

Exact identity `sigma₂ q-sigma₂Partial K q = 2*∑' j : ℕ, (-1:ℝ)^(j+K+1)*q^((j+K+1)^2)`.

Use: `chebyshev2.SineContinuum.sigma₂_remainder_bound` rewrites with this identity to
establish the stated quantitative bound `|sigma₂ q-sigma₂Partial K q| ≤
2*q^((K+1)^2)/(1-q^(2*K+3))`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sigma₂_summable` with the
arguments shown in the proof.
-/
theorem sigma₂_remainder {q : ℝ} (hq : 0 ≤ q) (hl : q < 1) (K : ℕ) :
    sigma₂ q-sigma₂Partial K q =
      2*∑' j : ℕ, (-1:ℝ)^(j+K+1)*q^((j+K+1)^2) := by
  have h := (sigma₂_summable hq hl).sum_add_tsum_nat_add K
  unfold sigma₂ sigma₂Partial
  simp only [Nat.add_assoc] at h ⊢
  linarith

/--
The factor 2 and exponent (K+1)^2 of the printed second tail.

The stated quantitative bound `|sigma₂ q-sigma₂Partial K q| ≤ 2*q^((K+1)^2)/(1-q^(2*K+3))`.

Use: `chebyshev2.SineContinuum.theta_remainder_bounds` uses this bound to establish the
stated quantitative bound `|sigma₁ q-sigma₁Partial K q| ≤ q^((K+1)*(K+2))/(1-q₀^(2*(K+2))) ∧
|sigma₂ q-sigma₂Partial K q| ≤ 2*q^((K+1)^2)/(1-q₀^(2*K+3))`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates
`_private.chebyshev2.SineContinuum.ThetaTruncation.0.chebyshev2.SineContinuum.geometric_majorant`,
`chebyshev2.SineContinuum.sigma₂_absolute`, `chebyshev2.SineContinuum.sigma₂_remainder`
with the arguments shown in the proof.
-/
theorem sigma₂_remainder_bound {q : ℝ} (hq : 0 ≤ q) (hl : q < 1) (K : ℕ) :
    |sigma₂ q-sigma₂Partial K q| ≤ 2*q^((K+1)^2)/(1-q^(2*K+3)) := by
  -- Apply
  -- `_private.chebyshev2.SineContinuum.ThetaTruncation.0.chebyshev2.SineContinuum.geometric_majorant`,
  -- `chebyshev2.SineContinuum.sigma₂_absolute`,
  -- `chebyshev2.SineContinuum.sigma₂_remainder` to the displayed hypotheses, then match
  -- the resulting expression to the goal.
  obtain ⟨hs,he⟩ := geometric_majorant hq hl ((K+1)^2) (2*K+3) (by omega)
  -- Prove the summability ha needed for the later infinite-sum manipulations.
  have ha : Summable (fun j : ℕ => |(-1:ℝ)^(j+K+1)*q^((j+K+1)^2)|) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff K).mpr (sigma₂_absolute hq hl)
  have hb : (∑' j : ℕ, |(-1:ℝ)^(j+K+1)*q^((j+K+1)^2)|) ≤
      q^((K+1)^2)/(1-q^(2*K+3)) := by
    rw [← he]
    apply ha.tsum_le_tsum _ hs
    intro j
    simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_nonneg (pow_nonneg hq _)]
    rw [← pow_mul,← pow_add]
    exact pow_le_pow_of_le_one hq hl.le (by
      nlinarith [Nat.le_mul_self j] : (K+1)^2+(2*K+3)*j ≤ (j+K+1)^2)
  have hn := norm_tsum_le_tsum_norm
    (f := fun j : ℕ => (-1:ℝ)^(j+K+1)*q^((j+K+1)^2))
    (by simpa only [Real.norm_eq_abs] using ha)
  simp only [Real.norm_eq_abs] at hn
  rw [sigma₂_remainder hq hl K,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*(q^((K+1)^2)/(1-q^(2*K+3))) :=
      mul_le_mul_of_nonneg_left (hn.trans hb) (by norm_num)
    _ = _ := by ring

/--
Uniform denominators: the omitted numerator retains the actual nome.

The stated quantitative bound `|sigma₁ q-sigma₁Partial K q| ≤ q^((K+1)*(K+2))/(1-q₀^(2*(K+2)))
∧ |sigma₂ q-sigma₂Partial K q| ≤ 2*q^((K+1)^2)/(1-q₀^(2*K+3))`.

Use:
`_private.chebyshev2.SineContinuum.EnergyRemainder.0.chebyshev2.SineContinuum.energy_series_remainders`
uses this bound to establish the bound stated in that declaration.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sigma₁_remainder_bound`,
`chebyshev2.SineContinuum.sigma₂_remainder_bound` with the arguments shown in the proof.
-/
theorem theta_remainder_bounds {q q₀ : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q₀) (h₀ : q₀ < 1)
    (K : ℕ) :
    |sigma₁ q-sigma₁Partial K q| ≤ q^((K+1)*(K+2))/(1-q₀^(2*(K+2))) ∧
    |sigma₂ q-sigma₂Partial K q| ≤ 2*q^((K+1)^2)/(1-q₀^(2*K+3)) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.sigma₁_remainder_bound`,
  -- `chebyshev2.SineContinuum.sigma₂_remainder_bound` with the arguments shown in the
  -- proof.
  have hl := hqq.trans_lt h₀
  have hqp := hq.trans hqq
  constructor
  · apply (sigma₁_remainder_bound hq hl K).trans
    exact div_le_div_of_nonneg_left (pow_nonneg hq _)
      (sub_pos.mpr (pow_lt_one₀ hqp h₀ (by omega)))
      (sub_le_sub_left (pow_le_pow_left₀ hq hqq _) 1)
  · apply (sigma₂_remainder_bound hq hl K).trans
    exact div_le_div_of_nonneg_left (by positivity)
      (sub_pos.mpr (pow_lt_one₀ hqp h₀ (by omega)))
      (sub_le_sub_left (pow_le_pow_left₀ hq hqq _) 1)

end
end chebyshev2.SineContinuum
