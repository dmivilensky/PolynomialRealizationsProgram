import «2610.05164v2».SineContinuum.ReferenceIdentification
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Article: 2610.05164v2, Proposition 2.
The literal real series in Proposition 2, equation (10).
Use: `«2610.05164v2».SineContinuum.sigma_bounds` feeds
`«2610.05164v2».SineContinuum.thetaDensity_envelope` (theta Density envelope).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency true

/--
The literal real series in Proposition 2, equation (10).

Use: `«2610.05164v2».SineContinuum.sigma₁_lower` uses this definition to establish the stated
quantitative bound `1 ≤ sigma₁ q`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def sigma₁ (q : ℝ) : ℝ := ∑' j : ℕ, q^(j*(j+1))
/--
Defines `sigma₂` of type `ℝ` by `1+2*∑' j : ℕ, (-1:ℝ)^(j+1)*q^((j+1)^2)`.

Use: `«2610.05164v2».SineContinuum.sigma_bounds` uses this definition to establish the stated
quantitative bound `1 ≤ sigma₁ q ∧ sigma₁ q ≤ 4/3 ∧ 1/3 ≤ sigma₂ q ∧ sigma₂ q ≤ 5/3`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def sigma₂ (q : ℝ) : ℝ := 1+2*∑' j : ℕ, (-1:ℝ)^(j+1)*q^((j+1)^2)

/--
Summability of the displayed sequence: `Summable (fun j : ℕ => q^(j*(j+1)))`.

Use: `«2610.05164v2».SineContinuum.sigma₁_lower` uses this summability result to establish the
stated quantitative bound `1 ≤ sigma₁ q`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem sigma₁_summable {q : ℝ} (hq : 0 ≤ q) (hql : q < 1) :
    Summable (fun j : ℕ => q^(j*(j+1))) := by
  apply (summable_geometric_of_lt_one hq hql).of_nonneg_of_le
  · intro j; exact pow_nonneg hq _
  · intro j
    exact pow_le_pow_of_le_one hq hql.le (by nlinarith : j ≤ j*(j+1))

/--
Summability of the displayed sequence: `Summable (fun j : ℕ => |(-1:ℝ)^(j+1)*q^((j+1)^2)|)`.

Use: `«2610.05164v2».SineContinuum.sigma₂_deviation` uses this summability result to establish
the stated quantitative bound `|sigma₂ q-1| ≤ 2*q/(1-q)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem sigma₂_absolute {q : ℝ} (hq : 0 ≤ q) (hql : q < 1) :
    Summable (fun j : ℕ => |(-1:ℝ)^(j+1)*q^((j+1)^2)|) := by
  apply ((summable_geometric_of_lt_one hq hql).mul_left q).of_nonneg_of_le
  · intro j; exact abs_nonneg _
  · intro j
    simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_nonneg (pow_nonneg hq _)]
    rw [← pow_succ']
    exact pow_le_pow_of_le_one hq hql.le (by nlinarith : j+1 ≤ (j+1)^2)

/--
Summability of the displayed sequence: `Summable (fun j : ℕ => (-1:ℝ)^(j+1)*q^((j+1)^2))`.

Use: `«2610.05164v2».SineContinuum.sigma₂_remainder` uses this summability result to establish
exact identity `sigma₂ q-sigma₂Partial K q = 2*∑' j : ℕ, (-1:ℝ)^(j+K+1)*q^((j+K+1)^2)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₂_absolute` with the
arguments shown in the proof.
-/
theorem sigma₂_summable {q : ℝ} (hq : 0 ≤ q) (hql : q < 1) :
    Summable (fun j : ℕ => (-1:ℝ)^(j+1)*q^((j+1)^2)) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using sigma₂_absolute hq hql

/--
The stated quantitative bound `1 ≤ sigma₁ q`.

Use: `«2610.05164v2».SineContinuum.sigma_bounds` uses this bound to establish the stated
quantitative bound `1 ≤ sigma₁ q ∧ sigma₁ q ≤ 4/3 ∧ 1/3 ≤ sigma₂ q ∧ sigma₂ q ≤ 5/3`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta_envelope`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₁_summable` with the
arguments shown in the proof.
-/
theorem sigma₁_lower {q : ℝ} (hq : 0 ≤ q) (hql : q < 1) : 1 ≤ sigma₁ q := by
  have h := (sigma₁_summable hq hql).le_tsum 0 (fun j _ => pow_nonneg hq (j*(j+1)))
  simpa only [Nat.zero_mul,pow_zero,sigma₁] using h

/--
The stated quantitative bound `sigma₁ q ≤ (1-q)⁻¹`.

Use: `«2610.05164v2».SineContinuum.sigma_bounds` uses this bound to establish the stated
quantitative bound `1 ≤ sigma₁ q ∧ sigma₁ q ≤ 4/3 ∧ 1/3 ≤ sigma₂ q ∧ sigma₂ q ≤ 5/3`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta_envelope`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₁_summable` with the
arguments shown in the proof.
-/
theorem sigma₁_upper {q : ℝ} (hq : 0 ≤ q) (hql : q < 1) : sigma₁ q ≤ (1-q)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hq hql]
  exact (sigma₁_summable hq hql).tsum_le_tsum
    (fun j => pow_le_pow_of_le_one hq hql.le (by nlinarith : j ≤ j*(j+1)))
    (summable_geometric_of_lt_one hq hql)

/--
The stated quantitative bound `|sigma₂ q-1| ≤ 2*q/(1-q)`.

Use: `«2610.05164v2».SineContinuum.sigma_bounds` uses this bound to establish the stated
quantitative bound `1 ≤ sigma₁ q ∧ sigma₁ q ≤ 4/3 ∧ 1/3 ≤ sigma₂ q ∧ sigma₂ q ≤ 5/3`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta_envelope`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₂_absolute` with the
arguments shown in the proof.
-/
theorem sigma₂_deviation {q : ℝ} (hq : 0 ≤ q) (hql : q < 1) :
    |sigma₂ q-1| ≤ 2*q/(1-q) := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₂_absolute` with the
  -- arguments shown in the proof.
  have h : (∑' j : ℕ, |(-1:ℝ)^(j+1)*q^((j+1)^2)|) ≤ q*(1-q)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hq hql,← (summable_geometric_of_lt_one hq hql).tsum_mul_left q]
    apply (sigma₂_absolute hq hql).tsum_le_tsum _ ((summable_geometric_of_lt_one hq hql).mul_left q)
    intro j
    simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_nonneg (pow_nonneg hq _)]
    rw [← pow_succ']
    exact pow_le_pow_of_le_one hq hql.le (by nlinarith : j+1 ≤ (j+1)^2)
  have hn := norm_tsum_le_tsum_norm
    (f := fun j : ℕ => (-1:ℝ)^(j+1)*q^((j+1)^2))
    (by simpa only [Real.norm_eq_abs] using sigma₂_absolute hq hql)
  simp only [Real.norm_eq_abs] at hn
  unfold sigma₂
  rw [add_sub_cancel_left,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*(q*(1-q)⁻¹) := mul_le_mul_of_nonneg_left (hn.trans h) (by norm_num)
    _ = _ := by ring

/--
The stated quantitative bound `1 ≤ sigma₁ q ∧ sigma₁ q ≤ 4/3 ∧ 1/3 ≤ sigma₂ q ∧ sigma₂ q ≤
5/3`.

Use: `«2610.05164v2».SineContinuum.thetaDensity_envelope` uses this bound to establish the
stated quantitative bound `(8/9:ℝ)*(thetaRho x*exp (-π*thetaRho x/2)) ≤ thetaDensity x ∧
thetaDensity x ≤ 40*(thetaRho x*exp (-π*thetaRho x/2))`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta_envelope`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₁_lower`,
`«2610.05164v2».SineContinuum.sigma₁_upper`, `«2610.05164v2».SineContinuum.sigma₂_deviation`
with the arguments shown in the proof.
-/
theorem sigma_bounds {q : ℝ} (hq : 0 ≤ q) (hql : q ≤ 1/4) :
    1 ≤ sigma₁ q ∧ sigma₁ q ≤ 4/3 ∧ 1/3 ≤ sigma₂ q ∧ sigma₂ q ≤ 5/3 := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.sigma₁_lower`,
  -- `«2610.05164v2».SineContinuum.sigma₁_upper`,
  -- `«2610.05164v2».SineContinuum.sigma₂_deviation` with the arguments shown in the proof.
  have hl : q < 1 := by linarith
  have hp : 0 < 1-q := by linarith
  have h₁ := sigma₁_lower hq hl
  have h₂ := sigma₁_upper hq hl
  have h₃ := sigma₂_deviation hq hl
  have hi : (1-q)⁻¹ ≤ 4/3 := by
    rw [← one_div,div_le_iff₀ hp]
    linarith
  have hd : 2*q/(1-q) ≤ 2/3 := by rw [div_le_iff₀ hp]; linarith
  exact ⟨h₁,h₂.trans hi,by linarith [neg_abs_le (sigma₂ q-1)],by linarith [le_abs_self (sigma₂ q-1)]⟩

end
end «2610.05164v2».SineContinuum
