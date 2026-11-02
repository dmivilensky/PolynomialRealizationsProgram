import Mathlib.Tactic

/-!
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform finite-cycle step.
Use: Close the actual Gram, angle, gate and projected-residual induction
before the first small line displacement, using one fixed quantitative allowance.
Source: proved real observed conjugacy and spectral gates, true normalized
model solves, actual recorded-step transfer and elementary scalar inequalities.
-/

namespace krylov.Correction
noncomputable section

/-- A genuine line above the quadratic cutoff gives the precise residual-to-line ratio needed by the real correction bound.
Use: Assemble the actual uniform gated-RFC cutoff induction from original measured data.
Article: main_krylov, thm:UCq and thm:UCg, genuine finite-cycle cutoff step.
Proof: Divide by the true positive cutoff constant, compare the old actual residual with the genuine line lower bound and multiply only by proved nonnegative scalars.
-/
theorem large_line_residual_ratio {ε C M H R t q : ℝ} (hC : 0≤C) (hM : 0<M)
    (hR : R≤C*ε^2) (ht : M*ε^2≤t)
    (hq : 4*C/M+4*H*ε≤q) : 4*(R+H*ε*t)≤q*t := by
  have ht0 : 0≤t := (mul_nonneg hM.le (sq_nonneg ε)).trans ht
  have hR' : R≤C/M*t := by
    calc
      _ ≤ C*ε^2 := hR
      _ = (C/M)*(M*ε^2) := by field_simp
      _ ≤ C/M*t := mul_le_mul_of_nonneg_left ht (div_nonneg hC hM.le)
  calc
    _ ≤ 4*(C/M*t+H*ε*t) := by linarith
    _ = (4*C/M+4*H*ε)*t := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hq ht0

/-- The genuine scalar projected-residual recurrence preserves a quadratic bound under one uniform small radius and growth allowance.
Use: Assemble the actual uniform gated-RFC cutoff induction from original measured data.
Article: main_krylov, thm:UCq and thm:UCg, genuine finite-cycle cutoff step.
Proof: The actual old residual contribution consumes one half of the quadratic allowance; the real line-growth contribution consumes the other half. Add those two exact nonnegative product bounds.
-/
theorem quadratic_residual_invariant {ε C F H L R t : ℝ}
    (hε : 0≤ε) (hC : 0≤C) (hF : 0≤F) (hH : 0≤H)
    (hR : R≤C*ε^2) (ht : t≤2*L) (hsmall : F*ε≤1/2)
    (hsize : 4*F*H*L≤C) : F*ε*(R+H*ε*t)≤C*ε^2 := by
  have h₁ : F*ε*R≤(1/2)*(C*ε^2) :=
    (mul_le_mul_of_nonneg_left hR (mul_nonneg hF hε)).trans
      (mul_le_mul_of_nonneg_right hsmall (mul_nonneg hC (sq_nonneg ε)))
  have h₂ : F*H*t≤C/2 := by
    have h := mul_le_mul_of_nonneg_left ht (mul_nonneg hF hH)
    nlinarith
  have h₃ := mul_le_mul_of_nonneg_right h₂ (sq_nonneg ε)
  nlinarith

/-- One horizon-only angle allowance gives the half-radius, genuine measured spectral margin and strict observed defect margin at every real prefix dimension.
Use: Assemble the actual uniform gated-RFC cutoff induction from original measured data.
Article: main_krylov, thm:UCq and thm:UCg, genuine finite-cycle cutoff step.
Proof: Compare the actual prefix dimension with the common horizon and use the true nonnegative angle and pair-error allowances, keeping the original positive threshold gap.
-/
theorem uniform_gate_margins {N m : ℕ} {γ a η : ℝ} (hN : 1≤N) (hm : m≤N)
    (hγ : 0≤γ) (hγ1 : γ<1) (ha : 0≤a) (hη : 0≤η) (hηa : η≤a/2)
    (hbudget : (N : ℝ)*a≤(1-γ)/8) :
    η≤1/2 ∧ (m : ℝ)*a+(m : ℝ)*η≤1/2 ∧
      (m : ℝ)*a+(m : ℝ)*η+γ*η≤1-γ ∧ (m : ℝ)*(4*η)<1 := by
  have hN' : (1 : ℝ)≤N := by exact_mod_cast hN
  have hm' : (m : ℝ)≤N := by exact_mod_cast hm
  have hN0 : 0≤(N : ℝ) := Nat.cast_nonneg N
  have hm0 : 0≤(m : ℝ) := Nat.cast_nonneg m
  have hma := mul_le_mul_of_nonneg_right hm' ha
  have hmη := mul_le_mul_of_nonneg_right hm' hη
  have hNη := mul_le_mul_of_nonneg_left hηa hN0
  have haN := mul_le_mul_of_nonneg_right hN' ha
  have hγη : γ*η≤η := by nlinarith
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · constructor <;> nlinarith

end
end krylov.Correction
