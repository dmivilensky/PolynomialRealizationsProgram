import krylov.Information.PreQuadraticGram

/-!
Article: main_krylov, s4:cor-Q, the original quantitative reflection slack.
Use: derive every stated 1−4nW₀ scalar margin from the genuine sharp
pre-quadratic Gram defect and actual hidden-base displacement bound.
Source: original flag-distortion formula and explicit real order algebra;
zero profiles and the admitted boundary 4nW₀=1 are included.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The actual pre-quadratic defect and primitive total-budget bound imply the original flag condition, strict twin-base domain and both printed reflection slack factors.
Use: the stated source factor 1−4nW₀ suffices for H1 and H2, including zero budgets and the allowed total-budget boundary.
Article: main_krylov, s4:cor-Q, κ_ε²≤2, ϖ≤4W₀ and (1−ϖ)/κ_ε²≥1−4nW₀.
Proof: the sharp actual defect is at most (n−1)W₀, hence at most one
quarter. The exact flag ratio is at most 1+4ε and at most two, so the
true hidden-base displacement is at most 4W₀ and strictly below one.
Multiplying the original slack by 1+4(n−1)W₀ leaves at most 1−4W₀;
its extra quadratic term is nonpositive, giving both stated margins. -/
theorem prequadratic_slack_controls (N : ℕ) (hN : 0<N) (W ε v : ℝ)
    (hW : 0≤W) (hε : 0≤ε) (hεW : ε≤(N : ℝ)*W)
    (hsmall : 4*((N : ℝ)+1)*W≤1)
    (hvb : v≤2*((1+ε)/(1-ε))*W) :
    let κ := (1+ε)/(1-ε)
    let θ := 1-4*((N : ℝ)+1)*W
    ε≤1/4 ∧ 0<κ ∧ κ≤2 ∧ v≤4*W ∧ v<1 ∧ 0≤θ ∧ θ≤(1-v)/κ ∧ θ≤1-v := by
  -- Retain the exact original n−1 Gram factor when converting it into the stated n-dependent slack.
  have hn : (1 : ℝ)≤(N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hNW : 0≤(N : ℝ)*W := mul_nonneg (Nat.cast_nonneg _) hW
  have hquarter : ε≤(1/4 : ℝ) := by nlinarith
  have hden : 0<1-ε := by linarith
  have hκ : 0<(1+ε)/(1-ε) := div_pos (by linarith) hden
  have hklinear : (1+ε)/(1-ε)≤1+4*ε := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hε (by linarith : 0≤1-2*ε)]
  have hk2 : (1+ε)/(1-ε)≤2 := by linarith
  have hv4 : v≤4*W := hvb.trans (by nlinarith)
  have hv1 : v<1 := by nlinarith [mul_le_mul_of_nonneg_right hn hW]
  have hθ : 0≤1-4*((N : ℝ)+1)*W := by linarith
  refine ⟨hquarter,hκ,hk2,hv4,hv1,hθ,?_,?_⟩
  · apply (le_div_iff₀ hκ).mpr
    calc
      _ ≤ (1-4*((N : ℝ)+1)*W)*(1+4*ε) := mul_le_mul_of_nonneg_left hklinear hθ
      _ ≤ (1-4*((N : ℝ)+1)*W)*(1+4*(N : ℝ)*W) := by nlinarith [mul_le_mul_of_nonneg_left hεW (by positivity : 0≤4*(1-4*((N : ℝ)+1)*W))]
      _ ≤ 1-4*W := by nlinarith only [show 0≤16*(N : ℝ)*((N : ℝ)+1)*W^2 by positivity]
      _ ≤ 1-v := by linarith
  · nlinarith

end
end krylov.Information
