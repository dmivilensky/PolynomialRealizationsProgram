import krylov.Strings.DiscreteState
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Article: main_krylov, apC:lem:apriori.
Use: actual discrete string ratios are uniformly bounded under the local
spectral product constraint, and actual logarithmic energy increments have
a sharp summable weight. No continuum or optimizer certificate is assumed.
Source: the exact discrete drift/impulse recurrence and `1+x≤exp x`.
-/

/-!
Article: krylov, Lemma D.20 [apC:lem:apriori].

The physical discrete ratio lies between one and 1+Λ; the weighted logarithmic energy sum has
the telescoping upper bound 1/γ.
The spectral top product constraint used by ratio_bounds is proved from the actual string norm
bound in the preceding discrete-operator results.
-/

namespace krylov.Asymptotics
noncomputable section
open Real Finset
open krylov.Strings
open scoped BigOperators

namespace DiscreteString
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)

/-- The source ratio bound is a consequence of the actual local gap/mass
product constraint at the preceding edge. -/
theorem ratio_succ_le {Λ : ℝ} (hΛ : 0 < Λ) (j : ℕ) (hj : j < N)
    (hprod : 1 ≤ Λ * S.mass (j + 1) * S.gap j) : S.ratio (j + 1) ≤ 1 + Λ := by
  obtain ⟨hφ, hp, hK, _⟩ := S.state_bounds j hj.le
  obtain ⟨hφ', _, hK', _⟩ := S.state_bounds (j + 1) (by omega)
  have hm := S.mass_pos (j + 1) (by omega)
  have hl := S.gap_pos j hj
  have hΛm : 0 ≤ Λ * S.mass (j + 1) := mul_nonneg hΛ.le hm.le
  have hφgap : S.gap j * S.p j ≤ S.φ (j + 1) := by rw [S.φ_succ]; linarith
  have hpr : S.p j ≤ Λ * S.mass (j + 1) * S.φ (j + 1) := by
    calc
      S.p j ≤ (Λ * S.mass (j + 1) * S.gap j) * S.p j := by
        nlinarith [mul_nonneg (show 0 ≤ S.p j by linarith) (sub_nonneg.mpr hprod)]
      _ = Λ * S.mass (j + 1) * (S.gap j * S.p j) := by ring
      _ ≤ Λ * S.mass (j + 1) * S.φ (j + 1) := mul_le_mul_of_nonneg_left hφgap hΛm
  have hpr' := mul_le_mul_of_nonneg_left hpr (show 0 ≤ S.φ (j + 1) by linarith)
  rw [krylov.Strings.DiscreteString.ratio]
  apply (div_le_iff₀ (show 0 < S.K (j + 1) by linarith)).2
  rw [S.p_succ, S.K_succ]
  nlinarith [mul_nonneg hΛ.le (show 0 ≤ S.K j by linarith)]

/-- Every physical discrete ratio obeys the source's a priori interval. -/
theorem ratio_bounds {Λ : ℝ} (hΛ : 0 < Λ)
    (hprod : ∀ j < N, 1 ≤ Λ * S.mass (j + 1) * S.gap j)
    {j : ℕ} (hj : j ≤ N) : 1 ≤ S.ratio j ∧ S.ratio j ≤ 1 + Λ := by
  refine ⟨S.ratio_ge_one j hj, ?_⟩
  cases j with
  | zero => simp [krylov.Strings.DiscreteString.ratio]; linarith
  | succ j => exact ratio_succ_le S hΛ j (by omega) (hprod j (by omega))

end DiscreteString

/-- Exact one-step logarithmic energy estimate. It also covers a zero
increment, unlike an argument that divides by the logarithm. -/
theorem weighted_log_step_le {a b γ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hγ : 0 < γ) :
    b ^ (-γ) * log (b / a) ≤ (a ^ (-γ) - b ^ (-γ)) / γ := by
  have hexp := Real.add_one_le_exp (γ * (log b - log a))
  have he : b ^ (-γ) * exp (γ * (log b - log a)) = a ^ (-γ) := by
    rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos ha, ← exp_add]
    congr 1
    ring
  have hp := Real.rpow_pos_of_pos hb (-γ)
  have hm := mul_le_mul_of_nonneg_left hexp hp.le
  rw [mul_add, mul_one, he] at hm
  rw [log_div hb.ne' ha.ne']
  apply (le_div_iff₀ hγ).2
  nlinarith only [hm]

namespace DiscreteString
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)

/-- The source energy-log sum has the exact telescoping deficit, hence is
bounded independently of the number of atoms. -/
theorem weighted_energy_log_sum_le {γ : ℝ} (hγ : 0 < γ) :
    (∑ j ∈ range N, S.K (j + 1) ^ (-γ) * log (S.K (j + 1) / S.K j)) ≤ 1 / γ := by
  have hstep (j : ℕ) (hj : j ∈ range N) :
      S.K (j + 1) ^ (-γ) * log (S.K (j + 1) / S.K j) ≤
        (S.K j ^ (-γ) - S.K (j + 1) ^ (-γ)) / γ := by
    exact weighted_log_step_le
      (by linarith [(S.state_bounds j (mem_range.mp hj).le).2.2.1])
      (by linarith [(S.state_bounds (j + 1) (by have := mem_range.mp hj; omega)).2.2.1]) hγ
  calc
    _ ≤ ∑ j ∈ range N, (S.K j ^ (-γ) - S.K (j + 1) ^ (-γ)) / γ :=
      sum_le_sum hstep
    _ = (1 - S.K N ^ (-γ)) / γ := by
      rw [← sum_div, sum_range_sub']
      simp
    _ ≤ 1 / γ := by
      exact div_le_div_of_nonneg_right (sub_le_self 1 (Real.rpow_nonneg (by linarith [(S.state_bounds N le_rfl).2.2.1]) _)) hγ.le

end DiscreteString

/-- Abel's estimate in the exact form needed for weighted logarithmic ratio
increments. Decreasing weights turn a uniformly bounded primitive into a
bound that is independent of total variation. -/
theorem weighted_increment_sum_le {f g : ℕ → ℝ} {L : ℝ} (n : ℕ)
    (hf₀ : f 0 = 0) (hf : ∀ j ≤ n, f j ≤ L)
    (hg : ∀ j ≤ n, 0 ≤ g j) (hdec : ∀ j, j + 1 < n → g (j + 1) ≤ g j) :
    (∑ j ∈ range n, g j * (f (j + 1) - f j)) ≤ g 0 * L := by
  cases n with
  | zero =>
    simp only [sum_range_zero]
    have hL : 0 ≤ L := hf₀ ▸ hf 0 le_rfl
    exact mul_nonneg (hg 0 le_rfl) hL
  | succ n =>
    have haux : ∀ k ≤ n, (∑ j ∈ range (k + 1), g j * (f (j + 1) - f j)) ≤
        g k * f (k + 1) + (g 0 - g k) * L := by
      intro k hk
      induction k with
      | zero => simp [hf₀]
      | succ k ih =>
        have ih' := ih (by omega)
        rw [sum_range_succ]
        have hweight := hdec k (by omega)
        have hbound := hf (k + 1) (by omega)
        have hmul := mul_nonneg (sub_nonneg.mpr hweight) (sub_nonneg.mpr hbound)
        nlinarith only [ih', hmul]
    have hlast := haux n le_rfl
    have hmul := mul_nonneg (hg n (by omega)) (sub_nonneg.mpr (hf (n + 1) le_rfl))
    nlinarith only [hlast, hmul]

end
end krylov.Asymptotics
