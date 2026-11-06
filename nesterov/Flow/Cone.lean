import nesterov.Flow.OneSpiral

/-!
Article: Remark `cone`.
Use: the single-plane support constraints are exactly an angle--winding
cone and the minimizer inequality, with a literal infimum over all real lags.
-/

noncomputable section

namespace nesterov.Flow

theorem kernelB_pos {c γ q : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hq : 0 < q) :
    0 < kernelB c γ q := by
  have hs := Real.self_lt_sinh_iff.mpr (mul_pos hc hq)
  have hh := mul_lt_mul_of_pos_left hs hγ
  have hsin := Real.sin_le (mul_pos hγ hq).le
  have hdiv : γ * q < γ * Real.sinh (c * q) / c := by
    apply (lt_div_iff₀ hc).mpr
    nlinarith
  dsimp [kernelB]
  linarith

def coneRatio (ρ x : ℝ) : ℝ := kernelA 1 ρ x / kernelB 1 ρ x

/-- Υ in Remark cone, with the infimum taken over all positive real x. -/
def coneProfile (ρ : ℝ) : ℝ := sInf {v : ℝ | ∃ x : ℝ, 0 < x ∧ v = coneRatio ρ x}

theorem le_coneProfile_iff {ρ a : ℝ} (hρ : 0 < ρ) :
    a ≤ coneProfile ρ ↔ ∀ x : ℝ, 0 < x → a ≤ coneRatio ρ x := by
  have hbd : BddBelow {v : ℝ | ∃ x : ℝ, 0 < x ∧ v = coneRatio ρ x} := by
    refine ⟨0, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact div_nonneg (kernelA_nonneg _ _ _) (kernelB_pos (by norm_num) hρ hx).le
  have hne : ({v : ℝ | ∃ x : ℝ, 0 < x ∧ v = coneRatio ρ x}).Nonempty :=
    ⟨coneRatio ρ 1, 1, by norm_num, rfl⟩
  constructor
  · intro h x hx
    exact h.trans (csInf_le hbd ⟨x, hx, rfl⟩)
  · intro h
    apply le_csInf hne
    rintro v ⟨x, hx, rfl⟩
    exact h x hx

theorem kernels_rescale {c : ℝ} (hc : 0 < c) (γ q : ℝ) :
    kernelA c γ q = kernelA 1 (γ / c) (c * q) ∧
      kernelB c γ q = kernelB 1 (γ / c) (c * q) := by
  have he : γ / c * (c * q) = γ * q := by field_simp
  dsimp [kernelA, kernelB]
  simp only [one_mul, he, div_one]
  constructor
  · trivial
  · field_simp

/-- Remark cone: both the positive-lag program and the minimizer condition
are equivalent to the two inequalities on angle and winding ratio. -/
theorem oneAtom_iff_cone {θ m c γ : ℝ} (hc : 0 < c) (hct : c < θ / 2)
    (hγ : 0 < γ) (ha : delta θ m c < γ ^ 2) :
    OneAtomFeasible θ m c γ ↔
      (θ - 2 * c) * γ / (γ ^ 2 - delta θ m c) ≤ coneProfile (γ / c) ∧
        (γ / c) * ((θ - 2 * c) * γ / (γ ^ 2 - delta θ m c)) ≤ 1 := by
  have hρ : 0 < γ / c := div_pos hγ hc
  have hA : 0 < γ ^ 2 - delta θ m c := sub_pos.mpr ha
  have hcoef : 0 < θ - 2 * c := by linarith
  have hforward (q : ℝ) (hq : 0 < q) :
      0 ≤ forwardKernel θ m c γ q ↔
        (θ - 2 * c) * γ / (γ ^ 2 - delta θ m c) ≤ coneRatio (γ / c) (c * q) := by
    dsimp [coneRatio]
    rw [← (kernels_rescale hc γ q).1, ← (kernels_rescale hc γ q).2]
    rw [div_le_div_iff₀ hA (kernelB_pos hc hγ hq)]
    dsimp [forwardKernel]
    constructor <;> intro h <;> nlinarith
  have hmin : c * delta θ m c ≤ (3 * c - θ) * γ ^ 2 ↔
      (γ / c) * ((θ - 2 * c) * γ / (γ ^ 2 - delta θ m c)) ≤ 1 := by
    have he : (γ / c) * ((θ - 2 * c) * γ / (γ ^ 2 - delta θ m c)) =
        (θ - 2 * c) * γ ^ 2 / (c * (γ ^ 2 - delta θ m c)) := by
      field_simp
    rw [he, div_le_iff₀ (mul_pos hc hA)]
    constructor <;> intro h <;> nlinarith
  constructor
  · intro h
    refine ⟨(le_coneProfile_iff hρ).mpr ?_, hmin.mp h.2.2⟩
    intro x hx
    have hq : 0 < x / c := div_pos hx hc
    have hh := (hforward (x / c) hq).mp (h.1 _ hq)
    have he : c * (x / c) = x := by field_simp
    rwa [he] at hh
  · rintro ⟨hcone, hmini⟩
    refine ⟨?_, ?_, hmin.mpr hmini⟩
    · intro q hq
      exact (hforward q hq).mpr ((le_coneProfile_iff hρ).mp hcone (c * q) (mul_pos hc hq))
    · intro q hq
      dsimp [backwardKernel]
      exact add_nonneg (mul_nonneg hA.le (kernelA_nonneg _ _ _))
        (mul_nonneg (mul_nonneg hcoef.le hγ.le) (kernelB_nonneg hc hγ.le hq.le))

end nesterov.Flow
