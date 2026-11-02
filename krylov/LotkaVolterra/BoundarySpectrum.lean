import krylov.LotkaVolterra.Saddle
import Mathlib.Analysis.Complex.Basic

/-!
Article: main_krylov, apC:prop:LV, the boundary hyperbolic sink.
Use: check the spectrum of the actual real Jacobian after complexification,
including all complex eigenvalues. At (0,1) both eigenvalues have strictly
negative real part for every positive gamma, so the boundary classification
does not rely on a phase-portrait assertion supplied as a hypothesis.
Source: the actual polynomial derivative and triangular-matrix eigenvalue algebra.
-/

namespace krylov.LotkaVolterra
noncomputable section

/-- Complexification of the real Fréchet derivative already computed in Saddle. -/
def complexJacobian (γ : ℝ) (z : ℝ × ℝ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  ((((4 * z.1 - 2 - 2 * γ * z.2 : ℝ) : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ +
    ((-2 * γ * z.1 : ℝ) : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((z.2 : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      ((z.1 + 1 - 2 * z.2 : ℝ) : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ))

/-- The complexified operator agrees with the actual derivative on real vectors. -/
theorem complexJacobian_real (γ : ℝ) (z v : ℝ × ℝ) :
    complexJacobian γ z ((v.1 : ℂ), (v.2 : ℂ)) =
      (((jacobian γ z v).1 : ℂ), ((jacobian γ z v).2 : ℂ)) := by
  rw [jacobian_apply]
  ext <;> simp [complexJacobian, sub_eq_add_neg]

/-- All complex eigenvalues at the boundary point (0,1) are exactly the two
negative real diagonal entries. -/
theorem boundary_sink_eigenvalues (γ : ℝ) (η : ℂ) :
    (∃ v : ℂ × ℂ, v ≠ 0 ∧ complexJacobian γ (0, 1) v = η • v) ↔
      η = ((-2 * (1 + γ) : ℝ) : ℂ) ∨ η = -1 := by
  constructor
  · rintro ⟨v, hv, he⟩
    have h₁ : (-2 - 2 * (γ : ℂ)) * v.1 = η * v.1 := by
      simpa [complexJacobian] using congrArg Prod.fst he
    have h₂ : v.1 - v.2 = η * v.2 := by
      have h := congrArg Prod.snd he
      norm_num [complexJacobian] at h
      simpa only [sub_eq_add_neg] using h
    by_cases hv₁ : v.1 = 0
    · have hv₂ : v.2 ≠ 0 := by
        intro hv₂
        exact hv (Prod.ext hv₁ hv₂)
      right
      rw [hv₁] at h₂
      have hprod : (η + 1) * v.2 = 0 := by linear_combination -h₂
      exact eq_neg_iff_add_eq_zero.mpr ((mul_eq_zero.mp hprod).resolve_right hv₂)
    · left
      have hprod : (η + 2 * (1 + (γ : ℂ))) * v.1 = 0 := by linear_combination -h₁
      have hh := (mul_eq_zero.mp hprod).resolve_right hv₁
      push_cast
      linear_combination hh
  · rintro (rfl | rfl)
    · refine ⟨((-(1 + 2 * (γ : ℂ))), 1), by simp, ?_⟩
      ext <;> simp [complexJacobian] <;> ring
    · refine ⟨(0, 1), by simp, ?_⟩
      ext <;> norm_num [complexJacobian]

/-- The boundary point (0,1) has no centre or unstable spectral direction:
every eigenvalue of its actual complexified derivative has negative real part. -/
theorem boundary_sink_spectrum_negative {γ : ℝ} (hγ : 0 < γ)
    {η : ℂ} {v : ℂ × ℂ} (hv : v ≠ 0)
    (he : complexJacobian γ (0, 1) v = η • v) : η.re < 0 := by
  rcases (boundary_sink_eigenvalues γ η).mp ⟨v, hv, he⟩ with rfl | rfl
  · simp only [Complex.ofReal_re]
    linarith
  · norm_num

end
end krylov.LotkaVolterra
