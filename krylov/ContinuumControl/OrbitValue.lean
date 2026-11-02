import krylov.ContinuumControl.EndpointOrbitValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Article: main_krylov, thm:value, all positive gamma values.
Use: differentiate the actual Bellman potential in LV orbit coordinates for
every gamma. This connects the global orbit quadratures directly to the reward.
Source: the real-power, quotient and square-root chain rules in mathlib.
-/

namespace krylov.ContinuumControl
noncomputable section
open Filter
open scoped Topology

/-- Homogeneous Bellman potential in the actual LV coordinates. -/
def orbitValue (γ s U K : ℝ) : ℝ :=
  K ^ (-γ) * (U + s - 1) / (2 * γ * U * Real.sqrt s)

/-- The exact reward derivative for every actual LV-gamma trajectory and its
energy quadrature. No graph or terminal identity is supplied as a hypothesis. -/
theorem hasDerivAt_orbitValue {γ x : ℝ} {s U K : ℝ → ℝ}
    (hγ : γ ≠ 0) (hs : 0 < s x) (hU : 0 < U x) (hK : 0 < K x)
    (hds : HasDerivAt s (2 * s x * (s x - 1 - γ * U x)) x)
    (hdU : HasDerivAt U (U x * (s x + 1 - U x)) x)
    (hdK : HasDerivAt K (U x * K x) x) :
    HasDerivAt (fun t ↦ orbitValue γ (s t) (U t) (K t))
      (-Real.sqrt (s x) * K x ^ (-γ)) x := by
  have hroot := Real.sqrt_pos.mpr hs
  have hpow := hdK.rpow_const (Or.inl hK.ne') (p := -γ)
  have hd := (hpow.mul ((hdU.add hds).sub_const 1)).div
    ((hdU.const_mul (2 * γ)).mul (hds.sqrt hs.ne'))
    (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hγ) hU.ne') hroot.ne')
  convert hd using 1
  · rfl
  · have hsq : Real.sqrt (s x) ^ 2 = s x := Real.sq_sqrt hs.le
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [Real.rpow_sub_one hK.ne']
    generalize heq : Real.sqrt (s x) = t at *
    rw [← hsq]
    field_simp
    ring

/-- The actual origin normalization gives the continuum constant directly. -/
theorem orbitValue_initial (γ s : ℝ) (hs : 0 < s) :
    orbitValue γ s 1 1 = Real.sqrt s / (2 * γ) := by
  have hroot := Real.sqrt_pos.mpr hs
  have hsq := Real.sq_sqrt hs.le
  unfold orbitValue
  rw [Real.one_rpow]
  by_cases hγ : γ = 0
  · simp [hγ]
  · field_simp
    nlinarith

/-- Positive orbit states have a nonnegative potential. -/
theorem orbitValue_nonneg {γ s U K : ℝ} (hγ : 0 ≤ γ) (hU : 1 ≤ U)
    (hs : 0 ≤ s) (hK : 0 ≤ K) : 0 ≤ orbitValue γ s U K := by
  have hn : 0 ≤ U + s - 1 := by linarith
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg hK _) hn) (by positivity)

/-- On a subcritical saddle trajectory the bounded positive LV coordinates
and diverging energy imply the terminal condition; it is not an extra
assumption on the optimizing string. -/
theorem orbitValue_tendsto_zero_of_finite_state {γ sLim ULim : ℝ} {s U K : ℝ → ℝ}
    (hγ : 0 < γ) (hsLim : 0 < sLim) (hULim : 0 < ULim)
    (hs : Tendsto s atTop (𝓝 sLim)) (hU : Tendsto U atTop (𝓝 ULim))
    (hK : Tendsto K atTop atTop) :
    Tendsto (fun t ↦ orbitValue γ (s t) (U t) (K t)) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_neg_atTop hγ).comp hK
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have h := (hpow.mul ((hU.add hs).sub_const 1)).div
    ((hU.const_mul (2 * γ)).mul hroot) (by positivity : 2 * γ * ULim * Real.sqrt sLim ≠ 0)
  convert! h using 1
  simp only [zero_mul, zero_div]

end
end krylov.ContinuumControl
