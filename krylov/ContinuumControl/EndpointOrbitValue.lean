import krylov.ContinuumControl.EndpointDecay

/-!
Article: main_krylov, thm:value and apC:prop:g1, attained endpoint value.
Use: the Bellman potential along the actual endpoint LV orbit differentiates
to minus its reward, directly in orbit coordinates. Its terminal decay follows
from the proved orbit corridor, without assuming a global graph parametrization.
Source: quotient/square-root differentiation and the elementary corridor bound.
-/

namespace krylov.ContinuumControl
noncomputable section
open Filter
open scoped Topology

/-- Endpoint Bellman potential expressed in the actual LV state coordinates. -/
def endpointOrbitValue (s U K : ℝ) : ℝ := (U + s - 1) / (2 * U * Real.sqrt s * K)

/-- Exact potential derivative on an actual endpoint orbit with its energy
quadrature. No graph or desired potential identity is an input hypothesis. -/
theorem hasDerivAt_endpointOrbitValue {s U K : ℝ → ℝ} {x : ℝ}
    (hs : 0 < s x) (hU : 0 < U x) (hK : 0 < K x)
    (hds : HasDerivAt s (2 * s x * (s x - 1 - U x)) x)
    (hdU : HasDerivAt U (U x * (s x + 1 - U x)) x)
    (hdK : HasDerivAt K (U x * K x) x) :
    HasDerivAt (fun t ↦ endpointOrbitValue (s t) (U t) (K t))
      (-Real.sqrt (s x) / K x) x := by
  have hroot := Real.sqrt_pos.mpr hs
  have hd := ((hdU.add hds).sub_const 1).div
    ((((hdU.const_mul 2).mul (hds.sqrt hs.ne')).mul hdK))
    (by positivity : 2 * U x * Real.sqrt (s x) * K x ≠ 0)
  convert hd using 1
  · rfl
  · have hsq : Real.sqrt (s x) ^ 2 = s x := Real.sq_sqrt hs.le
    simp only [Pi.mul_apply, Pi.add_apply]
    generalize heq : Real.sqrt (s x) = t at *
    rw [← hsq]
    field_simp
    ring

theorem endpointOrbitValue_nonneg {s U K : ℝ} (hU : 1 ≤ U)
    (hs : U + 1 ≤ s) (hK : 0 ≤ K) : 0 ≤ endpointOrbitValue s U K :=
  div_nonneg (by linarith) (by positivity)

/-- A majorant valid pointwise on the genuine endpoint orbit corridor. -/
theorem endpointOrbitValue_bound {s U K : ℝ} (hU : 1 ≤ U)
    (hs : U + 1 ≤ s) (hs' : s ≤ 4 * U) (hK : 1 ≤ K) :
    endpointOrbitValue s U K ≤ 5 / (2 * Real.sqrt (U + 1)) := by
  have hpos : 0 < U := by linarith
  have hspos : 0 < s := by linarith
  have hroot := Real.sqrt_pos.mpr hspos
  have hnum : 0 ≤ U + s - 1 := by linarith
  have hf : 0 ≤ (U + s - 1) / (2 * U * Real.sqrt s) := by positivity
  calc
    endpointOrbitValue s U K = ((U + s - 1) / (2 * U * Real.sqrt s)) / K := by
      rw [endpointOrbitValue, div_div]
    _ ≤ (U + s - 1) / (2 * U * Real.sqrt s) := div_le_self hf hK
    _ ≤ (5 * U) / (2 * U * Real.sqrt s) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 5 / (2 * Real.sqrt s) := by field_simp
    _ ≤ 5 / (2 * Real.sqrt (U + 1)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by nlinarith [Real.sqrt_le_sqrt hs])

/-- The terminal potential really vanishes on every actual orbit satisfying
the established endpoint corridor and U→∞. -/
theorem endpointOrbitValue_tendsto_zero {s U K : ℝ → ℝ}
    (hU : Tendsto U atTop atTop)
    (hc : ∀ᶠ t in atTop, 1 ≤ U t ∧ U t + 1 ≤ s t ∧ s t ≤ 4 * U t ∧ 1 ≤ K t) :
    Tendsto (fun t ↦ endpointOrbitValue (s t) (U t) (K t)) atTop (𝓝 0) := by
  have hroot := Real.tendsto_sqrt_atTop.comp
    (tendsto_atTop_add_const_right atTop 1 hU)
  have hlim : Tendsto (fun t ↦ 5 / (2 * Real.sqrt (U t + 1))) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp hroot).const_mul (5 / 2 : ℝ)
    simpa only [Function.comp_def, mul_zero, zero_mul, div_eq_mul_inv, mul_inv_rev,
      mul_assoc, mul_comm, mul_left_comm] using h
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hc] with t ht
    exact endpointOrbitValue_nonneg ht.1 ht.2.1 (by linarith [ht.2.2.2])
  · filter_upwards [hc] with t ht
    exact endpointOrbitValue_bound ht.1 ht.2.1 ht.2.2.1 ht.2.2.2

end
end krylov.ContinuumControl
