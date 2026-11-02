import jacobi.Continuum.Moments
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Article: jacobi, Section 3.5 (edge data and the lower constant).
Moment upper bounds and recovery of the top eigenvalue hold for every finite
mass. These statements concern the same ordered spectra already constructed
in chebyshev2, with no compact-support or normalization assumptions.
Use: controls all high spectral moments in the continuum relaxation.
-/

namespace jacobi.Continuum
noncomputable section
open chebyshev2.Continuum MeasureTheory Real Filter
open scoped BigOperators Topology

/-- Every positive spectral moment is bounded by the mass times a power of the top eigenvalue.
Use: controls all high spectral moments in the continuum relaxation.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: each summand satisfies a_j^(n+1) ≤ a_0^n a_j. -/
theorem moment_bound {a : ℕ → ℝ} (ha : Summable a) (hn : ∀ i, 0 ≤ a i)
    (hs : Antitone a) (n : ℕ) :
    (∑' i, a i^(n+1)) ≤ a 0^n * ∑' i, a i := by
  rw [← tsum_mul_left]
  apply (summable_powers ha hn (by omega : 0 < n+1)).tsum_le_tsum _ (ha.mul_left _)
  intro i
  calc
    _ = a i^n * a i := pow_succ _ _
    _ ≤ a 0^n * a i :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hn i) (hs (Nat.zero_le i)) n) (hn i)

/-- A nonnegative number is recovered by taking the positive integer root of its power.
Use: gives the exact lower and upper endpoints in the moment-root squeeze.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: multiply the reciprocal exponent by the positive integer exponent. -/
theorem root_power (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (a^(n+1)) ^ (1 / ((n : ℝ)+1)) = a := by
  rw [← Real.rpow_natCast_mul ha]
  have he : ((n+1 : ℕ) : ℝ) * (1 / ((n : ℝ)+1)) = 1 := by
    push_cast
    field_simp
  rw [he, Real.rpow_one]

/-- The roots of spectral moments converge to the top eigenvalue, at arbitrary finite mass.
Use: justifies the article's notation G_∞ and its interpretation as the limiting moment.
Article: jacobi, Proposition D.2.
Proof: squeeze between a_0 and a_0(Σa/a_0)^(1/p); handle the zero spectrum separately. -/
theorem moment_root_limit {a : ℕ → ℝ} (ha : Summable a) (hn : ∀ i, 0 ≤ a i)
    (hs : Antitone a) :
    Tendsto (fun n : ℕ => (∑' i, a i^(n+1)) ^ (1 / ((n : ℝ)+1))) atTop (𝓝 (a 0)) := by
  -- Treat the zero spectrum first; otherwise squeeze moment roots using the positive top eigenvalue.
  by_cases hz : a 0 = 0
  · have he (i : ℕ) : a i = 0 := le_antisymm (by simpa [hz] using hs (Nat.zero_le i)) (hn i)
    have hf : (fun n : ℕ => (∑' i, a i^(n+1)) ^ (1 / ((n : ℝ)+1))) = fun _ => (0 : ℝ) := by
      funext n
      simp only [he, zero_pow (by omega : n+1 ≠ 0), tsum_zero]
      exact Real.zero_rpow (by positivity)
    rw [hf, hz]
    exact tendsto_const_nhds
  have h0 : 0 < a 0 := lt_of_le_of_ne (hn 0) (Ne.symm hz)
  have hM : 0 < ∑' i, a i := h0.trans_le (ha.le_tsum 0 (fun i _ => hn i))
  let C := (∑' i, a i) / a 0
  have hC : 0 < C := div_pos hM h0
  have hu : Tendsto (fun n : ℕ => a 0 * C ^ (1 / ((n : ℝ)+1))) atTop (𝓝 (a 0)) := by
    have h := (tendsto_const_nhds (x := a 0)).mul
      ((tendsto_const_nhds (x := C)).rpow tendsto_one_div_add_atTop_nhds_zero_nat (Or.inl hC.ne'))
    simpa only [Real.rpow_zero, mul_one] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro n
    have h := (summable_powers ha hn (by omega : 0 < n+1)).le_tsum 0
      (fun i _ => pow_nonneg (hn i) _)
    have hr := Real.rpow_le_rpow (pow_nonneg (hn 0) _) h
      (by positivity : 0 ≤ (1 / ((n : ℝ)+1)))
    rwa [root_power _ (hn 0)] at hr
  · intro n
    have h := moment_bound ha hn hs n
    have he : a 0^n * (∑' i, a i) = a 0^(n+1) * C := by
      dsimp [C]
      rw [pow_succ]
      field_simp
    rw [he] at h
    have hr := Real.rpow_le_rpow (tsum_nonneg (fun i => pow_nonneg (hn i) _)) h
      (by positivity : 0 ≤ (1 / ((n : ℝ)+1)))
    rwa [Real.mul_rpow (pow_nonneg (hn 0) _) hC.le, root_power _ (hn 0)] at hr

/-- The actual continuum operator obeys the moment estimate with its own mass.
Use: supplies uniform spectral bounds for all admissible densities.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: use the ordered positive spectrum and the existing trace equals mass identity. -/
theorem kernel_moment_bound {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (n : ℕ) :
    (∑' i, kernelEigenvalue hm hn i^(n+1)) ≤
      kernelEigenvalue hm hn 0^n * ∫ x, m x := by
  have h := moment_bound (kernelSpectralData hm hn).eigenvalue_summable
    (kernelSpectralData hm hn).eigenvalue_nonneg (kernelSpectralData hm hn).eigenvalue_antitone n
  change (∑' i, kernelEigenvalue hm hn i^(n+1)) ≤
    kernelEigenvalue hm hn 0^n * ∑' i, kernelEigenvalue hm hn i at h
  rwa [kernelEigenvalue_mass hm hn] at h

/-- The moment roots of the actual continuum kernel converge to its largest eigenvalue.
Use: establishes G_∞ for the same densities and operators as every finite moment.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: apply the general nonnegative summable-spectrum limit to the existing ordered spectrum. -/
theorem kernel_moment_root_limit {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    Tendsto (fun n : ℕ => (∑' i, kernelEigenvalue hm hn i^(n+1)) ^
      (1 / ((n : ℝ)+1))) atTop (𝓝 (kernelEigenvalue hm hn 0)) :=
  moment_root_limit (kernelSpectralData hm hn).eigenvalue_summable
    (kernelSpectralData hm hn).eigenvalue_nonneg (kernelSpectralData hm hn).eigenvalue_antitone

end
end jacobi.Continuum
