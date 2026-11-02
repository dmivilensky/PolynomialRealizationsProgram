import krylov.Design.HyperbolicIntegral

/-!
Article: main_krylov, apC:lem:poisson, leading majorant asymptotics.
Use: prove actual theta-scaled sech and sech-square sums converge to pi/2 and
one, respectively, by a quantitative integral comparison. This supplies the
leading constants independently of the more precise Poisson identities.
Source: the integral test in mathlib and the exact hyperbolic primitives.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory Set jacobi.Young
open scoped Topology

/-- Quantitative Riemann-sum bounds for any nonnegative decreasing integrable half-line profile.
Article: main_krylov, apC:lem:poisson, majorant leading constants.
Proof: apply mathlib's two integral-test inequalities to the actual rescaled profile. -/
theorem scaled_antitone_sample_bounds (f : ℝ → ℝ) (hanti : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi 0, 0 ≤ f x)
    {θ : ℝ} (hθ : 0 < θ) :
    (∫ x in Ioi 0, f x) - θ * f 0 ≤ θ * (∑' n : ℕ, f (((n : ℝ) + 1) * θ)) ∧
      θ * (∑' n : ℕ, f (((n : ℝ) + 1) * θ)) ≤ ∫ x in Ioi 0, f x := by
  let g : ℝ → ℝ := fun x => f (x * θ)
  have ha : AntitoneOn g (Ici 0) := by
    intro x hx y hy hxy
    exact hanti (mul_nonneg hx hθ.le) (mul_nonneg hy hθ.le)
      (mul_le_mul_of_nonneg_right hxy hθ.le)
  have hg : IntegrableOn g (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_right_iff f 0 hθ).mpr
    simpa only [zero_mul] using hi
  have hgn : ∀ x ∈ Ioi 0, 0 ≤ g x := fun x hx => hn (x * θ) (mul_pos hx hθ)
  have hs := ha.summable_of_integrableOn_Ioi_zero hg hgn
  have hu := ha.tsum_add_one_le_integral hg hgn
  have hl := ha.integral_le_tsum hs hgn
  have he : (∫ x in Ioi 0, g x) = θ⁻¹ * ∫ x in Ioi 0, f x := by
    simpa only [g, zero_mul, smul_eq_mul] using integral_comp_mul_right_Ioi f 0 hθ
  have hsum : (∑' n : ℕ, g n) = f 0 + ∑' n : ℕ, f (((n : ℝ) + 1) * θ) := by
    rw [hs.tsum_eq_zero_add]
    simp only [g, Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one]
  rw [he, hsum] at hl
  rw [he] at hu
  have hu' : (∑' n : ℕ, f (((n : ℝ) + 1) * θ)) ≤ θ⁻¹ * ∫ x in Ioi 0, f x := by
    simpa only [g, Nat.cast_add, Nat.cast_one] using hu
  have hc : θ * (θ⁻¹ * ∫ x in Ioi 0, f x) = ∫ x in Ioi 0, f x := by
    rw [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul]
  have hupper := mul_le_mul_of_nonneg_left hu' hθ.le
  rw [hc] at hupper
  have hlower := mul_le_mul_of_nonneg_left hl hθ.le
  rw [hc] at hlower
  exact ⟨by nlinarith, hupper⟩

/-- Hyperbolic secant decreases on the nonnegative half-line.
Article: main_krylov, apC:lem:poisson. -/
theorem sech_antitoneOn : AntitoneOn sech (Ici 0) := by
  intro x hx y hy hxy
  apply (inv_le_inv₀ (Real.cosh_pos y) (Real.cosh_pos x)).mpr
  exact Real.cosh_strictMonoOn.monotoneOn hx hy hxy

/-- The actual scaled secant sum has sharp elementary integral bounds.
Article: main_krylov, the leading upper Chebyshev majorant asymptotic. -/
theorem sampledSech_scaled_bounds {θ : ℝ} (hθ : 0 < θ) :
    π / 2 - θ ≤ θ * sampledSech θ ∧ θ * sampledSech θ ≤ π / 2 := by
  have h := scaled_antitone_sample_bounds sech sech_antitoneOn sech_integrable.integrableOn
    (fun x _ => (sech_pos x).le) hθ
  rw [integral_Ioi_sech] at h
  simpa only [sampledSech, sech, Real.cosh_zero, inv_one, mul_one] using h

/-- The actual scaled Chebyshev secant majorant converges to pi/2 as theta tends to zero from above.
Article: main_krylov, the asymptotic upper endpoint pi/2 after thm:B.
Proof: squeeze between the exact integral constant and its explicit one-mesh error. -/
theorem sampledSech_scaled_tendsto :
    Tendsto (fun θ : ℝ => θ * sampledSech θ) (𝓝[>] 0) (𝓝 (π / 2)) := by
  have hl : Tendsto (fun θ : ℝ => π / 2 - θ) (𝓝[>] 0) (𝓝 (π / 2)) := by
    have hc : ContinuousAt (fun θ : ℝ => π / 2 - θ) 0 := continuousAt_const.sub continuousAt_id
    simpa only [sub_zero] using
      hc.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  apply hl.squeeze' tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact (sampledSech_scaled_bounds hθ).1
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact (sampledSech_scaled_bounds hθ).2

end
end krylov.Design
