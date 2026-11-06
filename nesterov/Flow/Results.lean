import nesterov.Flow.Run
import nesterov.Flow.SpiralRates
import nesterov.Flow.Spread

/-!
Article: Theorem `flow`(c,d).
Use: the proved spread construction is linked to actual smooth objectives,
then the literal all-Hilbert and all-finite-smoothness infima are evaluated.
-/

noncomputable section

namespace nesterov.Flow

theorem SpreadWitness.strictProgram {θ m c : ℝ} (w : SpreadWitness θ m c)
    (hc : 0 < c) : w.spectrum.StrictProgram θ m c w.margin := by
  have hdrop (q : ℝ) (hq : 0 < q) :
      (∑ j, w.spectrum.weight j * kernelA c (w.spectrum.frequency j) q) ≤
        w.spectrum.average (fun γ => kernelA c γ q + kernelB c γ q) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (w.spectrum.weight_nonneg j)
    linarith [kernelB_nonneg hc (w.spectrum.frequency_nonneg j) hq.le]
  refine ⟨w.margin_pos, ?_, ?_, w.minimizer⟩
  · intro q hq
    exact (mul_le_mul_of_nonneg_left (hdrop q hq) w.margin_pos.le).trans (w.forward q hq)
  · intro q hq
    exact (mul_le_mul_of_nonneg_left (hdrop q hq) w.margin_pos.le).trans (w.backward q hq)

/-- Theorem flow(c): finite-dimensional, finite-smoothness witnesses for
every exponent strictly between θ/3 and cQ, with both exact norm identities. -/
theorem exists_spiral_witness {θ m c : ℝ} (hθ : 0 < θ) (hm : 0 < m)
    (hc : θ / 3 < c) (hcQ : c < cQ θ m) :
    ∃ (J : ℕ) (L : ℝ) (f : EuclideanSpace ℂ (Fin J) → ℝ)
      (x v : ℝ → EuclideanSpace ℂ (Fin J)), 0 < J ∧ m < L ∧
      polyak.CenteredSmoothStronglyConvex m L f ∧ IsSolution θ f x v ∧
      ‖x 0‖ = 1 ∧ (∀ t : ℝ, ‖x t‖ = Real.exp (-c * t) * ‖x 0‖) ∧
      (∀ t : ℝ, ‖v t‖ = Real.exp (-c * t) * ‖v 0‖) ∧
      decayExponent x v = (c : EReal) ∧
      observableExponent (fun t => f (x t)) = ((2 * c : ℝ) : EReal) ∧
      observableExponent (fun t => energy f (x t) (v t)) = ((2 * c : ℝ) : EReal) := by
  obtain ⟨w⟩ := exists_spread hθ hm hc hcQ
  have hcp : 0 < c := by linarith
  have hct := ((lt_cQ_iff θ m c).mp hcQ).1.le
  obtain ⟨L, f, hL, hf, hsol, hvalues, hnorm, hvelocity⟩ :=
    w.spectrum.exists_smooth_spiral hm hcp hct (w.strictProgram hcp)
  obtain ⟨hs, hv, he⟩ := w.spectrum.smooth_spiral_exponents
    (of_centeredSmoothStronglyConvex hf) hvalues hvelocity
  have hzero : ‖w.spectrum.orbit c 0‖ = 1 := by simp [hnorm]
  refine ⟨w.J, L, f, w.spectrum.orbit c, w.spectrum.velocity c,
    w.J_pos, hL, hf, hsol, hzero, ?_, hvelocity, hs, hv, he⟩
  intro t
  rw [hzero, mul_one]
  exact hnorm t

theorem exists_spiral_smoothRun {θ m c : ℝ} (hθ : 0 < θ) (hm : 0 < m)
    (hc : θ / 3 < c) (hcQ : c < cQ θ m) :
    ∃ r : SmoothRun θ m, r.toRun.stateExponent = (c : EReal) ∧
      r.toRun.valueExponent = ((2 * c : ℝ) : EReal) ∧
      r.toRun.energyExponent = ((2 * c : ℝ) : EReal) := by
  obtain ⟨J, L, f, x, v, _, _, hf, hsol, hnorm, _, _, hs, hv, he⟩ :=
    exists_spiral_witness hθ hm hc hcQ
  let r : SmoothRun θ m :=
    { Carrier := EuclideanSpace ℂ (Fin J)
      f := f
      objective := of_centeredSmoothStronglyConvex hf
      x := x
      v := v
      solution := hsol
      nontrivial := by rw [hnorm]; positivity
      L := L
      smooth := hf }
  exact ⟨r, hs, hv, he⟩

theorem cap_at_open_endpoint {a b k : ℝ} {z : EReal} (hab : a < b) (hk : 0 < k)
    (h : ∀ c : ℝ, a < c → c < b → z ≤ ((k * c : ℝ) : EReal)) :
    z ≤ ((k * a : ℝ) : EReal) := by
  by_contra hz
  obtain ⟨r, har, hrz⟩ := EReal.exists_between_coe_real (lt_of_not_ge hz)
  have har' : k * a < r := EReal.coe_lt_coe_iff.mp har
  have har'' : a < r / k := (lt_div_iff₀ hk).mpr (by nlinarith)
  let d := min b (r / k)
  have had : a < d := lt_min hab har''
  let c := (a + d) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by have hd := min_le_left b (r / k); dsimp [c, d] at *; linarith
  have hcr : c < r / k := by have hd := min_le_right b (r / k); dsimp [c, d] at *; linarith
  have hkcr : k * c < r := by have hh := (lt_div_iff₀ hk).mp hcr; nlinarith
  have hh := h c hac hcb
  exact (not_lt_of_ge hh) ((EReal.coe_lt_coe_iff.mpr hkcr).trans hrz)

theorem smooth_inf_upper {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) :
    worstSmoothStateExponent θ m ≤ (cF θ m : EReal) ∧
      worstSmoothValueExponent θ m ≤ ((2 * cF θ m : ℝ) : EReal) ∧
      worstSmoothEnergyExponent θ m ≤ ((2 * cF θ m : ℝ) : EReal) := by
  obtain ⟨hQstate, hQvalue, hQenergy⟩ := quadratic_inf_upper hθ hm
  by_cases hgap : θ / 3 < cQ θ m
  · have hstate : worstSmoothStateExponent θ m ≤ (θ / 3 : ℝ) := by
      have hh := cap_at_open_endpoint (z := worstSmoothStateExponent θ m) hgap (by norm_num : (0 : ℝ) < 1)
        (fun c hc hcQ => by
          obtain ⟨r, hs, _, _⟩ := exists_spiral_smoothRun hθ hm hc hcQ
          rw [one_mul]
          exact sInf_le ⟨r, hs⟩)
      simpa using hh
    have hvalue : worstSmoothValueExponent θ m ≤ ((2 * (θ / 3) : ℝ) : EReal) := by
      apply cap_at_open_endpoint hgap (by norm_num : (0 : ℝ) < 2)
      intro c hc hcQ
      obtain ⟨r, _, hv, _⟩ := exists_spiral_smoothRun hθ hm hc hcQ
      exact sInf_le ⟨r, hv⟩
    have henergy : worstSmoothEnergyExponent θ m ≤ ((2 * (θ / 3) : ℝ) : EReal) := by
      apply cap_at_open_endpoint hgap (by norm_num : (0 : ℝ) < 2)
      intro c hc hcQ
      obtain ⟨r, _, _, he⟩ := exists_spiral_smoothRun hθ hm hc hcQ
      exact sInf_le ⟨r, he⟩
    rw [cF, min_eq_left hgap.le]
    exact ⟨hstate, hvalue, henergy⟩
  · rw [cF, min_eq_right (le_of_not_gt hgap)]
    exact ⟨hQstate, hQvalue, hQenergy⟩

/-- Theorem flow(d): exact state, gap, and energy infima, over the full class
F_m and equivalently over the union of all finite global smoothness bounds. -/
theorem exact_worst_exponents {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) :
    worstStateExponent θ m = (cF θ m : EReal) ∧
      worstSmoothStateExponent θ m = (cF θ m : EReal) ∧
      worstValueExponent θ m = ((2 * cF θ m : ℝ) : EReal) ∧
      worstSmoothValueExponent θ m = ((2 * cF θ m : ℝ) : EReal) ∧
      worstEnergyExponent θ m = ((2 * cF θ m : ℝ) : EReal) ∧
      worstSmoothEnergyExponent θ m = ((2 * cF θ m : ℝ) : EReal) := by
  obtain ⟨hslo, hvlo, helo⟩ := universal_inf_lower (m := m) hθ
  obtain ⟨hss, hvs, hes⟩ := universal_inf_le_smooth θ m
  obtain ⟨hshi, hvhi, hehi⟩ := smooth_inf_upper hθ hm
  exact ⟨le_antisymm (hss.trans hshi) hslo, le_antisymm hshi (hslo.trans hss),
    le_antisymm (hvs.trans hvhi) hvlo, le_antisymm hvhi (hvlo.trans hvs),
    le_antisymm (hes.trans hehi) helo, le_antisymm hehi (helo.trans hes)⟩

end nesterov.Flow
