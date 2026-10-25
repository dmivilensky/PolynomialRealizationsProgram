import polyak.Realization.Startup
import polyak.Dynamics.Rate
import Mathlib.Topology.Order.LiminfLimsup

/-!
Article: spectralgeneral(c), the original rate lower bound.
Use: pass the single all-horizon actual example to W_N and its original limsup rate.
Proof: dimension inclusion in the actual supremum and the nth-root limit of its positive prefactor.
-/

namespace polyak.Realization
noncomputable section
open Dynamics Filter Set
open scoped Topology

/-- Article: a genuine all-horizon example gives a finite-horizon source lower bound. -/
theorem example_le_worstAll {μ L α β c t : ℝ} {d : ℕ} (hd : 0<d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : CenteredSmoothStronglyConvex μ L f)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (x₀ : EuclideanSpace ℝ (Fin d)) (hx : x₀≠0)
    (h : ∀ N : ℕ,c*Real.exp (N*t)*‖x₀‖ ≤ ‖iterate (gradient f) α β x₀ N‖) (N : ℕ) :
    c*Real.exp (N*t) ≤ worstAll μ L α β N := by
  have hxpos := norm_pos_iff.mpr hx
  have hmin : ∀ y,f 0 ≤ f y := (hf.toSmoothStronglyConvex.minimizer_iff 0).mpr hf.gradient_zero
  have hr : ‖iterate (gradient f) α β x₀ N‖/‖x₀‖∈ratios μ L α β d N := by
    refine ⟨f,hf.toSmoothStronglyConvex,0,x₀,hmin,hx,?_⟩
    simp
  calc
    c*Real.exp (N*t) ≤ ‖iterate (gradient f) α β x₀ N‖/‖x₀‖ := (le_div_iff₀ hxpos).mpr (h N)
    _ ≤ worstAll μ L α β N := le_csSup
      (allRatios_bddAbove hf.mu_pos hf.mu_lt_L hα hβ N) (mem_insert_of_mem _ ⟨d,hd,hr⟩)

/-- Article: a positive exponential lower bound gives the actual source limsup rate. -/
theorem exp_le_rate_of_example {μ L α β c t : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0<c)
    (h : ∀ N : ℕ,c*Real.exp (N*t) ≤ worstAll μ L α β N) :
    Real.exp t ≤ rate μ L α β := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hcroot : Tendsto (fun n : ℕ => c^((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa only [Function.comp_def,Real.rpow_zero] using
      (Real.continuousAt_const_rpow (a := c) (b := 0) (ne_of_gt hc)).tendsto.comp hinv
  have hlim := hcroot.mul_const (Real.exp t)
  simp only [one_mul] at hlim
  have hcmp : ∀ᶠ N : ℕ in atTop,c^((N : ℝ)⁻¹)*Real.exp t ≤ worstAll μ L α β N^((N : ℝ)⁻¹) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNne : (N : ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hN)
    have hex : Real.exp (N*t)^((N : ℝ)⁻¹)=Real.exp t := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      congr 1
      field_simp
    have hh := Real.rpow_le_rpow (mul_pos hc (Real.exp_pos _)).le (h N) (by positivity : 0 ≤ (N : ℝ)⁻¹)
    rwa [Real.mul_rpow hc.le (Real.exp_pos _).le,hex] at hh
  have hh := limsup_le_limsup hcmp hlim.isCoboundedUnder_le
    (isBoundedUnder_of ⟨1+α*L+2*β,worstAll_root_le hμ hL hα hβ⟩)
  rwa [hlim.limsup_eq] at hh

variable {J : Type*} [Fintype J]

/-- Article: spectralgeneral(c), in particular ρ≥eᵗ.
Use: finitely supported spectral feasibility yields the lower rate of the original from-rest problem. -/
theorem exp_le_originalRate {μ L α β C t : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0 ≤ β) (hβ1 : β<1) (hquad : α*L<2*(1+β))
    (w : J → NNReal) (c : J → Spectral.Frequency) (hw : ∑ j,w j=1)
    (h : Waves.MixtureFeasible (Waves.finiteSpectrum w c hw)
      (Waves.multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β t) C t)
    (hstrict : 0<t → |C|<Waves.spectrumG (Waves.finiteSpectrum w c hw)
      (Waves.multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β t)) :
    Real.exp t ≤ rate μ L α β := by
  obtain ⟨f,hf,x₀,hx,c₀,hc₀,hh⟩ := exists_startup hμ hL hα hβ hβ1 hquad w c hw h hstrict
  exact exp_le_rate_of_example hμ hL hα.le hβ hc₀
    (fun N => example_le_worstAll (by omega) f hf hα.le hβ x₀ hx hh N)

end
end polyak.Realization
