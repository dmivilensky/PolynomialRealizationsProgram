import polyak.Results.OptimalExamples
import polyak.Growth.OriginalRate

/-!
Article: Theorem rate, the unrestricted finite-horizon worst cases have a genuine root limit.
Use: a single all-horizon example gives the lower limit; the exact free growth
envelope gives the upper limit, independently of the stronger constant-prefactor theorem.
-/

namespace polyak.Results
noncomputable section
open Filter Dynamics Spectral Growth
open scoped Topology

theorem prefactor_root_tendsto {c : ℝ} (hc : 0<c) (t : ℝ) :
    Tendsto (fun n : ℕ => c^((n : ℝ)⁻¹)*Real.exp t) atTop (𝓝 (Real.exp t)) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hcroot : Tendsto (fun n : ℕ => c^((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa only [Function.comp_def,Real.rpow_zero] using
      (Real.continuousAt_const_rpow (a:=c) (b:=0) hc.ne').tendsto.comp hinv
  simpa only [one_mul] using hcroot.mul_const (Real.exp t)

theorem prefactor_root_le {c t : ℝ} {w : ℕ → ℝ} (hc : 0<c)
    (h : ∀ n : ℕ,c*Real.exp (n*t)≤w n) :
    ∀ᶠ n : ℕ in atTop,c^((n : ℝ)⁻¹)*Real.exp t≤w n^((n : ℝ)⁻¹) := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hex : Real.exp (n*t)^((n : ℝ)⁻¹)=Real.exp t := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    congr 1
    field_simp
  have hh := Real.rpow_le_rpow (mul_pos hc (Real.exp_pos _)).le (h n)
    (by positivity : 0≤(n : ℝ)⁻¹)
  rwa [Real.mul_rpow hc.le (Real.exp_pos _).le,hex] at hh

/-- Article: the root limit of W_N is the actual exact rate, not merely a limsup. -/
theorem tendsto_worstAll_root {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    Tendsto (fun n : ℕ => worstAll μ L (polyakAlpha μ L) (polyakBeta μ L) n^((n : ℝ)⁻¹))
      atTop (𝓝 (Real.exp (T (polyakQ μ L)))) := by
  let q := polyakQ μ L
  obtain ⟨c,hc,hlower⟩ := exists_worstAll_optimal_lower hμ hL
  have hlow := prefactor_root_tendsto hc (T q)
  have hcomp := prefactor_root_le hc hlower
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ => (Real.sqrt 2)^((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero,Function.comp_def] using
      (Real.continuousAt_const_rpow (a:=Real.sqrt 2) (b:=0) (by positivity)).tendsto.comp hinv
  have hq : 0<q := polyakQ_pos hμ hL
  have hup := hsqrt.mul (tendsto_envelope_root (A:=0) (β:=q^2) (by positivity : 2*q≠0))
  have hfree : growthRate 0 (2*q) (q^2)=Real.exp (T q) := freeRate_eq_exp_T hq
  rw [one_mul,hfree] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup hcomp
  apply Eventually.of_forall
  intro n
  have hh := Real.rpow_le_rpow
    (worstAll_nonneg hμ hL (polyakAlpha_pos hμ hL).le (polyakBeta_mem hμ hL).1 n)
    (worstAll_le_envelope μ L (polyakAlpha μ L) (polyakBeta μ L) n)
    (by positivity : 0≤(n : ℝ)⁻¹)
  rw [polyak_normalizedA hμ hL,polyak_normalizedB hμ hL] at hh
  exact hh.trans_eq (Real.mul_rpow (Real.sqrt_nonneg _) (envelope_nonneg 0 (2*q) (q^2) n))

/-- Article: one finite dimension already has the same genuine root limit.
The separate support-classification theorem is needed to specialize this dimension to five. -/
theorem exists_dimension_tendsto_worst_root {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    ∃ d : ℕ,0<d ∧ Tendsto
      (fun n : ℕ => worst μ L (polyakAlpha μ L) (polyakBeta μ L) d n^((n : ℝ)⁻¹))
      atTop (𝓝 (Real.exp (T (polyakQ μ L)))) := by
  obtain ⟨d,hd,f,hf,x₀,hx,c,hc,hbound⟩ := exists_finite_dimensional_optimal_example hμ hL
  have hxpos := norm_pos_iff.mpr hx
  have hmin : ∀ y,f 0≤f y := (hf.toSmoothStronglyConvex.minimizer_iff 0).mpr hf.gradient_zero
  have hlower (n : ℕ) : c*Real.exp (n*T (polyakQ μ L))≤
      worst μ L (polyakAlpha μ L) (polyakBeta μ L) d n := by
    have hr : ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ n‖/‖x₀‖∈
        ratios μ L (polyakAlpha μ L) (polyakBeta μ L) d n := by
      refine ⟨f,hf.toSmoothStronglyConvex,0,x₀,hmin,hx,?_⟩
      simp
    exact ((le_div_iff₀ hxpos).mpr (hbound n)).trans
      (le_csSup (ratios_bddAbove hμ hL (polyakAlpha_pos hμ hL).le
        (polyakBeta_mem hμ hL).1 d n) (Set.mem_insert_of_mem _ hr))
  refine ⟨d,hd,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (prefactor_root_tendsto hc (T (polyakQ μ L))) (tendsto_worstAll_root hμ hL)
    (prefactor_root_le hc hlower)
  apply Eventually.of_forall
  intro n
  exact Real.rpow_le_rpow
    (worst_nonneg hμ hL (polyakAlpha_pos hμ hL).le (polyakBeta_mem hμ hL).1 d n)
    (worst_le_worstAll hμ hL (polyakAlpha_pos hμ hL).le (polyakBeta_mem hμ hL).1 hd n)
    (by positivity)

end
end polyak.Results
