import jacobi.Young.Sharp
import jacobi.Variational.Semicontinuity

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
The source theorem assumes only integrability of m^(3/2). Compact spatial and
amplitude cutoffs give actual finite-mass densities, so the verified sharp
inequality applies to each cutoff. Fatou on R² then proves the full extended
double-integral inequality without an unproved L1 assumption on m.
Use: approximates arbitrary finite-energy densities by actual finite-mass ones.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real Set Filter jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Simultaneous spatial and amplitude cutoff at the positive level n+1.
Use: approximates arbitrary finite-energy densities by actual finite-mass ones.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def cutoff (m : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (Icc (-(n+1 : ℝ)) (n+1 : ℝ)).indicator (fun x => min (m x) (n+1 : ℝ))

/-- Every cutoff of a measurable density remains measurable.
Use: supplies both the variational density and the product-space Fatou integrands.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: measurable minimum and the indicator of a closed interval preserve measurability. -/
theorem cutoff_measurable {m : ℝ → ℝ} (hm : Measurable m) (n : ℕ) : Measurable (cutoff m n) :=
  (hm.min measurable_const).indicator measurableSet_Icc

/-- The cutoff remains nonnegative.
Use: real powers and all extended product integrals stay on their nonnegative branches.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: both the amplitude minimum and the interval indicator are nonnegative. -/
theorem cutoff_nonneg {m : ℝ → ℝ} (hn : ∀ x, 0 ≤ m x) (n : ℕ) (x : ℝ) :
    0 ≤ cutoff m n x :=
  indicator_nonneg (fun y _ => le_min (hn y) (by positivity)) x

/-- The cutoff is bounded above by the original density everywhere.
Use: every approximate energy is at most the original finite energy.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: inside the interval use min≤m; outside use nonnegativity of m. -/
theorem cutoff_le {m : ℝ → ℝ} (hn : ∀ x, 0 ≤ m x) (n : ℕ) (x : ℝ) : cutoff m n x ≤ m x := by
  by_cases hx : x ∈ Icc (-(n+1 : ℝ)) (n+1 : ℝ)
  · exact (indicator_of_mem hx _).trans_le (min_le_left _ _)
  · simpa only [cutoff,indicator_of_notMem hx] using hn x

/-- Each cutoff has finite mass without any mass hypothesis on the original density.
Use: constructs admissible inputs for the finite-mass sharp Young theorem.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: dominate by the constant n+1 on a finite-volume compact interval. -/
theorem cutoff_integrable {m : ℝ → ℝ} (hm : Measurable m) (hn : ∀ x, 0 ≤ m x) (n : ℕ) :
    Integrable (cutoff m n) := by
  -- The L1 majorant is compactly supported even when m itself has infinite mass.
  have hi : Integrable ((Icc (-(n+1 : ℝ)) (n+1 : ℝ)).indicator (fun _ : ℝ => (n+1 : ℝ))) :=
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top)).integrable_indicator measurableSet_Icc
  apply hi.mono' (cutoff_measurable hm n).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_nonneg hn n x)]
    by_cases hx : x ∈ Icc (-(n+1 : ℝ)) (n+1 : ℝ)
    · simpa only [cutoff,indicator_of_mem hx] using min_le_right (m x) (n+1 : ℝ)
    · simp only [cutoff,indicator_of_notMem hx,le_refl]

/-- A compact cutoff belongs to the actual finite-energy variational domain.
Use: invokes sharp_young on approximations without weakening its input type.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def cutoffDensity {m : ℝ → ℝ} (hm : Measurable m) (hn : ∀ x, 0 ≤ m x)
    (hE : Integrable (fun x => m x^(3/2 : ℝ))) (n : ℕ) : Density where
  value := cutoff m n
  measurable := cutoff_measurable hm n
  nonneg := cutoff_nonneg hn n
  integrable := cutoff_integrable hm hn n
  energy_integrable := by
    apply hE.mono' ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3/2)).measurable.comp
      (cutoff_measurable hm n)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      change ‖cutoff m n x^(3/2 : ℝ)‖ ≤ m x^(3/2 : ℝ)
      rw [Real.norm_eq_abs,abs_of_nonneg (rpow_nonneg (cutoff_nonneg hn n x) _)]
      exact rpow_le_rpow (cutoff_nonneg hn n x) (cutoff_le hn n x) (by norm_num)

/-- The cutoff agrees eventually with the original density at each fixed point.
Use: the product-space Fatou limit is the original literal double integrand.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: choose n larger than both the spatial radius and the finite value m(x). -/
theorem cutoff_eventually_eq (m : ℝ → ℝ) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, cutoff m n x=m x := by
  -- One index simultaneously removes the amplitude clipping and the spatial truncation.
  obtain ⟨N,hN⟩ := exists_nat_gt (max |x| (m x))
  apply eventually_atTop.mpr
  refine ⟨N,fun n hn => ?_⟩
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hx : |x| ≤ (n+1 : ℝ) := by linarith [le_max_left |x| (m x)]
  have hm : m x ≤ (n+1 : ℝ) := by linarith [le_max_right |x| (m x)]
  have hxi : x ∈ Icc (-(n+1 : ℝ)) (n+1 : ℝ) := abs_le.mp hx
  rw [cutoff,indicator_of_mem hxi,min_eq_left hm]

/-- The cutoff converges pointwise to the original measurable density.
Use: continuity of multiplication and ofReal identifies the Fatou integrand limit.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: eventual equality implies convergence to the same constant. -/
theorem cutoff_limit (m : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun n => cutoff m n x) atTop (𝓝 (m x)) := by
  have he : (fun n => cutoff m n x) =ᶠ[atTop] (fun _ => m x) := cutoff_eventually_eq m x
  exact tendsto_const_nhds.congr' he.symm

/-- Sharp Young in the complete scope of the article, including infinite total mass.
Use: verifies the stated theorem for every measurable nonnegative L^(3/2) density.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: each compact cutoff satisfies the proved sharp spectral inequality and has
energy at most the original energy; product-space Fatou removes both cutoffs. -/
theorem sharp_young_general {m : ℝ → ℝ} (hm : Measurable m) (hn : ∀ x, 0 ≤ m x)
    (hE : Integrable (fun x => m x^(3/2 : ℝ))) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (m z.1*m z.2*exp (-2*|z.1-z.2|)) ∂volume.prod volume) ≤
      ENNReal.ofReal ((5/18 : ℝ)^(1/3 : ℝ)*(∫ x, m x^(3/2 : ℝ))^(4/3 : ℝ)) := by
  -- Finite-mass spectral moments are exactly the extended product integrals of the cutoffs.
  let b (n : ℕ) := cutoffDensity hm hn hE n
  let C := (5/18 : ℝ)^(1/3 : ℝ)*(∫ x, m x^(3/2 : ℝ))^(4/3 : ℝ)
  let F (n : ℕ) (z : ℝ × ℝ) := ENNReal.ofReal ((b n).value z.1*(b n).value z.2*exp (-2*|z.1-z.2|))
  have hbound (n : ℕ) : (∫⁻ z, F n z ∂volume.prod volume) ≤ ENNReal.ofReal C := by
    have he : (b n).energy ≤ ∫ x, m x^(3/2 : ℝ) := integral_mono (b n).energy_integrable hE
      (fun x => rpow_le_rpow ((b n).nonneg x) (cutoff_le hn n x) (by norm_num))
    have hg : observe (b n) .second ≤ C := (sharp_young (b n)).trans
      (mul_le_mul_of_nonneg_left (rpow_le_rpow (b n).energy_nonneg he (by norm_num)) (by positivity))
    have hi := second_integrand_integrable (b n).integrable (b n).integrable (b n).measurable (b n).measurable
    have hpos : ∀ z : ℝ × ℝ, 0 ≤ (b n).value z.1*(b n).value z.2*exp (-2*|z.1-z.2|) :=
      fun z => mul_nonneg (mul_nonneg ((b n).nonneg z.1) ((b n).nonneg z.2)) (exp_pos _).le
    have hid := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hpos)
    change ENNReal.ofReal (secondPairing (b n).value (b n).value)=∫⁻ z, F n z ∂volume.prod volume at hid
    rw [← hid,(b n).secondPairing_self]
    exact ENNReal.ofReal_le_ofReal hg
  -- Fatou is used before asserting finiteness or defining a real double integral for m.
  have hmeas (n : ℕ) : Measurable (F n) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      ((((b n).measurable.comp measurable_fst).mul ((b n).measurable.comp measurable_snd)).mul
        (by have h : Continuous (fun z : ℝ × ℝ => exp (-2*|z.1-z.2|)) := by fun_prop
            exact h.measurable))
  have hpoint (z : ℝ × ℝ) :
      Tendsto (fun n => F n z) atTop (𝓝 (ENNReal.ofReal (m z.1*m z.2*exp (-2*|z.1-z.2|)))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((cutoff_limit m z.1).mul (cutoff_limit m z.2)).mul_const _)
  have hid : (fun z : ℝ × ℝ => ENNReal.ofReal (m z.1*m z.2*exp (-2*|z.1-z.2|))) =
      fun z => liminf (fun n => F n z) atTop := funext (fun z => (hpoint z).liminf_eq.symm)
  rw [hid]
  exact (lintegral_liminf_le hmeas).trans
    ((liminf_le_liminf (Filter.Eventually.of_forall hbound)).trans_eq (liminf_const _))

end
end jacobi.Young
