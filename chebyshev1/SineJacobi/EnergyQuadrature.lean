import chebyshev1.SineJacobi.GradedEnergy
import chebyshev1.Analysis.Simpson
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: chebyshev1, Theorem 5.2.
The composite rule excludes the singular endpoint panel.
Use: `chebyshev1.SineJacobi.sineEnergy_quadrature_error` feeds
`chebyshev1.SineJacobi.sineEnergy_decimal` (A decimal enclosure of the actual elliptic-profile
integral in Theorem 5.2).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_decimal` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set Filter Topology MeasureTheory chebyshev1.Analysis
set_option backward.isDefEq.respectTransparency false

/--
The precise assertion is `IntervalIntegrable energyDensity volume 0 1`.

Use: `chebyshev1.SineJacobi.sineEnergy_eq_graded` uses this assertion to establish exact
identity `sineEnergy = ∫ s in (0:ℝ)..1, gradedEnergy s`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
private theorem energyDensity_integrable : IntervalIntegrable energyDensity volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)]
  change Integrable energyDensity (volume.restrict (Ioo (0:ℝ) 1))
  convert (sineDensity_memLp 2).integrable_norm_pow (p := 2) (by norm_num) using 1
  funext t
  simp only [energyDensity, Real.norm_eq_abs, sq_abs]

/--
Exact identity `energyDensity (1-t) = energyDensity t`.

Use: `chebyshev1.SineJacobi.sineEnergy_eq_graded` rewrites with this identity to establish
exact identity `sineEnergy = ∫ s in (0:ℝ)..1, gradedEnergy s`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
private theorem energyDensity_reflection (t : ℝ) : energyDensity (1-t) = energyDensity t := by
  simp only [energyDensity, sineDensity, profileProduct, sub_sub_cancel]
  ring

/--
Exact identity `sineEnergy = ∫ s in (0:ℝ)..1, gradedEnergy s`.

Use: `chebyshev1.SineJacobi.sineEnergy_quadrature_error` rewrites with this identity to
establish the stated quantitative bound `|sineEnergy-energyQuadrature N| ≤
1300000/(3*(N:ℝ)^4)+12/(N:ℝ)^6`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sineEnergy_eq_graded : sineEnergy = ∫ s in (0:ℝ)..1, gradedEnergy s := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hi0 := energyDensity_integrable.mono_set
    (show uIcc (0:ℝ) (1/2) ⊆ uIcc 0 1 by simp only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2),
      uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩)
  have hi1 := energyDensity_integrable.mono_set
    (show uIcc (1/2:ℝ) 1 ⊆ uIcc 0 1 by simp only [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)
  have hsym : (∫ t in (1/2:ℝ)..1, energyDensity t) = ∫ t in (0:ℝ)..1/2, energyDensity t := by
    have hh := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1/2) energyDensity 1
    simp only [energyDensity_reflection] at hh
    norm_num only at hh
    exact hh.symm
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := energyDensity) (a := (0:ℝ)) (b := 1)
    (f := fun s => s^3/2) (f' := fun s => 3*s^2/2)
    (by fun_prop) (fun s _ => by
      convert ((hasDerivAt_id s).pow 3).div_const 2 using 1 <;> simp)
    (fun s _ => by positivity)
  have he : (∫ s in (0:ℝ)..1, gradedEnergy s) = 2*(∫ t in (0:ℝ)..1/2, energyDensity t) := by
    have hg : gradedEnergy = fun s => 2*((energyDensity ∘ (fun s => s^3/2)) s*(3*s^2/2)) := by
      funext s; dsimp [gradedEnergy]; ring
    rw [hg, intervalIntegral.integral_const_mul, hsub]
    norm_num
  change (∫ t in (0:ℝ)..1, energyDensity t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1, hsym, he]
  ring

/--
An integrable endpoint majorant for the graded integrand.

The stated quantitative bound `0 ≤ gradedEnergy s ∧ gradedEnergy s ≤ 12*s^5`.

Use:
`_private.chebyshev1.SineJacobi.EnergyQuadrature.0.chebyshev1.SineJacobi.gradedEnergy_integrable`
rewrites with this bound to establish `IntervalIntegrable gradedEnergy
volume 0 1`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineDensity_square_bound` with
the arguments shown in the proof.
-/
theorem gradedEnergy_bound {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ gradedEnergy s ∧ gradedEnergy s ≤ 12*s^5 := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.sineDensity_square_bound` with the
  -- arguments shown in the proof.
  have hs3 := pow_le_pow_left₀ hs.le hs1 3
  have ht : s^3/2 ∈ Ioo (0:ℝ) 1 := ⟨by positivity, by nlinarith [hs3]⟩
  have hb := sineDensity_square_bound ht
  have hsin := sin_le (show 0 ≤ Real.pi*(s^3/2) by positivity)
  have hpi := mul_le_mul_of_nonneg_right pi_lt_four.le ht.1.le
  have hu : energyDensity (s^3/2) ≤ 4*s^3 := by
    change sineDensity (s^3/2)^2 ≤ _
    nlinarith [hb, hsin, hpi]
  constructor
  · unfold gradedEnergy energyDensity; positivity
  · have hh := mul_le_mul_of_nonneg_left hu (show 0 ≤ 3*s^2 by positivity)
    simpa only [gradedEnergy] using (hh.trans_eq (by ring))

/--
The precise assertion is `IntervalIntegrable gradedEnergy volume 0 1`.

Use: `chebyshev1.SineJacobi.sineEnergy_quadrature_error` uses this assertion to establish
the stated quantitative bound `|sineEnergy-energyQuadrature N| ≤
1300000/(3*(N:ℝ)^4)+12/(N:ℝ)^6`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
private theorem gradedEnergy_integrable : IntervalIntegrable gradedEnergy volume 0 1 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply IntegrableOn.of_bound (by simp)
    (((gradedEnergy_contDiffOn 0).continuousOn.mono
      (Ioo_subset_Ioo le_rfl (by norm_num : (1:ℝ) ≤ 1.1))).aestronglyMeasurable measurableSet_Ioo) 12
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (gradedEnergy_bound hs.1 hs.2.le).1]
  exact (gradedEnergy_bound hs.1 hs.2.le).2.trans (by
    have hh := pow_le_pow_left₀ hs.1.le hs.2.le 5
    norm_num at hh
    linarith)

/--
The composite rule excludes the singular endpoint panel.

Use: `chebyshev1.SineJacobi.sineEnergy_quadrature_error` rewrites with this definition to
establish the stated quantitative bound `|sineEnergy-energyQuadrature N| ≤
1300000/(3*(N:ℝ)^4)+12/(N:ℝ)^6`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def energyQuadrature (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 N, simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N)

/--
The stated quantitative bound `|sineEnergy-energyQuadrature N| ≤
1300000/(3*(N:ℝ)^4)+12/(N:ℝ)^6`.

Use: `chebyshev1.SineJacobi.sineEnergy_decimal` uses this bound to establish the stated
quantitative bound `(1.14269215:ℝ) < sineEnergy ∧ sineEnergy < (1.14269221:ℝ)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the exact cubic grading of sineEnergy and split off the first panel [0,1/N], which
meets the singular endpoint. Its s^5 majorant gives the N^-6 tail budget. On all remaining
panels, the proved fourth-derivative bound gives a Simpson error of order N^-5 per panel. Sum
at most N such errors, then add the separately controlled endpoint tail to obtain the displayed
N^-4 plus N^-6 bound.
-/
theorem sineEnergy_quadrature_error {N : ℕ} (hN : 2 ≤ N) :
    |sineEnergy-energyQuadrature N| ≤ 1300000/(3*(N:ℝ)^4)+12/(N:ℝ)^6 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hi0 : IntervalIntegrable gradedEnergy volume 0 (1/(N:ℝ)) :=
    gradedEnergy_integrable.mono_set (by
      rw [uIcc_of_le (by positivity), uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      intro s hs; exact ⟨hs.1, hs.2.trans ((div_le_one hNp).mpr hN1)⟩)
  have hi1 : IntervalIntegrable gradedEnergy volume (1/(N:ℝ)) 1 :=
    gradedEnergy_integrable.mono_set (by
      rw [uIcc_of_le ((div_le_one hNp).mpr hN1), uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      intro s hs; exact ⟨(by positivity : (0:ℝ) ≤ 1/(N:ℝ)).trans hs.1, hs.2⟩)
  -- Handle the singular first panel by its integrable majorant, without applying a
  -- fourth-derivative quadrature bound at zero.
  have htail : |∫ s in (0:ℝ)..1/(N:ℝ), gradedEnergy s| ≤ 12/(N:ℝ)^6 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1/(N:ℝ))
      (C := 12/(N:ℝ)^5) (fun s hs => by
        rw [uIoc_of_le (by positivity)] at hs
        rw [Real.norm_eq_abs, abs_of_nonneg (gradedEnergy_bound hs.1 (hs.2.trans ((div_le_one hNp).mpr hN1))).1]
        have hb := (gradedEnergy_bound hs.1 (hs.2.trans ((div_le_one hNp).mpr hN1))).2
        have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1.le hs.2 5) (by norm_num : (0:ℝ) ≤ 12)
        exact hb.trans (by simpa only [div_pow, one_pow, mul_one_div] using hp))
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos (by positivity : (0:ℝ) < 1/(N:ℝ))] at hh
    convert hh using 1; field_simp
  -- Every remaining panel is strictly inside the smooth domain; the uniform fourth-derivative
  -- bound therefore applies on its closed endpoints.
  have hpanel (j : ℕ) (hj : j ∈ Finset.Ico 1 N) :
      |(∫ s in (j:ℝ)/N..(j+1:ℝ)/N, gradedEnergy s)-
        simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N)| ≤ 1300000/(3*(N:ℝ)^5) := by
    have hj' := Finset.mem_Ico.mp hj
    have hab : (j:ℝ)/N < (j+1:ℝ)/N := by exact (div_lt_div_iff_of_pos_right hNp).mpr (by linarith)
    have hsub : Icc ((j:ℝ)/N) ((j+1:ℝ)/N) ⊆ Ioo (0:ℝ) 1.1 := by
      intro s hs
      have hjp : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      have hje : (j+1:ℝ) ≤ N := by exact_mod_cast (show j+1 ≤ N by omega)
      refine ⟨(div_pos hjp hNp).trans_le hs.1, ?_⟩
      have hb := hs.2.trans ((div_le_one hNp).mpr hje)
      linarith
    have hb := simpson_error hab (by norm_num : (0:ℝ) ≤ 1300000)
      ((gradedEnergy_contDiffOn 4).mono hsub) (fun s hs => by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
          ((gradedEnergy_contDiffOn 4).contDiffAt (isOpen_Ioo.mem_nhds (hsub hs))) hs]
        apply gradedEnergy_fourth_bound (hsub hs).1
        exact hs.2.trans ((div_le_one hNp).mpr (by exact_mod_cast (show j+1 ≤ N by omega))))
    convert hb using 1; field_simp; ring
  have hint (j : ℕ) (hj : j ∈ Finset.Ico 1 N) :
      IntervalIntegrable gradedEnergy volume ((j:ℝ)/N) ((j+1:ℝ)/N) := by
    apply gradedEnergy_integrable.mono_set
    have hj' := Finset.mem_Ico.mp hj
    rw [uIcc_of_le (by apply (div_le_div_iff_of_pos_right hNp).mpr; linarith),
      uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro s hs
    refine ⟨(by positivity : (0:ℝ) ≤ (j:ℝ)/N).trans hs.1, ?_⟩
    exact hs.2.trans ((div_le_one hNp).mpr (by exact_mod_cast (show j+1 ≤ N by omega)))
  -- The adjacency formula reassembles the regular panels into the integral from 1/N to 1.
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun j => (j:ℝ)/N)
    (m := 1) (n := N) (by omega) (fun j hj => by simpa only [Nat.cast_add, Nat.cast_one] using hint j (Finset.mem_Ico.mpr hj))
  simp only [Nat.cast_one, div_self hNp.ne'] at hsum
  -- The sum has N-1 panels. Replacing that count by N turns the per-panel N^-5 budget into the
  -- stated N^-4 budget.
  have herr : |(∫ s in 1/(N:ℝ)..1, gradedEnergy s)-energyQuadrature N| ≤
      1300000/(3*(N:ℝ)^4) := by
    rw [← hsum, energyQuadrature, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simp only [Nat.cast_add, Nat.cast_one]
    apply (Finset.sum_le_sum hpanel).trans
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hcard : ((N-1:ℕ):ℝ) ≤ N := by exact_mod_cast (Nat.sub_le N 1)
    have hh := mul_le_mul_of_nonneg_right hcard (by positivity : (0:ℝ) ≤ 1300000/(3*(N:ℝ)^5))
    convert hh using 1; field_simp
  -- Combine the regular-panel error with the separately bounded singular tail by the triangle
  -- inequality.
  rw [sineEnergy_eq_graded, ← intervalIntegral.integral_add_adjacent_intervals hi0 hi1]
  have he : (∫ s in (0:ℝ)..1/(N:ℝ), gradedEnergy s)+
      (∫ s in 1/(N:ℝ)..1, gradedEnergy s)-energyQuadrature N =
      (∫ s in (0:ℝ)..1/(N:ℝ), gradedEnergy s)+
      ((∫ s in 1/(N:ℝ)..1, gradedEnergy s)-energyQuadrature N) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith [htail, herr])

end
end chebyshev1.SineJacobi
