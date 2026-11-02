import krylov.Strings.GeneralSpectralWeylLower

/-!
Article: main_krylov, apC:prop:tauber, actual Weyl variational bounds.
Use: relate the genuine boundary compliance to sharp local trace estimates
and actual compactly supported trials.  The weak solution is the one
constructed by the CFC resolvent, not an assumed minimizer.
Source: the proved weak equation and Hilbert-space Cauchy--Schwarz.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- The genuine parameter-t mass-plus-gradient energy of a physical pair. -/
def parameterEnergy (S : StringMeasure) (t : ℝ) (w : EnergyAmbient S.measure) : ℝ :=
  t * ‖w.fst‖ ^ 2 + ‖w.snd‖ ^ 2

/-- Physical positive-parameter energy is nonnegative for every pair. -/
theorem parameterEnergy_nonneg (S : StringMeasure) {t : ℝ} (ht : 0 ≤ t)
    (w : EnergyAmbient S.measure) : 0 ≤ parameterEnergy S t w :=
  add_nonneg (mul_nonneg ht (sq_nonneg _)) (sq_nonneg _)

/-- Testing the actual Neumann equation against its actual solution gives
its energy as the boundary compliance, including reality of the trace. -/
theorem parameter_solution_energy (S : StringMeasure) (t : ℝ) (ht : 0 < t) :
    parameterEnergy S t (parameterEnergySolution S t ht (boundaryVector S)) =
      boundaryCompliance S t ht := by
  let w := parameterEnergySolution S t ht (boundaryVector S)
  have hh := parameterEnergySolution_variational S t ht (boundaryVector S)
    (parameterEnergySolution_mem S t ht (boundaryVector S))
  have hf : w.fst = parameterResolvent S t ht (boundaryVector S) :=
    parameterEnergySolution_fst S t ht (boundaryVector S)
  have hm : inner ℂ w.fst w.fst = ((‖w.fst‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hg : inner ℂ w.snd w.snd = ((‖w.snd‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [← hf] at hh
  change (t : ℂ) * inner ℂ w.fst w.fst + inner ℂ w.snd w.snd =
    inner ℂ (boundaryVector S) w.fst at hh
  rw [hm, hg] at hh
  have hr := congrArg Complex.re hh
  change parameterEnergy S t w = (inner ℂ (boundaryVector S)
    (parameterResolvent S t ht (boundaryVector S))).re
  rw [← hf]
  simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, parameterEnergy] using hr

/-- The actual physical boundary trace of the Neumann solution is the
real compliance, not just a complex number with the same real part. -/
theorem parameter_solution_trace (S : StringMeasure) (t : ℝ) (ht : 0 < t) :
    boundaryTrace S (parameterEnergySolution S t ht (boundaryVector S)).fst =
      (boundaryCompliance S t ht : ℂ) := by
  let w := parameterEnergySolution S t ht (boundaryVector S)
  have hh := parameterEnergySolution_variational S t ht (boundaryVector S)
    (parameterEnergySolution_mem S t ht (boundaryVector S))
  have hf : w.fst = parameterResolvent S t ht (boundaryVector S) :=
    parameterEnergySolution_fst S t ht (boundaryVector S)
  rw [← hf] at hh
  change (t : ℂ) * inner ℂ w.fst w.fst + inner ℂ w.snd w.snd =
    inner ℂ (boundaryVector S) w.fst at hh
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_pow] at hh
  change boundaryTrace S w.fst = _
  change _ = boundaryTrace S w.fst at hh
  rw [← parameter_solution_energy S t ht]
  apply hh.symm.trans
  change (t : ℂ) * RCLike.ofReal (‖w.fst‖ ^ 2) + RCLike.ofReal (‖w.snd‖ ^ 2) = _
  simp only [parameterEnergy, Complex.ofReal_add, Complex.ofReal_mul]
  rfl

/-- The constructed physical compliance is nonnegative. -/
theorem boundaryCompliance_nonneg (S : StringMeasure) (t : ℝ) (ht : 0 < t) :
    0 ≤ boundaryCompliance S t ht := by
  rw [← parameter_solution_energy]
  exact parameterEnergy_nonneg S ht.le _

/-- Any actual uniform trace estimate bounds the constructed compliance
from above.  The conclusion follows from testing the true weak solution. -/
theorem boundaryCompliance_le_of_trace (S : StringMeasure) (t : ℝ) (ht : 0 < t)
    {C : ℝ} (hC : 0 < C)
    (htrace : ∀ w ∈ energyGraph S, C * ‖boundaryTrace S w.fst‖ ^ 2 ≤ parameterEnergy S t w) :
    boundaryCompliance S t ht ≤ 1 / C := by
  let h := boundaryCompliance S t ht
  change h ≤ 1 / C
  have h0 : 0 ≤ h := boundaryCompliance_nonneg S t ht
  have hh := htrace _ (parameterEnergySolution_mem S t ht (boundaryVector S))
  rw [parameter_solution_trace, parameter_solution_energy] at hh
  change C * ‖(h : ℂ)‖ ^ 2 ≤ h at hh
  rw [Complex.norm_real, Real.norm_of_nonneg h0] at hh
  by_cases hz : h = 0
  · exact hz ▸ (div_nonneg zero_le_one hC.le)
  · have hp : 0 < h := lt_of_le_of_ne h0 (Ne.symm hz)
    apply (le_div_iff₀ hC).mpr
    have he : (h * C) * h ≤ 1 * h := by nlinarith [hh]
    exact (mul_le_mul_iff_of_pos_right hp).mp he

/-- Local lower density gives the actual upper compliance comparison,
with no assumption on the distant physical mass. -/
theorem boundaryCompliance_le_local (S : StringMeasure) {δ ρ t k : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (ht : 0 < t) (hk : 0 ≤ k)
    (hf : S.measure (Icc 0 δ) ≠ ⊤)
    (hlower : ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ) ≤ S.measure.restrict (Ioc 0 δ))
    (hkbound : k ^ 2 + k / δ ≤ t * ρ) :
    boundaryCompliance S t ht ≤ 1 / (t + k) := by
  apply boundaryCompliance_le_of_trace S t ht (add_pos_of_pos_of_nonneg ht hk)
  intro w hw
  exact energyGraph_trace_lower S hδ hρ ht.le hk hf hlower hkbound hw

private def weightedEnergyVector (S : StringMeasure) (t : ℝ) (w : EnergyAmbient S.measure) :
    EnergyAmbient S.measure := WithLp.toLp 2 (((Real.sqrt t : ℂ) • w.fst), w.snd)

private theorem weightedEnergyVector_norm_sq (S : StringMeasure) {t : ℝ} (ht : 0 ≤ t)
    (w : EnergyAmbient S.measure) : ‖weightedEnergyVector S t w‖ ^ 2 = parameterEnergy S t w := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(Real.sqrt t : ℂ) • w.fst‖ ^ 2 + ‖w.snd‖ ^ 2 = _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t),
    mul_pow, Real.sq_sqrt ht]
  rfl

private theorem weightedEnergyVector_inner (S : StringMeasure) {t : ℝ} (ht : 0 ≤ t)
    (u w : EnergyAmbient S.measure) :
    inner ℂ (weightedEnergyVector S t u) (weightedEnergyVector S t w) =
      (t : ℂ) * inner ℂ u.fst w.fst + inner ℂ u.snd w.snd := by
  rw [WithLp.prod_inner_apply]
  change inner ℂ ((Real.sqrt t : ℂ) • u.fst) ((Real.sqrt t : ℂ) • w.fst) + _ = _
  rw [inner_smul_left, inner_smul_right]
  have hs : (starRingEnd ℂ) (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
    rw [Complex.conj_ofReal]
    norm_cast
    exact Real.mul_self_sqrt ht
  rw [← mul_assoc, hs]
  rfl

/-- Every actual unit-trace energy trial satisfies the genuine reciprocal
compliance bound by weighted Hilbert-space Cauchy--Schwarz. -/
theorem one_le_compliance_mul_trial (S : StringMeasure) (t : ℝ) (ht : 0 < t)
    {w : EnergyAmbient S.measure} (hw : w ∈ energyGraph S)
    (htrace : boundaryTrace S w.fst = 1) :
    1 ≤ boundaryCompliance S t ht * parameterEnergy S t w := by
  let u := parameterEnergySolution S t ht (boundaryVector S)
  have hf : u.fst = parameterResolvent S t ht (boundaryVector S) :=
    parameterEnergySolution_fst S t ht (boundaryVector S)
  have hv := parameterEnergySolution_variational S t ht (boundaryVector S) hw
  rw [← hf] at hv
  change _ = boundaryTrace S w.fst at hv
  rw [htrace] at hv
  have he : inner ℂ (weightedEnergyVector S t u) (weightedEnergyVector S t w) = 1 := by
    rw [weightedEnergyVector_inner S ht.le]
    exact hv
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (weightedEnergyVector S t u) (weightedEnergyVector S t w)
  rw [he, norm_one] at hcs
  have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hcs
  rw [one_pow, mul_pow, weightedEnergyVector_norm_sq S ht.le,
    weightedEnergyVector_norm_sq S ht.le, parameter_solution_energy] at hsq
  exact hsq

/-- An actual unit-trace trial with a proved energy bound gives the
lower bound on the physical compliance used in Weyl bracketing. -/
theorem le_boundaryCompliance_of_trial (S : StringMeasure) (t : ℝ) (ht : 0 < t)
    {D : ℝ} (hD : 0 < D) {w : EnergyAmbient S.measure}
    (hw : w ∈ energyGraph S) (htrace : boundaryTrace S w.fst = 1)
    (henergy : parameterEnergy S t w ≤ D) :
    1 / D ≤ boundaryCompliance S t ht := by
  apply (div_le_iff₀ hD).mpr
  have hh := one_le_compliance_mul_trial S t ht hw htrace
  have hb := mul_le_mul_of_nonneg_left henergy (boundaryCompliance_nonneg S t ht)
  linarith

end
end krylov.Strings.GeneralSpectral
