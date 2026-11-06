import nesterov.Spectral.Finite
import polyak.Spectral.FiniteTrig
import polyak.Spectral.StrictMinimizer

/-!
Article: Appendix A, strict minimizer slack of finite-support spectra away from t=0.
Use: every optimal spectrum with finite interior support has |C|<ḡ, hence finitely
many active lag constraints. No special classified family is assumed.
Proof: saturation would bound the negative part of a nonzero finite positive-frequency
trigonometric sum by an exponentially vanishing quantity, contradicting its Cesàro moments.
-/

noncomputable section
open MeasureTheory
open nesterov.Spectral
open scoped BigOperators NNReal
namespace nesterov.Attainment

variable {J : Type*}

abbrev finiteUnitPhase := @polyak.Spectral.finiteUnitPhase
abbrev finiteUnitPhase_norm := @polyak.Spectral.finiteUnitPhase_norm
abbrev finiteUnitPhase_im_pos := @polyak.Spectral.finiteUnitPhase_im_pos
abbrev finiteUnitPhase_injective := @polyak.Spectral.finiteUnitPhase_injective

def boundaryCoefficient (w : J → ℝ≥0) (c : J → Frequency) (a : SymbolPair)
    (δ : ℝ) (j : J) : ℂ :=
  -(w j : ℂ) * (Complex.ofReal (g a (c j)) -
    Complex.ofReal (δ * (2 * skew a (c j))) * Complex.I)

variable [Fintype J]

/-- Article: the averaged minimizer slack of a finite spectrum is its actual weighted sum. -/
theorem finite_meanG (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1) (u : SymbolPair) :
    meanG (finiteSpectrum w c hw) u=∑ j,(w j : ℝ)*g u (c j) := by
  exact polyak.Waves.finiteSpectrum_integral w c hw _

/-- Article: exact finite-spectrum symmetric lag expansion. -/
theorem finite_meanA (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1) (u : SymbolPair) (t : ℝ) (m : ℕ) :
    meanA (finiteSpectrum w c hw) u t m=
      meanG (finiteSpectrum w c hw) u*Real.cosh (m*t)-
        ∑ j,(w j : ℝ)*g u (c j)*Real.cos (m*Real.arccos (c j)) := by
  change (∫ a : Frequency,lagA u t m a ∂finiteSpectrum w c hw)=_
  rw [polyak.Waves.finiteSpectrum_integral,finite_meanG]
  simp_rw [lagA,mul_sub,← mul_assoc]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul]

theorem finite_meanB (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1)
    (u : SymbolPair) (m : ℕ) :
    meanB (finiteSpectrum w c hw) u m =
      ∑ j,(w j : ℝ)*(2*skew u (c j)*Real.sin (m*Real.arccos (c j))) :=
  polyak.Waves.finiteSpectrum_integral w c hw _

/-- Article: the saturated signed raw lag is an exponential plus an actual finite oscillation. -/
theorem saturated_lag_identity (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1)
    (u : SymbolPair) (t δ : ℝ) (m : ℕ) :
    meanA (finiteSpectrum w c hw) u t m-δ*meanB (finiteSpectrum w c hw) u m-
      meanG (finiteSpectrum w c hw) u*Real.sinh (m*t) =
      meanG (finiteSpectrum w c hw) u*Real.exp (-(m*t))+
        polyak.Spectral.FiniteTrig.oscillation (finiteUnitPhase c) (boundaryCoefficient w c u δ) m := by
  rw [finite_meanA,finite_meanB w c hw u m]
  have hphase (j : J) :
      (boundaryCoefficient w c u δ j*finiteUnitPhase c j^m).re=
        -((w j : ℝ)*g u (c j)*Real.cos (m*Real.arccos (c j)))-
        δ*((w j : ℝ)*(2*skew u (c j)*Real.sin (m*Real.arccos (c j)))) := by
    simp only [boundaryCoefficient,finiteUnitPhase,polyak.Spectral.finiteUnitPhase,Complex.mul_re,Complex.mul_im,Complex.neg_re,
      Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_re,Complex.sub_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub,sub_zero,
      polyak.Waves.z_pow_re,polyak.Waves.z_pow_im,mul_zero,Real.exp_zero,one_mul]
    norm_cast
    ring
  unfold polyak.Spectral.FiniteTrig.oscillation
  rw [Complex.re_sum]
  simp_rw [hphase]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_neg_distrib]
  have he := Real.cosh_sub_sinh (m*t)
  rw [← he]
  ring

omit [Fintype J] in
theorem boundaryCoefficient_ne_zero (w : J → ℝ≥0) (c : J → Frequency)
    (u : SymbolPair) (δ : ℝ) (hδ : δ=1 ∨ δ= -1) (j : J) (hwj : 0 < w j)
    (hgs : g u (c j) ≠ 0 ∨ skew u (c j) ≠ 0) : boundaryCoefficient w c u δ j ≠ 0 := by
  have hwc : (w j : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hwj)
  apply mul_ne_zero (neg_ne_zero.mpr hwc)
  intro he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.zero_re, Complex.zero_im] at hr hi
  rcases hgs with hg | hs
  · apply hg; linarith
  · apply hs
    rcases hδ with rfl | rfl <;> linarith

/-- Article: no finite interior spectrum can saturate the minimizer inequality at a positive exponent. -/
theorem finite_strict_minimizer_pos (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1)
    (hci : Function.Injective c) (hc : ∀ j,-1 < (c j : ℝ) ∧ (c j : ℝ) < 1)
    {u : SymbolPair} {C t : ℝ} (hgs : ∀ j, g u (c j) ≠ 0 ∨ skew u (c j) ≠ 0) (ht : 0 < t) (h : Feasible u t (finiteSpectrum w c hw) C) :
    |C| < meanG (finiteSpectrum w c hw) u := by
  by_contra hnot
  let H := meanG (finiteSpectrum w c hw) u
  have hH : 0 ≤ H := (abs_nonneg C).trans h.1
  have heq : |C|=H := le_antisymm h.1 (le_of_not_gt hnot)
  have hboundary : ∃ δ : ℝ, (δ=1 ∨ δ= -1) ∧ ∀ m : ℕ,1 ≤ m →
      0 ≤ meanA (finiteSpectrum w c hw) u t m-
        δ*meanB (finiteSpectrum w c hw) u m-H*Real.sinh (m*t) := by
    rcases le_total 0 C with hC | hC
    · have hCH : C=H := by rwa [abs_of_nonneg hC] at heq
      refine ⟨-1,Or.inr rfl,fun m hm => ?_⟩
      have hh := (h.2 m hm).2
      rw [hCH] at hh
      simpa only [neg_one_mul,sub_neg_eq_add] using hh
    · have hCH : C= -H := by rw [abs_of_nonpos hC] at heq; linarith
      refine ⟨1,Or.inl rfl,fun m hm => ?_⟩
      have hh := (h.2 m hm).1
      rw [hCH] at hh
      simpa only [one_mul,neg_mul,sub_eq_add_neg] using hh
  obtain ⟨δ,hδ,hraw⟩ := hboundary
  obtain ⟨j,hj⟩ := polyak.Spectral.exists_positive_weight w hw
  have ha : ∃ j,boundaryCoefficient w c u δ j ≠ 0 :=
    ⟨j,boundaryCoefficient_ne_zero w c u δ hδ j hj (hgs j)⟩
  apply polyak.Spectral.FiniteTrig.not_exponential_lower_bound (finiteUnitPhase c) (boundaryCoefficient w c u δ)
    (finiteUnitPhase_norm c) (finiteUnitPhase_im_pos c hc) (finiteUnitPhase_injective c hci)
    ha H t hH ht
  intro m hm
  have hh := hraw m hm
  rw [saturated_lag_identity w c hw u t δ m] at hh
  change 0 ≤ H*Real.exp (-(m*t))+polyak.Spectral.FiniteTrig.oscillation (finiteUnitPhase c) (boundaryCoefficient w c u δ) m at hh
  linarith

/-- Article: strict minimizer slack for every finite interior feasible spectrum and every t≠0. -/
theorem finite_strict_minimizer (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1)
    (hci : Function.Injective c) (hc : ∀ j,-1 < (c j : ℝ) ∧ (c j : ℝ) < 1)
    {u : SymbolPair} {C t : ℝ} (hgs : ∀ j, g u (c j) ≠ 0 ∨ skew u (c j) ≠ 0) (ht : t ≠ 0) (h : Feasible u t (finiteSpectrum w c hw) C) :
    |C| < meanG (finiteSpectrum w c hw) u := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hneg := (nesterov.Spectral.feasible_neg_t_iff u t C (finiteSpectrum w c hw)).mpr h
    simpa only [abs_neg] using finite_strict_minimizer_pos w c hw hci hc hgs (neg_pos.mpr ht) hneg
  · exact finite_strict_minimizer_pos w c hw hci hc hgs ht h

end nesterov.Attainment
