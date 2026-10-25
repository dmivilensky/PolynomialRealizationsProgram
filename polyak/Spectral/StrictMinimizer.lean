import polyak.Spectral.FiniteTrig
import polyak.Boundary.Tail
import polyak.Waves.Finite

/-!
Article: Appendix A, strict minimizer slack of finite-support spectra away from t=0.
Use: every optimal spectrum with finite interior support has |C|<ḡ, hence finitely
many active lag constraints. No special classified family is assumed.
Proof: saturation would bound the negative part of a nonzero finite positive-frequency
trigonometric sum by an exponentially vanishing quantity, contradicting its Cesàro moments.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace polyak.Spectral

variable {J : Type*}

/-- Article: unit-frequency character at an interior cosine frequency. -/
def finiteUnitPhase (c : J → Frequency) (j : J) : ℂ := Waves.z 0 (Real.arccos (c j))

/-- Article: coefficients of the oscillation forced by a saturated minimizer constraint. -/
def boundaryCoefficient (w : J → ℝ≥0) (c : J → Frequency) (u δ : ℝ) (j : J) : ℂ :=
  -(w j : ℂ)*(Complex.ofReal (g u (c j))-
    Complex.ofReal (δ*(2*u*Real.sin (Real.arccos (c j))))*Complex.I)

/-- Article: every spectral phase lies on the unit complex circle. -/
theorem finiteUnitPhase_norm (c : J → Frequency) (j : J) : ‖finiteUnitPhase c j‖=1 := by
  have h := Waves.norm_z_pow 0 (Real.arccos (c j)) 1
  simpa [finiteUnitPhase] using h

/-- Article: cosine coordinates are recovered exactly from the unit phase. -/
theorem finiteUnitPhase_re (c : J → Frequency) (j : J) : (finiteUnitPhase c j).re=c j := by
  have h := Waves.z_pow_re 0 (Real.arccos (c j)) 1
  simpa [finiteUnitPhase,Real.cos_arccos (c j).property.1 (c j).property.2] using h

/-- Article: interior frequencies have strictly positive phase imaginary parts. -/
theorem finiteUnitPhase_im_pos (c : J → Frequency)
    (hc : ∀ j,-1 < (c j : ℝ) ∧ (c j : ℝ) < 1) (j : J) : 0 < (finiteUnitPhase c j).im := by
  have h := Waves.z_pow_im 0 (Real.arccos (c j)) 1
  have ha : 0 < Real.arccos (c j) := Real.arccos_pos.mpr (hc j).2
  have hb : Real.arccos (c j) < Real.pi := Real.arccos_lt_pi.mpr (hc j).1
  have he : (finiteUnitPhase c j).im=Real.sin (Real.arccos (c j)) := by simpa [finiteUnitPhase] using h
  rw [he]
  exact Real.sin_pos_of_pos_of_lt_pi ha hb

/-- Article: distinct cosine atoms give distinct positive-frequency characters. -/
theorem finiteUnitPhase_injective (c : J → Frequency) (hc : Function.Injective c) :
    Function.Injective (finiteUnitPhase c) := by
  intro i j hij
  apply hc
  apply Subtype.ext
  simpa only [finiteUnitPhase_re] using congrArg Complex.re hij

variable [Fintype J]

/-- Article: the averaged minimizer slack of a finite spectrum is its actual weighted sum. -/
theorem finite_meanG (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1) (u : ℝ) :
    meanG (Waves.finiteSpectrum w c hw) u=∑ j,(w j : ℝ)*g u (c j) := by
  rw [meanG_eq_integral]
  exact Waves.finiteSpectrum_integral w c hw _

/-- Article: exact finite-spectrum symmetric lag expansion. -/
theorem finite_meanA (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1) (u t : ℝ) (m : ℕ) :
    meanA (Waves.finiteSpectrum w c hw) u t m=
      meanG (Waves.finiteSpectrum w c hw) u*Real.cosh (m*t)-
        ∑ j,(w j : ℝ)*g u (c j)*chebT m (c j) := by
  rw [meanA_eq_integral]
  change (∫ a : Frequency,lagA u t m a ∂Waves.finiteSpectrum w c hw)=_
  rw [Waves.finiteSpectrum_integral,finite_meanG]
  simp_rw [lagA,lagD,mul_sub,← mul_assoc]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul]

/-- Article: exact finite-spectrum skew lag expansion, without sine denominators. -/
theorem finite_meanB (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1) (u : ℝ)
    (m : ℕ) (hm : 1 ≤ m) :
    meanB (Waves.finiteSpectrum w c hw) u m=
      ∑ j,(w j : ℝ)*(2*u*Real.sin (Real.arccos (c j))*Real.sin (m*Real.arccos (c j))) := by
  rw [meanB_eq_integral]
  change (∫ a : Frequency,lagB u m a ∂Waves.finiteSpectrum w c hw)=_
  rw [Waves.finiteSpectrum_integral]
  apply Finset.sum_congr rfl
  intro j _
  rw [Boundary.lagB_trig u m hm]

/-- Article: the saturated signed raw lag is an exponential plus an actual finite oscillation. -/
theorem saturated_lag_identity (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1)
    (u t δ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    meanA (Waves.finiteSpectrum w c hw) u t m-δ*meanB (Waves.finiteSpectrum w c hw) u m-
      meanG (Waves.finiteSpectrum w c hw) u*Real.sinh (m*t) =
      meanG (Waves.finiteSpectrum w c hw) u*Real.exp (-(m*t))+
        FiniteTrig.oscillation (finiteUnitPhase c) (boundaryCoefficient w c u δ) m := by
  rw [finite_meanA,finite_meanB w c hw u m hm]
  have hphase (j : J) :
      (boundaryCoefficient w c u δ j*finiteUnitPhase c j^m).re=
        -((w j : ℝ)*g u (c j)*chebT m (c j))-
        δ*((w j : ℝ)*(2*u*Real.sin (Real.arccos (c j))*Real.sin (m*Real.arccos (c j)))) := by
    simp only [boundaryCoefficient,finiteUnitPhase,Complex.mul_re,Complex.mul_im,Complex.neg_re,
      Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_re,Complex.sub_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub,sub_zero,
      Waves.z_pow_re,Waves.z_pow_im,mul_zero,Real.exp_zero,one_mul]
    rw [Waves.chebT_arccos]
    norm_cast
    ring
  unfold FiniteTrig.oscillation
  rw [Complex.re_sum]
  simp_rw [hphase]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_neg_distrib]
  have he := Real.cosh_sub_sinh (m*t)
  rw [← he]
  ring

omit [Fintype J] in
/-- Article: a positive-weight interior atom always contributes a nonzero oscillatory coefficient.
Proof: the sharp amplitude identity is strictly positive at an interior frequency. -/
theorem boundaryCoefficient_ne_zero (w : J → ℝ≥0) (c : J → Frequency) (u δ : ℝ)
    (hδ : δ=1 ∨ δ= -1) (j : J) (hwj : 0 < w j)
    (hcj : -1 < (c j : ℝ) ∧ (c j : ℝ) < 1) : boundaryCoefficient w c u δ j ≠ 0 := by
  have hk : 0 < 1-(c j : ℝ)^2 := by
    have hh := (sq_lt_one_iff_abs_lt_one (c j : ℝ)).mpr (abs_lt.mpr hcj)
    linarith
  let M : ℂ := Complex.ofReal (g u (c j))-
    Complex.ofReal (δ*(2*u*Real.sin (Real.arccos (c j))))*Complex.I
  have hn : Complex.normSq M=(1-(c j : ℝ)^2+u^2)^2 := by
    have ha := Boundary.amplitude_identity u (c j)
    have hd : δ^2=1 := by rcases hδ with rfl | rfl <;> norm_num
    dsimp [M]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      sub_zero,zero_sub]
    nlinarith [ha,hd]
  have hM : M ≠ 0 := by
    intro h
    rw [h,Complex.normSq_zero] at hn
    have hR : 0 < 1-(c j : ℝ)^2+u^2 := by nlinarith [sq_nonneg u]
    nlinarith [sq_pos_of_pos hR]
  have hwc : (w j : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hwj)
  exact mul_ne_zero (neg_ne_zero.mpr hwc) hM

/-- Article: a probability spectrum has at least one strictly positive atom weight. -/
theorem exists_positive_weight (w : J → ℝ≥0) (hw : ∑ j,w j=1) : ∃ j,0 < w j := by
  classical
  by_contra hn
  push Not at hn
  have hzero : ∀ j,w j=0 := fun j => le_antisymm (hn j) zero_le
  simp_rw [hzero] at hw
  norm_num at hw

/-- Article: no finite interior spectrum can saturate the minimizer inequality at a positive exponent. -/
theorem finite_strict_minimizer_pos (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1)
    (hci : Function.Injective c) (hc : ∀ j,-1 < (c j : ℝ) ∧ (c j : ℝ) < 1)
    {u C t : ℝ} (ht : 0 < t) (h : FeasibleU u t (Waves.finiteSpectrum w c hw) C) :
    |C| < meanG (Waves.finiteSpectrum w c hw) u := by
  by_contra hnot
  let H := meanG (Waves.finiteSpectrum w c hw) u
  have hH : 0 ≤ H := (abs_nonneg C).trans h.1
  have heq : |C|=H := le_antisymm h.1 (le_of_not_gt hnot)
  have hboundary : ∃ δ : ℝ, (δ=1 ∨ δ= -1) ∧ ∀ m : ℕ,1 ≤ m →
      0 ≤ meanA (Waves.finiteSpectrum w c hw) u t m-
        δ*meanB (Waves.finiteSpectrum w c hw) u m-H*Real.sinh (m*t) := by
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
  obtain ⟨j,hj⟩ := exists_positive_weight w hw
  have ha : ∃ j,boundaryCoefficient w c u δ j ≠ 0 :=
    ⟨j,boundaryCoefficient_ne_zero w c u δ hδ j hj (hc j)⟩
  apply FiniteTrig.not_exponential_lower_bound (finiteUnitPhase c) (boundaryCoefficient w c u δ)
    (finiteUnitPhase_norm c) (finiteUnitPhase_im_pos c hc) (finiteUnitPhase_injective c hci)
    ha H t hH ht
  intro m hm
  have hh := hraw m hm
  rw [saturated_lag_identity w c hw u t δ m hm] at hh
  change 0 ≤ H*Real.exp (-(m*t))+FiniteTrig.oscillation (finiteUnitPhase c) (boundaryCoefficient w c u δ) m at hh
  linarith

/-- Article: strict minimizer slack for every finite interior feasible spectrum and every t≠0. -/
theorem finite_strict_minimizer (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1)
    (hci : Function.Injective c) (hc : ∀ j,-1 < (c j : ℝ) ∧ (c j : ℝ) < 1)
    {u C t : ℝ} (ht : t ≠ 0) (h : FeasibleU u t (Waves.finiteSpectrum w c hw) C) :
    |C| < meanG (Waves.finiteSpectrum w c hw) u := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hneg := (feasibleU_neg_t_iff u t C (Waves.finiteSpectrum w c hw)).mpr h
    simpa only [abs_neg] using finite_strict_minimizer_pos w c hw hci hc (neg_pos.mpr ht) hneg
  · exact finite_strict_minimizer_pos w c hw hci hc ht h

/-- Article: the same strict minimizer inequality in the original twist coordinate v. -/
theorem finite_feasible_strict_minimizer (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1)
    (hci : Function.Injective c) (hc : ∀ j,-1 < (c j : ℝ) ∧ (c j : ℝ) < 1)
    {v C t : ℝ} (ht : t ≠ 0) (h : Feasible v t (Waves.finiteSpectrum w c hw) C) :
    |C| < meanG (Waves.finiteSpectrum w c hw) (Real.sinh v) :=
  finite_strict_minimizer w c hw hci hc ht h

/-- Article: only finitely many lag constraints can be active for a finite interior feasible spectrum.
Proof: the strict minimizer theorem supplies the positive coefficient in the sharp analytic tail bound. -/
theorem finite_active_lags_bounded (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j,w j=1)
    (hci : Function.Injective c) (hc : ∀ j,-1 < (c j : ℝ) ∧ (c j : ℝ) < 1)
    {u C t : ℝ} (ht : t ≠ 0) (h : FeasibleU u t (Waves.finiteSpectrum w c hw) C) :
    ∃ N : ℕ, ∀ m : ℕ,N ≤ m →
      0 < meanA (Waves.finiteSpectrum w c hw) u t m-meanB (Waves.finiteSpectrum w c hw) u m+
        C*Real.sinh (m*t) ∧
      0 < meanA (Waves.finiteSpectrum w c hw) u t m+meanB (Waves.finiteSpectrum w c hw) u m-
        C*Real.sinh (m*t) := by
  have hstrict := finite_strict_minimizer w c hw hci hc ht h
  exact Filter.eventually_atTop.mp (Boundary.eventually_raw_lags_positive
    (Waves.finiteSpectrum w c hw) u C t hstrict ht)

end polyak.Spectral
