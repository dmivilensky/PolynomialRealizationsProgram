import jacobi.Young.SobolevPrimitive
import Mathlib.Topology.Order.Compact

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
The proof applies to actual H1 representatives with a.e. derivatives and local
absolute continuity, reusing the representation proved in chebyshev2.
Square completion and the exact primitive height give the bound at a maximum;
an elementary polynomial identity then optimizes the height. This file proves
the inequality; classification of all equality cases is a separate assertion.
Use: applies to the composition F_a(v) in the sharp Sobolev argument.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Set Filter Real chebyshev2.Sobolev
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A function vanishing at both ends must spend twice its attained height in total variation.
Use: applies to the composition F_a(v) in the sharp Sobolev argument.
Article: jacobi, Section 3.2 (sharp Young inequality).
Source: the fundamental theorem for absolutely continuous functions.
Proof: pass the interval FTC to both infinite endpoints, bound each signed
half-line integral by its absolute integral, and add the two halves. -/
theorem total_variation_height {F D : ℝ → ℝ}
    (hac : ∀ a b, AbsolutelyContinuousOnInterval F a b)
    (hd : ∀ᵐ x, HasDerivAt F (D x) x) (hi : Integrable D)
    (ht : Tendsto F atTop (𝓝 0)) (hb : Tendsto F atBot (𝓝 0)) (b : ℝ) :
    2*|F b| ≤ ∫ x, |D x| := by
  -- Both signed half-line integrals are fixed by the same absolutely continuous representative.
  have hl : (∫ x in Iic b, D x)=F b := by
    have h := intervalIntegral_tendsto_integral_Iic b hi.integrableOn tendsto_id
    have h' : Tendsto (fun x => ∫ t in x..b, D t) atBot (𝓝 (F b)) := by
      simpa only [locallyAC_integral_eq_sub hac hd,sub_zero] using hb.const_sub (F b)
    exact tendsto_nhds_unique h h'
  have hr : (∫ x in Ioi b, D x) = -F b := by
    have h := intervalIntegral_tendsto_integral_Ioi b hi.integrableOn tendsto_id
    have h' : Tendsto (fun x => ∫ t in b..x, D t) atTop (𝓝 (-F b)) := by
      simpa only [locallyAC_integral_eq_sub hac hd,zero_sub] using ht.sub_const (F b)
    exact tendsto_nhds_unique h h'
  have h1 := norm_integral_le_integral_norm (μ := volume.restrict (Iic b)) D
  have h2 := norm_integral_le_integral_norm (μ := volume.restrict (Ioi b)) D
  simp only [Real.norm_eq_abs,hl,hr,abs_neg] at h1 h2
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := b) hi.abs.integrableOn hi.abs.integrableOn]
  linarith

/-- A bounded nonnegative H1 representative has an integrable cube.
Use: every term of the sharp Sobolev energy inequality is a genuine finite integral.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: v³≤a v² and the squared representative is integrable by its L2 membership. -/
theorem cube_integrable {f d : ℝ → ℝ} (h : SobolevRegular f d) (hn : ∀ x, 0 ≤ f x)
    {a : ℝ} (ha : ∀ x, f x ≤ a) : Integrable (fun x => f x^3) := by
  apply (h.value_memLp.integrable_sq.const_mul a).mono'
  · exact h.value_memLp.aestronglyMeasurable.pow 3
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hn x) _)]
      nlinarith [mul_le_mul_of_nonneg_right (ha x) (sq_nonneg (f x))]

/-- The exact peak-height inequality for every nonnegative H1 representative.
Use: the analytic core of the sharp Sobolev and sharp Young inequalities.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: compose with the proved Lipschitz primitive, integrate square completion,
and use the total variation spent on both sides of the attained maximum. -/
theorem sobolev_peak_bound {f d : ℝ → ℝ} (h : SobolevRegular f d) (hn : ∀ x, 0 ≤ f x)
    {a b : ℝ} (ha : 0 < a) (hmax : ∀ x, f x ≤ a) (hpeak : f b=a) :
    (4/a)*(∫ x, f x^3)+(32/15 : ℝ)*a^2 ≤ (∫ x, d x^2)+4*(∫ x, f x^2) := by
  -- The primitive composition is locally AC on the entire range, including where f=a.
  let D (x : ℝ) := f x*d x*sqrt (1-f x/a)
  have hr (x : ℝ) : sqrt (1-f x/a) ≤ 1 := sqrt_le_one.mpr (by
    linarith [div_nonneg (hn x) ha.le])
  obtain ⟨u,hu⟩ := (H1.range_iff f).mpr ⟨d,h⟩
  have hfc : Continuous f := hu ▸ H1.continuous_rep u
  have hwc : Continuous (fun x => sqrt (1-f x/a)) := by fun_prop
  have hi : Integrable D := by
    apply (l2_product_integrable h.value_memLp h.derivative_memLp).abs.mono'
    · exact (h.value_memLp.aestronglyMeasurable.mul h.derivative_memLp.aestronglyMeasurable).mul
        hwc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        dsimp only [D]
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sqrt_nonneg _)]
        exact mul_le_of_le_one_right (abs_nonneg _) (hr x)
  have hac (l r : ℝ) : AbsolutelyContinuousOnInterval (wellPrimitive a ∘ f) l r :=
    (wellPrimitive_lipschitz ha).comp_absolutelyContinuousOnInterval
      (fun x _ => ⟨hn x,hmax x⟩) (h.locally_ac l r)
  have hd : ∀ᵐ x, HasDerivAt (wellPrimitive a ∘ f) (D x) x := by
    filter_upwards [h.derivative_ae] with x hx
    convert (wellPrimitive_hasDerivAt ha (f x)).comp x hx using 1
    dsimp [D]
    ring
  have hPc : Continuous (wellPrimitive a) := continuous_iff_continuousAt.mpr
    (fun z => (wellPrimitive_hasDerivAt ha z).continuousAt)
  have h0 : wellPrimitive a 0=0 := wellPrimitive_zero a
  have hv := total_variation_height hac hd hi
    (by simpa only [Function.comp_def,h0] using (hPc.tendsto 0).comp h.tendsto_zero.1)
    (by simpa only [Function.comp_def,h0] using (hPc.tendsto 0).comp h.tendsto_zero.2) b
  have hheight : (wellPrimitive a ∘ f) b=(4/15 : ℝ)*a^2 := by
    rw [Function.comp_apply,hpeak,wellPrimitive_self ha]
  rw [hheight,abs_of_nonneg (by positivity)] at hv
  -- A nonnegative square gives the pointwise energy defect, with its sharp coefficient four.
  have hpoint (x : ℝ) : 4*|D x| ≤ d x^2+4*f x^2-(4/a)*f x^3 := by
    have hf0 := hn x
    have hf1 := hmax x
    have hs : sqrt (1-f x/a)^2 = 1-f x/a := sq_sqrt (by
      rw [sub_nonneg,div_le_iff₀ ha]
      simpa using hf1)
    dsimp only [D]
    rw [abs_mul,abs_mul,abs_of_nonneg (hn x),abs_of_nonneg (sqrt_nonneg _)]
    calc
      _ ≤ d x^2+4*f x^2*sqrt (1-f x/a)^2 := by
        nlinarith [sq_nonneg (|d x|-2*f x*sqrt (1-f x/a)),sq_abs (d x)]
      _ = _ := by rw [hs]; ring
  have hc := cube_integrable h hn hmax
  have hdi := h.derivative_memLp.integrable_sq
  have hfi := h.value_memLp.integrable_sq
  have hb := integral_mono (hi.abs.const_mul 4) ((hdi.add (hfi.const_mul 4)).sub (hc.const_mul (4/a))) hpoint
  have he := integral_sub (hdi.add (hfi.const_mul 4)) (hc.const_mul (4/a))
  have he' := integral_add hdi (hfi.const_mul 4)
  simp only [Pi.sub_apply,Pi.add_apply] at he he' hb
  rw [he,he',integral_const_mul,integral_const_mul] at hb
  rw [integral_const_mul] at hb
  linarith

/-- Exact algebraic optimization of the peak-height bound.
Use: eliminates the attained maximum from the sharp Sobolev inequality.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: put b=(15S/16)^(1/3); the remaining difference is proportional to
(a-b)²(a+2b), which is nonnegative. -/
theorem optimize_peak {S A a : ℝ} (hS : 0 ≤ S) (ha : 0 < a)
    (hb : (4/a)*S+(32/15 : ℝ)*a^2 ≤ A) :
    (32/5 : ℝ)*(15*S/16)^(2/3 : ℝ) ≤ A := by
  -- The cube-root substitution makes the sharp optimization a polynomial identity.
  let b := (15*S/16)^(1/3 : ℝ)
  have hb0 : 0 ≤ b := rpow_nonneg (by positivity) _
  have hb3 : b^3=15*S/16 := by
    dsimp only [b]
    rw [← rpow_natCast,← rpow_mul (by positivity : 0 ≤ 15*S/16)]
    norm_num
  have hb2 : b^2=(15*S/16)^(2/3 : ℝ) := by
    dsimp only [b]
    rw [← rpow_natCast,← rpow_mul (by positivity : 0 ≤ 15*S/16)]
    norm_num
  have hab := mul_le_mul_of_nonneg_left hb ha.le
  have he : a*((4/a)*S+(32/15 : ℝ)*a^2)=4*S+(32/15 : ℝ)*a^3 := by field_simp
  rw [he] at hab
  have hp : 0 ≤ (a-b)^2*(a+2*b) := mul_nonneg (sq_nonneg _) (by positivity)
  have hbound : a*((32/5 : ℝ)*b^2) ≤ a*A := by nlinarith
  rw [← hb2]
  exact (mul_le_mul_iff_of_pos_left ha).mp hbound

/-- The sharp nonnegative Sobolev inequality for actual H1 functions.
Use: the global analytic inequality from which sharp Young and the second-moment
calibration lower bound follow.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: a nonzero continuous H1 representative attains a positive maximum,
because it vanishes at both ends; apply the peak bound and its exact optimization. -/
theorem sharp_sobolev_nonneg {f d : ℝ → ℝ} (h : SobolevRegular f d) (hn : ∀ x, 0 ≤ f x) :
    (32/5 : ℝ)*(15*(∫ x, f x^3)/16)^(2/3 : ℝ) ≤ (∫ x, d x^2)+4*(∫ x, f x^2) := by
  -- The identically zero representative is the only case without a positive peak.
  by_cases hz : ∀ x, f x=0
  · simp only [hz,zero_pow (by decide : 3 ≠ 0),integral_zero,mul_zero,zero_div,
      zero_rpow (by norm_num : (2/3 : ℝ) ≠ 0)]
    positivity
  obtain ⟨z,hz⟩ : ∃ z, 0 < f z := by
    push Not at hz
    obtain ⟨z,hz⟩ := hz
    exact ⟨z,lt_of_le_of_ne (hn z) (Ne.symm hz)⟩
  obtain ⟨u,hu⟩ := (H1.range_iff f).mpr ⟨d,h⟩
  have hc : Continuous f := hu ▸ H1.continuous_rep u
  have ht : Tendsto f (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_sup.mpr ⟨h.tendsto_zero.2,h.tendsto_zero.1⟩
  obtain ⟨b,hb⟩ := hc.exists_forall_ge' z ((ht.eventually (Iio_mem_nhds hz)).mono (fun _ hx => hx.le))
  have hp : 0 < f b := hz.trans_le (hb z)
  exact optimize_peak (integral_nonneg (fun x => pow_nonneg (hn x) _)) hp
    (sobolev_peak_bound h hn hp hb rfl)

end
end jacobi.Young
