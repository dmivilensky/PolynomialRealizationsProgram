import jacobi.Analytic.ReferenceHighFrequency
import jacobi.Reference.FrequencyStrip

/-!
Article: jacobi, Lemma C.1.
The actual reference wave has its full minimum endpoint/frequency
envelope uniformly in complex order. Both the initial and propagated
regions, bounded frequencies and the physical endpoints are included.
Use: completes the full complex-order strip bound including the low-frequency region.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original Gauss core has a common bound at bounded frequency and throughout the physical spatial disk, uniformly in complex order.
Use: completes the full complex-order strip bound including the low-frequency region.
Article: jacobi, Lemma C.1.
Proof: bound both actual numerator parameter norms by the same fixed
positive number and the moving denominator real part by its fixed
positive margin. The proved coefficient comparison gives one summable
Gauss majorant at spatial radius one half. -/
theorem waveCore_low_frequency {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,‖gamma a‖≤G → δ≤(gamma a+1/2).re →
      ‖omega‖≤1 → ∀ x : ℂ,‖x‖≤1/2 → ‖waveCore a omega x‖≤C := by
  -- This is a genuine convergent majorant for the same original reference series.
  let K : ℝ := G+1/Real.pi+1
  have hK : 0<K := by dsimp [K]; positivity
  let M := fun n => ‖ordinaryHypergeometricCoefficient (K:ℂ) (K:ℂ) (δ:ℂ) n‖*(1/2:ℝ)^n
  have hM : Summable M := by
    have hh := jacobi.Reference.Hypergeometric.summable_norm
      (u := (K:ℂ)) (v := (K:ℂ)) (c := (δ:ℂ)) (x := (1/2:ℂ)) (by norm_num)
    convert! hh using 1
    ext n
    simp only [M,norm_mul,norm_pow]
    norm_num
  refine ⟨(∑' n,M n)+1,by
    have hh : 0≤∑' n,M n := tsum_nonneg (fun n => by dsimp [M]; positivity)
    linarith,fun a omega ha hc homega x hx => ?_⟩
  have hd : ‖omega/(Real.pi:ℂ)‖≤1/Real.pi := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right homega Real.pi_pos.le
  have hm : ‖gamma a-omega/(Real.pi:ℂ)‖≤K := by
    have hh := norm_sub_le (gamma a) (omega/(Real.pi:ℂ))
    dsimp [K]
    linarith
  have hp : ‖gamma a+omega/(Real.pi:ℂ)‖≤K := by
    have hh := norm_add_le (gamma a) (omega/(Real.pi:ℂ))
    dsimp [K]
    linarith
  have ht (n : ℕ) : ‖ordinaryHypergeometricCoefficient (gamma a-omega/(Real.pi:ℂ))
      (gamma a+omega/(Real.pi:ℂ)) (gamma a+1/2) n*x^n‖≤M n := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul (jacobi.Reference.Hypergeometric.coefficient_parameters_bound hK hδ hm hp hc n)
      (pow_le_pow_left₀ (norm_nonneg _) hx n) (by positivity) (norm_nonneg _)
  have hs := hM.of_nonneg_of_le (fun _ => norm_nonneg _) ht
  rw [waveCore,ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ht hM).trans (by linarith))

/-- The original complex-order wave has one uniform endpoint-power bound at all bounded frequencies, including zero frequency and the physical endpoint.
Use: supplies the low-frequency region of the full analytic GL reference estimate.
Article: jacobi, Lemma C.1.
Proof: multiply the actual bounded-frequency core bound by the true
sine-power norm bound. At zero the original complex power vanishes
because its exponent has positive real part. -/
theorem wave_low_frequency {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → ‖omega‖≤1 → ∀ t∈Icc (0:ℝ) (1/2),
        ‖wave a omega t‖≤C*t^(gamma a).re := by
  -- The same original normalization is used at both the regular and singular physical points.
  obtain ⟨C,hC,hbound⟩ := waveCore_low_frequency hG hδ
  refine ⟨C,hC,fun a omega hag ha hc homega t ht => ?_⟩
  by_cases ht0 : t=0
  · subst t
    have hg : gamma a≠0 := ne_of_apply_ne Complex.re hag.ne'
    simp only [wave,weight,mul_zero,Real.sin_zero,zero_div,Complex.ofReal_zero,Complex.zero_cpow hg,zero_mul,norm_zero]
    positivity
  · have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    rw [wave,norm_mul]
    exact (mul_le_mul (weight_half_bound hag ⟨htp,ht.2⟩)
      (hbound a omega ha hc homega (coordinate t:ℂ) (coordinate_half_bound ht))
      (norm_nonneg _) (Real.rpow_pos_of_pos htp _).le).trans_eq (by ring)

/-- The actual complex-order wave has its endpoint-power bound with the exact original imaginary-frequency exponential, uniformly over all large frequencies and the whole half interval.
Use: combines with the inverse-frequency estimate to yield the minimum envelope in analytic GL.
Article: jacobi, Lemma C.1.
Proof: before the genuine initial time use the proved actual initial
state. Afterwards the reciprocal frequency is at most 4*pi*t, so its
power is bounded by a constant times the actual endpoint power. The
exponent real part is at most the common order norm bound G. -/
theorem wave_endpoint_high_bound {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → 1≤‖omega‖ → ∀ t∈Icc (0:ℝ) (1/2),
        ‖wave a omega t‖≤C*t^(gamma a).re*Real.exp (t*|omega.im|) := by
  -- The propagated estimate and actual selected branch have one common complex-order constant.
  obtain ⟨A,D,hA,_,hsmall⟩ := wave_small_scale hG hδ
  obtain ⟨B,hB,hlarge⟩ := wave_uniform_high_frequency hG hδ
  let C : ℝ := A+B*(4*Real.pi)^G
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,fun a omega hag ha hc homega t ht => ?_⟩
  have hR : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  by_cases ht0 : t=0
  · subst t
    have hg : gamma a≠0 := ne_of_apply_ne Complex.re hag.ne'
    simp only [wave,weight,mul_zero,Real.sin_zero,zero_div,Complex.ofReal_zero,Complex.zero_cpow hg,zero_mul,norm_zero]
    positivity
  have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htg := Real.rpow_pos_of_pos htp (gamma a).re
  have he : 1≤Real.exp (t*|omega.im|) := Real.one_le_exp (by positivity)
  by_cases hstart : initialTime omega≤t
  · have hinit : 4*Real.pi*initialTime omega=‖omega‖⁻¹ := by
      dsimp [initialTime]
      field_simp [Real.pi_ne_zero,hR.ne']
    have hscale : ‖omega‖⁻¹≤4*Real.pi*t := by
      rw [← hinit]
      exact mul_le_mul_of_nonneg_left hstart (by positivity)
    have hp := Real.rpow_le_rpow (inv_nonneg.mpr hR.le) hscale hag.le
    rw [Real.mul_rpow (by positivity : 0≤4*Real.pi) htp.le,← Real.rpow_neg_eq_inv_rpow] at hp
    have horder : (4*Real.pi)^(gamma a).re≤(4*Real.pi)^G :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [Real.two_le_pi]) ((Complex.re_le_norm _).trans ha)
    have hfinal : ‖omega‖^(-(gamma a).re)≤(4*Real.pi)^G*t^(gamma a).re :=
      hp.trans (mul_le_mul_of_nonneg_right horder htg.le)
    calc
      _ ≤ B*‖omega‖^(-(gamma a).re)*Real.exp (t*|omega.im|) := hlarge a omega hag ha hc homega t ht
      _ ≤ B*((4*Real.pi)^G*t^(gamma a).re)*Real.exp (t*|omega.im|) := by gcongr
      _ = (B*(4*Real.pi)^G)*t^(gamma a).re*Real.exp (t*|omega.im|) := by ring
      _ ≤ C*t^(gamma a).re*Real.exp (t*|omega.im|) := by
        gcongr
        dsimp [C]
        linarith
  · have hinit := initialTime_properties homega
    have hscale := mul_le_mul_of_nonneg_left (le_of_not_ge hstart) (show 0≤Real.pi*‖omega‖ by positivity)
    have hh := (hsmall a omega hag ha hc homega t ⟨htp,ht.2⟩ (by nlinarith [hinit.2])).1
    calc
      _ ≤ A*t^(gamma a).re := hh
      _ ≤ C*t^(gamma a).re := mul_le_mul_of_nonneg_right
        (by dsimp [C]; exact le_add_of_nonneg_right (by positivity) : A≤C) htg.le
      _ ≤ C*t^(gamma a).re*Real.exp (t*|omega.im|) := le_mul_of_one_le_right (by positivity) he

/-- The genuine complex-order reference wave has the full minimum endpoint/frequency envelope at every large frequency, with a common constant on the whole parameter set.
Use: gives the summand amplitude estimate for the actual analytic GL kernel.
Article: jacobi, Lemma C.1.
Proof: increase the two proved actual amplitude constants to their
common sum and choose the smaller of the genuine endpoint and frequency scales. -/
theorem wave_minimum_high_frequency {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → 1≤‖omega‖ → ∀ t∈Icc (0:ℝ) (1/2),
        ‖wave a omega t‖≤C*min (t^(gamma a).re) (‖omega‖^(-(gamma a).re))*Real.exp (t*|omega.im|) := by
  -- Both actual bounds hold for the same solution on the same complete physical half interval.
  obtain ⟨A,hA,hendpoint⟩ := wave_endpoint_high_bound hG hδ
  obtain ⟨B,hB,hfrequency⟩ := wave_uniform_high_frequency hG hδ
  refine ⟨A+B,by positivity,fun a omega hag ha hc homega t ht => ?_⟩
  have htgp := Real.rpow_nonneg ht.1 (gamma a).re
  have hRp := Real.rpow_nonneg (norm_nonneg omega) (-(gamma a).re)
  have hep := (Real.exp_pos (t*|omega.im|)).le
  by_cases h : t^(gamma a).re≤‖omega‖^(-(gamma a).re)
  · rw [min_eq_left h]
    exact (hendpoint a omega hag ha hc homega t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : A≤A+B) htgp) hep)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (hfrequency a omega hag ha hc homega t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : B≤A+B) hRp) hep)

/-- The original reference wave satisfies the complete minimum amplitude bound on every fixed frequency strip, uniformly throughout a bounded complex-order set with positive denominator margin.
Use: supplies the full reference amplitude estimate needed for normal convergence of the original analytic GL kernel and profile series.
Article: jacobi, Lemma C.1.
Proof: at large frequency absorb the proved exact exponential into
exp(b/2). At bounded nonzero frequency the reciprocal scale is at least
one and the actual endpoint scale is at most one, so the endpoint is
the true minimum and the genuine bounded-frequency estimate applies. -/
theorem wave_strip_bound {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) (b : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → omega≠0 → |omega.im|≤b → ∀ t∈Icc (0:ℝ) (1/2),
        ‖wave a omega t‖≤C*min (t^(gamma a).re) (‖omega‖^(-(gamma a).re)) := by
  -- The common order constants apply to every frequency and physical point, including the endpoints.
  obtain ⟨A,hA,hhigh⟩ := wave_minimum_high_frequency hG hδ
  obtain ⟨B,hB,hlow⟩ := wave_low_frequency hG hδ
  let C : ℝ := A*Real.exp (b/2)+B
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,fun a omega hag ha hc hne him t ht => ?_⟩
  have hg : 0≤(gamma a).re := hag.le
  have hmin : 0≤min (t^(gamma a).re) (‖omega‖^(-(gamma a).re)) :=
    le_min (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hR : 1≤‖omega‖
  · have he : Real.exp (t*|omega.im|)≤Real.exp (b/2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul ht.2 him (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
      linarith
    calc
      _ ≤ A*min (t^(gamma a).re) (‖omega‖^(-(gamma a).re))*Real.exp (t*|omega.im|) := hhigh a omega hag ha hc hR t ht
      _ ≤ A*min (t^(gamma a).re) (‖omega‖^(-(gamma a).re))*Real.exp (b/2) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg hA.le hmin)
      _ = (A*Real.exp (b/2))*min (t^(gamma a).re) (‖omega‖^(-(gamma a).re)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hmin
  · have hRp : 0<‖omega‖ := norm_pos_iff.mpr hne
    have hRle : ‖omega‖≤1 := le_of_not_ge hR
    have hrpow : 1≤‖omega‖^(-(gamma a).re) := by
      have hh := Real.rpow_le_rpow_of_nonpos hRp hRle (neg_nonpos.mpr hg)
      simpa only [Real.one_rpow] using hh
    have htone : t^(gamma a).re≤1 := Real.rpow_le_one ht.1 (by linarith [ht.2]) hg
    rw [min_eq_left (htone.trans hrpow)]
    exact (hlow a omega hag ha hc hRle t ht).trans (mul_le_mul_of_nonneg_right
      (show B≤C by dsimp [C]; linarith [mul_pos hA (Real.exp_pos (b/2))]) (Real.rpow_nonneg ht.1 _))

end
end jacobi.ComplexReference
