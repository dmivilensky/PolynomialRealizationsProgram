import jacobi.Hankel.FrequencyDisks
import jacobi.Hankel.FrequencyNormalization
import jacobi.Hankel.SineDiskBounds
import jacobi.Analysis.ZeroDisk

/-!
Article: jacobi, Lemma E.1.
Use: uniform_bessel_zero_disks has one actual rational-comparison constant for all orders and indices, independent of an unproved asymptotic certificate.
-/
namespace jacobi.Hankel
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- The original Bessel quadratic coefficient has a genuine explicit bound on the complex unit order disk.
Use: uniform_bessel_zero_disks has one actual rational-comparison constant for all orders and indices, independent of an unproved asymptotic certificate.
Article: jacobi, Lemma E.1.
Proof: the order norm is at most the norm of the center plus one; apply the original quadratic coefficient formula and the complex norm triangle inequality. -/
theorem besselCoefficient_unit_bound {a a0 : ℂ} (ha : ‖a-a0‖≤1) :
    ‖besselCoefficient a‖≤(‖a0‖+1)^2+1 := by
  have hn : ‖a‖≤‖a0‖+1 := by
    have hh := norm_le_norm_sub_add a a0
    linarith
  apply (norm_sub_le (1/4:ℂ) (a^2)).trans
  change ‖(1/4:ℂ)‖+‖a^2‖≤(‖a0‖+1)^2+1
  rw [norm_pow]
  norm_num
  nlinarith [norm_nonneg a,norm_nonneg a0]

/-- The original grid Fourier normalization has a uniform inverse bound throughout the genuine order disk of radius at most one.
Use: uniform_bessel_zero_disks converts both actual Bessel cubic errors into the true normalized sine-equation errors.
Article: jacobi, Lemma E.1.
Proof: the genuine grid imaginary part is pi*Im(alpha)/2, bounded above by two on the actual unit order disk. Apply the exact original normalization norm identity. -/
theorem frequencyNormalizer_quotient_bound {a w : ℂ} {a0 r M : ℝ}
    (ha : ‖a-(a0:ℂ)‖<r) (hr : r≤1) (hw : ‖w‖≤M) (k : ℕ) :
    ‖w/frequencyNormalizer a k‖≤M*Real.exp 2/2 := by
  -- The actual Fourier multiplier has an explicit bounded norm on the common order disk.
  have hi := Complex.abs_im_le_norm (a-(a0:ℂ))
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
  have him : a.im≤1 := (le_abs_self _).trans (hi.trans (ha.le.trans hr))
  have hq : (frequencyGrid a k).im≤2 := by
    rw [(frequencyGrid_coordinates a k).2]
    nlinarith [Real.pi_pos,Real.pi_lt_four]
  have hM : 0≤M := (norm_nonneg _).trans hw
  rw [frequencyNormalizer_quotient_norm]
  gcongr

/-- The actual Bessel disk equation has uniform genuine derivative and center bounds sufficient for its unique simple zero, on one common complex-order disk.
Use: the uniform numbered zero-tail continuation starts with genuine existing, unique simple zeros of the original Bessel function on these common moving disks.
Article: jacobi, Lemma E.1.
Proof: the proved actual Bessel disk estimate supplies cubic value and slope errors. The exact original Fourier normalization is uniformly bounded; the genuine rational sine derivative differs from one by at most one eighth plus O(1/k). Choose one index cutoff making the true center residual at most one eighth and the actual derivative error at most one half. Apply the community Banach-based unique-zero theorem, then remove the two genuine nonzero normalizing factors to recover the original Bessel zero. -/
theorem uniform_bessel_zero_disk_bounds {a0 : ℝ} (ha0 : -1<a0) :
    ∃ R r : ℝ,∃ hR : 0<R,∃ N : ℕ,0<r ∧ r≤1 ∧ r<a0+1 ∧ 1≤N ∧
      ∀ a : ℂ,‖a-(a0:ℂ)‖<r → ‖besselCoefficient a‖/R≤1/2 ∧ -1<a.re ∧ outgoingBesselCoefficient hR a≠0 ∧
      ∀ k : ℕ,N≤k →
        (∀ ζ∈Metric.closedBall (0:ℂ) (1/4),
          HasDerivAt (frequencyZeroEquation hR a k) (frequencyZeroSlope hR a k ζ) ζ ∧
          ‖1-frequencyZeroSlope hR a k ζ‖≤1/2) ∧
        ‖frequencyZeroEquation hR a k 0‖≤(1/4:ℝ)/2 := by
  -- All fixed-point inputs below are proved for the original Bessel function on one common disk.
  obtain ⟨R,r,C,hR,N,hr,hr1,hra,hC,hN1,hdata⟩ := uniform_bessel_frequency_disks ha0
  let B : ℝ := (‖(a0:ℂ)‖+1)^2+1
  let E : ℝ := C*Real.exp 2/2
  let J : ℝ := 3*B*(B+2)/4+2*B
  have hB : 0<B := by dsimp [B]; positivity
  have hE : 0<E := by dsimp [E]; positivity
  have hJ : 0≤J := by dsimp [J]; positivity
  obtain ⟨M,hM⟩ := exists_nat_gt (8*(B/2+E)+8*(J+E)+1)
  refine ⟨R,r,hR,max N M,hr,hr1,hra,hN1.trans (le_max_left _ _),fun a ha => ?_⟩
  obtain ⟨hcoef,hreal,hA,hdisks⟩ := hdata a ha
  have hc := besselCoefficient_unit_bound (ha.le.trans hr1)
  change ‖besselCoefficient a‖≤B at hc
  refine ⟨hcoef,hreal,hA,fun k hk => ?_⟩
  have hNk : N≤k := (le_max_left N M).trans hk
  have hMk : M≤k := (le_max_right N M).trans hk
  have hk1 : 1≤(k:ℝ) := by exact_mod_cast hN1.trans hNk
  have hkp : 0<(k:ℝ) := lt_of_lt_of_le zero_lt_one hk1
  have hklarge : 8*(B/2+E)+8*(J+E)+1<(k:ℝ) := hM.trans_le (by exact_mod_cast hMk)
  have hrealz (ζ : ℂ) (hζ : ‖ζ‖≤1/4) : frequencyGrid a k+ζ∈Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le zero_lt_one (hdisks k hNk ζ hζ).1))
  have herr (ζ : ℂ) (hζ : ‖ζ‖≤1/4) :
      ‖frequencyError hR a (frequencyGrid a k+ζ)/frequencyNormalizer a k‖≤E/(k:ℝ) ∧
      ‖frequencyErrorSlope hR a (frequencyGrid a k+ζ)/frequencyNormalizer a k‖≤E/(k:ℝ) := by
    have hd := hdisks k hNk ζ hζ
    have hv := frequencyNormalizer_quotient_bound ha hr1 hd.2.1 k
    have hs := frequencyNormalizer_quotient_bound ha hr1 hd.2.2 k
    have hv' : ‖frequencyError hR a (frequencyGrid a k+ζ)/frequencyNormalizer a k‖≤E/(k:ℝ)^3 :=
      hv.trans_eq (by dsimp [E]; ring)
    have hs' : ‖frequencyErrorSlope hR a (frequencyGrid a k+ζ)/frequencyNormalizer a k‖≤E/(k:ℝ)^3 :=
      hs.trans_eq (by dsimp [E]; ring)
    have hquot : E/(k:ℝ)^3≤E/(k:ℝ) :=
      div_le_div_of_nonneg_left hE.le hkp (le_self_pow₀ hk1 (by norm_num : (3:ℕ)≠0))
    exact ⟨hv'.trans hquot,hs'.trans hquot⟩
  have hder (ζ : ℂ) (hζ : ζ∈Metric.closedBall (0:ℂ) (1/4)) :=
    frequencyZeroEquation_hasDerivAt hR a k (hrealz ζ (by simpa only [Metric.mem_closedBall,dist_zero_right] using hζ))
  have hb (ζ : ℂ) (hζ : ζ∈Metric.closedBall (0:ℂ) (1/4)) : ‖1-frequencyZeroSlope hR a k ζ‖≤1/2 := by
    have hζ' : ‖ζ‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hζ
    have hgeom := (frequencyGrid_disk_geometry ha hr1 hreal k hζ').1
    have hz := Complex.slitPlane_ne_zero (hrealz ζ hζ')
    have hsine := frequencySineSlope_close hB.le hc hk1 (hgeom.trans (Complex.re_le_norm _)) hζ'
    have he := (frequencyZeroEquation_expansion hR a k hz).2
    rw [he,norm_sub_rev]
    have heq : frequencySineSlope (besselCoefficient a) (frequencyGrid a k) ζ+
        frequencyErrorSlope hR a (frequencyGrid a k+ζ)/frequencyNormalizer a k-1=
      (frequencySineSlope (besselCoefficient a) (frequencyGrid a k) ζ-1)+
        frequencyErrorSlope hR a (frequencyGrid a k+ζ)/frequencyNormalizer a k := by ring
    rw [heq]
    apply ((norm_add_le _ _).trans (add_le_add hsine (herr ζ hζ').2)).trans
    change 1/8+J/(k:ℝ)+E/(k:ℝ)≤1/2
    rw [add_assoc,← add_div]
    have hsmall : J+E≤(3/8:ℝ)*(k:ℝ) := by nlinarith
    have hh := (div_le_iff₀ hkp).mpr hsmall
    linarith
  have hzero : ‖frequencyZeroEquation hR a k 0‖≤(1/4:ℝ)/2 := by
    have hζ : ‖(0:ℂ)‖≤1/4 := by norm_num
    rw [(frequencyZeroEquation_expansion hR a k (Complex.slitPlane_ne_zero (hrealz 0 hζ))).1]
    have hsine : frequencySine (besselCoefficient a) (frequencyGrid a k) 0= -besselCoefficient a/(2*frequencyGrid a k) := by
      simp [frequencySine,neg_div]
    rw [hsine]
    have hnorm := frequency_quotient_bound hc hk1
      (((frequencyGrid_disk_geometry ha hr1 hreal k hζ).1).trans (Complex.re_le_norm _))
      (by norm_num : (0:ℝ)<2) (n := 1) (by norm_num)
    simp only [add_zero,pow_one] at hnorm
    have hneg : ‖-besselCoefficient a/(2*frequencyGrid a k)‖≤B/(2*(k:ℝ)) := by
      rw [neg_div,norm_neg]
      exact hnorm
    have hh := (norm_add_le _ _).trans (add_le_add hneg (herr 0 hζ).1)
    apply hh.trans
    have hsmall : B/2+E≤(1/8:ℝ)*(k:ℝ) := by nlinarith
    have hquot := (div_le_iff₀ hkp).mpr hsmall
    convert! hquot using 1 <;> ring
  exact ⟨fun ζ hζ => ⟨hder ζ hζ,hb ζ hζ⟩,hzero⟩

/-- The actual disk equation vanishes exactly at the original Bessel zeros whenever its genuine outgoing coefficient is nonzero.
Use: uniform_bessel_zero_disks removes the actual two normalizing factors after constructing the genuine unique simple zero.
Article: jacobi, Lemma E.1.
Proof: both true constant normalizations are nonzero, and the original Liouville factor is a nonzero complex exponential. -/
theorem frequencyZeroEquation_zero_iff {R : ℝ} (hR : 0<R) {a : ℂ}
    (hA : outgoingBesselCoefficient hR a≠0) (k : ℕ) (ζ : ℂ) :
    frequencyZeroEquation hR a k ζ=0 ↔ jacobi.Bessel.normalized a ((frequencyGrid a k+ζ)^2)=0 := by
  simp only [frequencyZeroEquation,div_eq_zero_iff,frequencyNormalizer_ne_zero,hA,or_false,
    frequencyWave,frequencyFactor,mul_eq_zero,Complex.exp_ne_zero,false_or]

/-- Every sufficiently large original moving frequency disk contains exactly one genuine simple Bessel zero on a common complex-order disk.
Use: the holomorphic zero-tail construction identifies its actual branches by this original uniqueness statement.
Article: jacobi, Lemma E.1.
Proof: all quantitative value and derivative hypotheses have been discharged for the original Bessel equation by uniform_bessel_zero_disk_bounds. Apply the proved disk contraction theorem and remove the genuine nonzero source normalizations. -/
theorem uniform_bessel_zero_disks {a0 : ℝ} (ha0 : -1<a0) :
    ∃ R r : ℝ,∃ hR : 0<R,∃ N : ℕ,0<r ∧ r≤1 ∧ r<a0+1 ∧ 1≤N ∧
      ∀ a : ℂ,‖a-(a0:ℂ)‖<r → ‖besselCoefficient a‖/R≤1/2 ∧ -1<a.re ∧ outgoingBesselCoefficient hR a≠0 ∧
      ∀ k : ℕ,N≤k → ∃ ζ : ℂ,‖ζ‖≤1/4 ∧
        jacobi.Bessel.normalized a ((frequencyGrid a k+ζ)^2)=0 ∧
        frequencyZeroSlope hR a k ζ≠0 ∧
        ∀ η : ℂ,‖η‖≤1/4 → jacobi.Bessel.normalized a ((frequencyGrid a k+η)^2)=0 → η=ζ := by
  -- The actual disk bounds and unique zero theorem use the same original normalized Bessel function.
  obtain ⟨R,r,hR,N,hr,hr1,hra,hN,hdata⟩ := uniform_bessel_zero_disk_bounds ha0
  refine ⟨R,r,hR,N,hr,hr1,hra,hN,fun a ha => ?_⟩
  obtain ⟨hc,hreal,hA,hbounds⟩ := hdata a ha
  refine ⟨hc,hreal,hA,fun k hk => ?_⟩
  have hh := hbounds k hk
  obtain ⟨ζ,hζ,hzero,_hsize,hsimple,hunique⟩ := jacobi.Analysis.unique_simple_zero_disk
    (by norm_num : (0:ℝ)≤1/4) (fun z hz => (hh.1 z hz).1) (fun z hz => (hh.1 z hz).2) hh.2
  exact ⟨ζ,hζ,(frequencyZeroEquation_zero_iff hR hA k ζ).mp hzero,hsimple,
    fun η hη he => hunique η hη ((frequencyZeroEquation_zero_iff hR hA k η).mpr he)⟩

end
end jacobi.Hankel
