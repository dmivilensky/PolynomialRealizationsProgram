import jacobi.Analytic.OrderReferenceBounds
import jacobi.Analytic.ReferenceEnergyContinuity

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Bounded perturbations of the squared affine frequency grid have square
roots in a common horizontal strip, with the original linear frequency
scale. The choice of sign is used only for estimates, not for analyticity.
Use: transfers the proved reference strip estimate to actual complex energy disks without differentiating a square root.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric jacobi.ComplexReference jacobi.Hankel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A bounded perturbation of a square with positive real frequency has a square root close to that frequency.
Use: transfers the proved reference strip estimate to actual complex energy disks without differentiating a square root.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: choose the sign of a square root to make its real part nonnegative. Factoring the difference of squares gives a denominator whose norm is at least the positive real part of the reference frequency. -/
theorem square_root_near_frequency {z v : ℂ} {r E : ℝ}
    (hr : 0<r) (hv : r≤v.re) (hz : ‖z-v^2‖≤E) :
    ∃ w : ℂ,w^2=z ∧ ‖w-v‖≤E/r := by
  -- The sign choice is pointwise and never enters the defining analytic energy series.
  obtain ⟨w,hw,hre⟩ : ∃ w : ℂ,w^2=z ∧ 0≤w.re := by
    by_cases h : 0≤(Complex.sqrt z).re
    · exact ⟨Complex.sqrt z,jacobi.Reference.frequency_square z,h⟩
    · refine ⟨-Complex.sqrt z,?_,?_⟩
      · simpa only [neg_sq] using jacobi.Reference.frequency_square z
      · simpa only [Complex.neg_re] using (neg_nonneg.mpr (le_of_not_ge h))
  refine ⟨w,hw,(le_div_iff₀ hr).mpr ?_⟩
  have hden : r≤‖w+v‖ := by
    have hh := Complex.re_le_norm (w+v)
    simp only [Complex.add_re] at hh
    linarith
  calc
    ‖w-v‖*r ≤ ‖w-v‖*‖w+v‖ := mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ = ‖z-v^2‖ := by rw [← norm_mul,show (w-v)*(w+v)=z-v^2 by rw [← hw]; ring]
    _ ≤ E := hz

/-- The genuine affine reference frequency has a uniform positive real-part scale on the whole original spectral order disk.
Use: supplies the denominator lower bound in the complex energy perturbation estimate, including the first index.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: admissibility gives Re(alpha)>-1, and pi>3 makes the positive quarter offset dominate half the shifted index. -/
theorem OrderDisk.frequency_real_lower {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) (k : ℕ) :
    (k+1:ℝ)/2≤(frequencyGrid a k).re := by
  rw [(frequencyGrid_coordinates a k).1]
  have har := D.admissible ha
  have hk : 0≤(k:ℝ) := Nat.cast_nonneg k
  nlinarith [Real.pi_gt_three]

/-- Uniformly bounded energy perturbations of the actual reference spectrum retain a common frequency strip and the original linear frequency scale in the tail.
Use: applies the proved complex-order reference bound on all genuine energy Cauchy disks around the target-reference spectral segments.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: compare a square root of the shifted energy with the original affine grid using the factored difference of squares. The imaginary grid coordinate is uniformly bounded by the order disk; the root displacement is at most twice the energy radius. For sufficiently large index this also preserves a quarter of the original frequency scale. -/
theorem OrderDisk.energy_frequency_geometry {a0 : ℝ} (D : OrderDisk a0)
    {E : ℝ} (hE : 0≤E) {a z : ℂ} (ha : ‖a-(a0:ℂ)‖≤D.radius)
    (k : ℕ) (hk : 8*E+4≤(k+1:ℝ)) (hz : ‖z-frequencyReference a k‖≤E) :
    ∃ w : ℂ,w^2=z-besselCoefficient a ∧
      |w.im|≤Real.pi*D.radius/2+2*E ∧ (k+1:ℝ)/4≤‖w‖ := by
  -- The same strip covers all perturbed energies and every order in the actual closed disk.
  have hkp : 0<(k+1:ℝ) := by positivity
  have hgrid := D.frequency_real_lower ha k
  obtain ⟨w,hw,hd⟩ := square_root_near_frequency (half_pos hkp) hgrid
    (z := z-besselCoefficient a) (E := E) (by
      convert hz using 1
      congr 1
      unfold frequencyReference
      ring)
  have hd2 : ‖w-frequencyGrid a k‖≤2*E := by
    have hh : E/((k+1:ℝ)/2)≤2*E := by
      apply (div_le_iff₀ (half_pos hkp)).mpr
      have hkn : 1≤(k+1:ℝ) := by norm_cast; omega
      nlinarith
    exact hd.trans hh
  have hi : |a.im|≤D.radius := by
    have hh := Complex.abs_im_le_norm (a-(a0:ℂ))
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hh
    exact hh.trans ha
  refine ⟨w,hw,?_,?_⟩
  · have him : |w.im-(frequencyGrid a k).im|≤2*E := by
      simpa only [Complex.sub_im] using (Complex.abs_im_le_norm _).trans hd2
    calc
      |w.im| ≤ |w.im-(frequencyGrid a k).im|+|(frequencyGrid a k).im| := by
        simpa only [sub_add_cancel] using abs_add_le (w.im-(frequencyGrid a k).im) (frequencyGrid a k).im
      _ ≤ 2*E+|(frequencyGrid a k).im| := by linarith
      _ ≤ 2*E+Real.pi*D.radius/2 := by
        rw [(frequencyGrid_coordinates a k).2,abs_div,abs_mul,abs_of_pos Real.pi_pos]
        norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
        gcongr
      _ = _ := by ring
  · have hh := norm_le_norm_sub_add (frequencyGrid a k) w
    rw [norm_sub_rev] at hh
    have hgn := hgrid.trans (Complex.re_le_norm (frequencyGrid a k))
    linarith

end
end jacobi.Analytic
