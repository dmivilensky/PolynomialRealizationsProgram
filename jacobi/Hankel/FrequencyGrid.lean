import jacobi.Hankel.FrequencyStrip
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Article: jacobi, Lemma C.1.
The actual affine Bessel phase grid, with zero-based Lean indices,
has its canonical exponential phase and explicit complex disk
geometry. These are the centers used by the numbered zero tail.
Use: the actual large Bessel zero disks are centered at this grid; its square with the inverse-square correction gives the reference spectrum tau.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The original complex affine frequency grid with zero-based index.
Use: the actual large Bessel zero disks are centered at this grid; its square with the inverse-square correction gives the reference spectrum tau.
Article: jacobi, Lemma E.1.
-/
def frequencyGrid (a : ℂ) (k : ℕ) : ℂ := (Real.pi:ℂ)*((k:ℂ)+a/2+3/4)

/-- Every actual frequency-grid center has the original canonical doubled Fourier phase.
Use: frequencyHankel_sine rewrites the true two-wave Hankel approximation as the sine zero equation in each actual frequency disk.
Article: jacobi, Lemma E.1.
Proof: the integer phase increment is k*2*pi*i, whose exponential is exactly one by the community periodicity theorem. -/
theorem frequencyGrid_phase (a : ℂ) (k : ℕ) :
    Complex.exp (2*Complex.I*frequencyGrid a k)=besselZeroPhase a := by
  rw [show 2*Complex.I*frequencyGrid a k=(k:ℂ)*(2*(Real.pi:ℂ)*Complex.I)+
    2*Complex.I*(Real.pi:ℂ)*(a/2+3/4) by unfold frequencyGrid; ring,
    Complex.exp_add,Complex.exp_nat_mul_two_pi_mul_I,one_mul]
  rfl

/-- The actual complex phase grid has its exact original real and imaginary coordinates.
Use: frequencyGrid_disk_geometry places every large moving frequency disk in one genuine bounded complex-frequency strip.
Article: jacobi, Lemma E.1.
Proof: evaluate the actual affine grid through the complex real and imaginary coordinate homomorphisms. -/
theorem frequencyGrid_coordinates (a : ℂ) (k : ℕ) :
    (frequencyGrid a k).re=Real.pi*((k:ℝ)+a.re/2+3/4) ∧
      (frequencyGrid a k).im=Real.pi*a.im/2 := by
  constructor
  · simp [frequencyGrid,Complex.mul_re]
  · simp [frequencyGrid,Complex.mul_im]
    ring

/-- The genuine radius-one-quarter frequency disks have a uniform right-half-plane lower bound and a bounded imaginary part on every admissible order disk of radius at most one.
Use: the actual complex Hankel strip estimate applies simultaneously to all sufficiently large moving frequency disks; their real part grows at least linearly in the original index.
Article: jacobi, Lemma E.1.
Proof: the original order has real part greater than minus one. The frequency displacement changes each coordinate by at most its norm; the order's imaginary part is bounded by its genuine distance from the real center. -/
theorem frequencyGrid_disk_geometry {a : ℂ} {a0 r : ℝ} (ha : ‖a-(a0:ℂ)‖<r)
    (hr : r≤1) (har : -1<a.re) (k : ℕ) {ζ : ℂ} (hζ : ‖ζ‖≤1/4) :
    (k:ℝ)≤(frequencyGrid a k+ζ).re ∧ |(frequencyGrid a k+ζ).im|≤4 := by
  -- The source index is zero-based; the positive quarter offset covers even the first disk's geometry.
  have hi := Complex.abs_im_le_norm (a-(a0:ℂ))
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
  have hia : |a.im|≤1 := hi.trans (ha.le.trans hr)
  obtain ⟨hqre,hqim⟩ := frequencyGrid_coordinates a k
  have hre : -(1/4:ℝ)≤ζ.re := by have hh := Complex.abs_re_le_norm ζ; linarith [(neg_le_abs ζ.re).trans (hh.trans hζ)]
  have him : |ζ.im|≤1/4 := (Complex.abs_im_le_norm ζ).trans hζ
  constructor
  · rw [Complex.add_re,hqre]
    have hp := Real.pi_gt_three
    have hk : 0≤(k:ℝ) := Nat.cast_nonneg k
    nlinarith
  · rw [Complex.add_im,hqim]
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_mul,abs_of_pos Real.pi_pos]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hp := Real.pi_lt_four
    nlinarith [Real.pi_pos]

end
end jacobi.Hankel
