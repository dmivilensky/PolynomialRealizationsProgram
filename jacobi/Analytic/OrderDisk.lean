import jacobi.Analytic.BesselZeroSeparation

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
This is a concrete common disk for the original numbered spectrum, with
all estimates valid on its closure and holomorphic branches on a larger
open disk. Its existence follows from the proved Bessel zero theorem.
Use: every norming product and GL series uses these same branches, so their real restrictions retain the original spectral numbering.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric

/-- A closed order disk carrying the actual continued numbered Bessel spectrum.
Use: every norming product and GL series uses these same branches, so their
real restrictions retain the original spectral numbering.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
structure OrderDisk (a0 : ℝ) where
  /-- The radius of the closed disk used for uniform estimates.
  Use: compactness upgrades normal convergence to uniform convergence.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  radius : ℝ
  /-- The radius is strictly positive.
  Use: holomorphic conclusions hold on a genuine neighborhood of the real base point.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  radius_pos : 0<radius
  /-- The closed disk lies in the admissible order half-plane.
  Use: the reference spectral gaps have no zeros on this disk.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  radius_lt : radius<a0+1
  /-- One positive numerator bounds every inverse-square spectral error.
  Use: gives the summable perturbation of the original gap products.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  errorConstant : ℝ
  /-- Positivity of the common spectral-error numerator.
  Use: preserves inequalities when summing the actual spectral perturbations.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  error_pos : 0<errorConstant
  /-- One positive constant controls every original quadratic spectral gap.
  Use: division by the actual complex gaps is uniformly bounded.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  gapConstant : ℝ
  /-- Strict positivity of the spectral-gap constant.
  Use: every off-diagonal denominator is nonzero.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  gap_pos : 0<gapConstant
  /-- The holomorphic continuation of the original numbered squared Bessel zeros.
  Use: these are the target energies throughout the analytic GL construction.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  spectrum : ℕ → ℂ → ℂ
  /-- The branches are holomorphic on an open disk containing the whole closed estimation disk.
  Use: finite gap products are holomorphic and continuous up to its boundary.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  holomorphic : ∀ k,DifferentiableOn ℂ (spectrum k) (ball (a0:ℂ) (2*radius))
  /-- On the real axis every branch is the original numbered Bessel zero.
  Use: identifies the continued norming products with the real GL data.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  real_eq : ∀ b : ℝ,∀ hb : -1<b,‖(b:ℂ)-(a0:ℂ)‖≤radius →
    ∀ k,spectrum k (b:ℂ)=(jacobi.Bessel.sigma b hb k:ℂ)
  /-- Every continued spectral value is a zero of the original normalized Bessel function.
  Use: rules out arbitrary holomorphic spectral replacements in the GL construction.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  root : ∀ a : ℂ,‖a-(a0:ℂ)‖≤radius → ∀ k,
    jacobi.Bessel.normalized a (spectrum k a)=0
  /-- The genuine reference displacement has one inverse-square bound, including the finite prefix.
  Use: yields the uniform inverse-square norming-product estimate.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  error : ∀ a : ℂ,‖a-(a0:ℂ)‖≤radius → ∀ k,
    ‖spectrum k a- jacobi.Hankel.frequencyReference a k‖≤errorConstant/(k+1:ℝ)^2
  /-- Each actual continued spectral value stays quadratically away from zero.
  Use: bounds the reciprocals in the analytic profile series.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  lower : ∀ a : ℂ,‖a-(a0:ℂ)‖≤radius → ∀ k : ℕ,
    gapConstant*(k+1:ℝ)^2≤‖spectrum k a‖
  /-- Distinct continued spectral values have the original quadratic-index separation.
  Use: the norming products have no singular denominators anywhere on the disk.
  Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
  separation : ∀ a : ℂ,‖a-(a0:ℂ)‖≤radius → ∀ k l : ℕ,k≠l →
    gapConstant*|(l+1:ℝ)^2-(k+1:ℝ)^2|≤‖spectrum l a-spectrum k a‖

/-- A common closed spectral disk exists for every original admissible real order.
Use: supplies the actual data for analytic GL without any continuation,
separation, or asymptotic assumption left for the caller to prove.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: halve the radius of the full proved numbered Bessel-zero theorem.
The estimates then hold on the closed smaller disk while the original
open disk still supplies the required holomorphic neighborhood. -/
theorem orderDisk_nonempty {a0 : ℝ} (ha0 : -1<a0) : Nonempty (OrderDisk a0) := by
  -- The finite prefix and infinite tail are already included in the actual Bessel theorem.
  obtain ⟨r,C,c,S,hr,hra,hC,hc,hSa,hreal,hdata,hsep⟩ :=
    jacobi.Bessel.uniform_numbered_bessel_zeros ha0
  have hsmall {a : ℂ} (ha : ‖a-(a0:ℂ)‖≤r/2) : ‖a-(a0:ℂ)‖<r := by linarith
  exact ⟨{
    radius := r/2
    radius_pos := by positivity
    radius_lt := by linarith
    errorConstant := C
    error_pos := hC
    gapConstant := c
    gap_pos := hc
    spectrum := S
    holomorphic := by simpa only [show 2*(r/2)=r by ring] using hSa
    real_eq := fun b hb ha => hreal b hb (hsmall ha)
    root := fun a ha k => (hdata a (hsmall ha) k).1
    error := fun a ha k => (hdata a (hsmall ha) k).2.1
    lower := fun a ha k => (hdata a (hsmall ha) k).2.2
    separation := fun a ha k l => hsep a (hsmall ha) k l }⟩

/-- Every point of the actual closed spectral disk has admissible real part.
Use: the genuine reference gaps are nonzero on the entire estimation disk.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the real-part displacement is bounded by the complex norm, which
is at most the disk radius and strictly less than the real half-plane margin. -/
theorem OrderDisk.admissible {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) : -1<a.re := by
  have hh := Complex.re_le_norm ((a0:ℂ)-a)
  rw [norm_sub_rev] at hh
  simp only [Complex.sub_re,Complex.ofReal_re] at hh
  linarith [D.radius_lt]

end
end jacobi.Analytic
