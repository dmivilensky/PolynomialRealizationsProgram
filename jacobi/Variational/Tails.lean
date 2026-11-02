import jacobi.Variational.Problem

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Pointwise radial bounds are derived from the actual integral constraints for
symmetric decreasing densities. These estimates are the majorants required
for local compactness and for tightness under a root-mass bound.
Source: the elementary integral bound for a nonnegative decreasing function.
Use: the precise shape supplied by rearrangement and preserved by compactness limits. The value at the null singleton {0} is unrestricted: a finite-energy limit can have an unbounded singularity near zero while remaining finite almost everywhere.
-/
namespace jacobi.Variational
noncomputable section
open Set Real MeasureTheory

/-- Evenness and monotonicity on the open positive half-line.
Use: the precise shape supplied by rearrangement and preserved by compactness limits.
The value at the null singleton {0} is unrestricted: a finite-energy limit
can have an unbounded singularity near zero while remaining finite almost everywhere.
Article: jacobi, Lemma D.1.
-/
structure SymmetricDecreasing (m : ℝ → ℝ) : Prop where
  /-- Reflection symmetry on the real line. -/
  even : ∀ x, m (-x)=m x
  /-- The density does not increase at strictly positive radii. -/
  decreasing : AntitoneOn m (Ioi 0)

/-- Even functions depend only on the absolute value of their argument.
Use: applies the half-line monotonicity to every point in a centered interval.
Article: jacobi, Appendix D.1 (radial convolution and strict ground monotonicity).
Proof: split according to the sign of the argument and use reflection symmetry. -/
theorem SymmetricDecreasing.abs_eq {m : ℝ → ℝ} (hs : SymmetricDecreasing m) (x : ℝ) :
    m |x| = m x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, hs.even]

/-- Every nonzero point in a centered interval has at least the boundary density value.
Use: compares the interval integral with its length times the boundary value.
Article: jacobi, Appendix D.1 (radial tail bounds).
Proof: absolute values order the distances to the origin. -/
theorem SymmetricDecreasing.lower_on_interval {m : ℝ → ℝ} (hs : SymmetricDecreasing m)
    (x y : ℝ) (hy : y ∈ Icc (-|x|) |x|) (hy0 : y ≠ 0) : m x ≤ m y := by
  rw [← hs.abs_eq x, ← hs.abs_eq y]
  exact hs.decreasing (abs_pos.mpr hy0)
    ((abs_pos.mpr hy0).trans_le (abs_le.mpr hy)) (abs_le.mpr hy)

/-- The exact radial integral bound behind all three pointwise tail estimates.
Use: applies to m, m^(3/2) and sqrt(m) with their respective integral constraints.
Article: jacobi, Appendix D.1 (radial tail bounds).
Proof: integrate the constant lower bound on the centered interval and then
use nonnegativity to bound its integral by the full mass. -/
theorem radial_integral_bound {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hs : SymmetricDecreasing m) (x : ℝ) : 2*|x| *m x ≤ ∫ y, m y := by
  -- The centered interval has length 2|x| and lies inside the full integration domain.
  have hc : IntegrableOn (fun _ : ℝ => m x) (Icc (-|x|) |x|) := integrableOn_const (hs := isCompact_Icc.measure_ne_top)
  have hzero : ∀ᵐ y : ℝ, y ≠ 0 := by simp [ae_iff]
  have h := setIntegral_mono_ae_restrict hc hm.integrableOn (by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hzero] with y hy hy0
    exact hs.lower_on_interval x y hy hy0)
  have he : (∫ _y in Icc (-|x|) |x|, m x) = 2*|x| *m x := by
    rw [setIntegral_const, Measure.real, Real.volume_Icc]
    simp only [sub_neg_eq_add, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [he] at h
  exact h.trans (setIntegral_le_integral hm (Filter.Eventually.of_forall hn))

/-- The mass tail bound holds at every nonzero point.
Use: bounds the operator norm of the density removed by truncation.
Article: jacobi, Appendix D.1 (radial tail bounds).
Proof: divide the radial mass bound by the strictly positive interval length. -/
theorem mass_tail {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hs : SymmetricDecreasing m) {M : ℝ} (hM : (∫ y, m y) ≤ M) {x : ℝ} (hx : x ≠ 0) :
    m x ≤ M/(2*|x|) := by
  rw [le_div_iff₀ (mul_pos (by norm_num) (abs_pos.mpr hx))]
  nlinarith [radial_integral_bound hm hn hs x]

/-- The energy integrand preserves symmetry and radial monotonicity.
Use: applies the radial integral bound with the energy rather than the mass.
Article: jacobi, Appendix D.1 (radial tail bounds).
Proof: real 3/2 powers are monotone on the nonnegative half-line. -/
theorem SymmetricDecreasing.energy {m : ℝ → ℝ} (hs : SymmetricDecreasing m)
    (hn : ∀ x, 0 ≤ m x) : SymmetricDecreasing (fun x => m x^(3/2 : ℝ)) where
  even x := by rw [hs.even]
  decreasing := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow (hn y) (hs.decreasing hx hy hxy) (by norm_num)

/-- The energy constraint gives the integrable local majorant away from the origin.
Use: the dominating function in the Compactness lemma's local L1 convergence.
Article: jacobi, Appendix D.1 (radial tail bounds).
Proof: apply the radial bound to m^(3/2), then take the increasing 2/3 power. -/
theorem energy_tail (m : Density) (hs : SymmetricDecreasing m.value) {E : ℝ}
    (hE : m.energy ≤ E) {x : ℝ} (hx : x ≠ 0) :
    m.value x ≤ (E/(2*|x|))^(2/3 : ℝ) := by
  have h : m.value x^(3/2 : ℝ) ≤ E/(2*|x|) :=
    mass_tail m.energy_integrable (fun y => Real.rpow_nonneg (m.nonneg y) _)
      (hs.energy m.nonneg) hE hx
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg (m.nonneg x) _) h (by norm_num : 0 ≤ (2/3 : ℝ))
  simpa only [← Real.rpow_mul (m.nonneg x), show (3/2 : ℝ)*(2/3)=1 by norm_num,
    Real.rpow_one] using hr

/-- Square roots preserve symmetry and radial monotonicity.
Use: the root-mass bound provides an integrable majorant at infinity.
Article: jacobi, Appendix D.1 (radial tail bounds).
Proof: the nonnegative square-root function is monotone. -/
theorem SymmetricDecreasing.root {m : ℝ → ℝ} (hs : SymmetricDecreasing m) :
    SymmetricDecreasing (fun x => Real.sqrt (m x)) where
  even x := by rw [hs.even]
  decreasing := by
    intro x hx y hy hxy
    exact Real.sqrt_le_sqrt (hs.decreasing hx hy hxy)

/-- A finite root-mass bound yields the quadratic pointwise decay estimate.
Use: combines with the energy majorant to give global L1 tightness.
Article: jacobi, Appendix D.1 (radial tail bounds).
Proof: apply the radial bound to sqrt(m) and square the resulting nonnegative inequality. -/
theorem root_tail {m : ℝ → ℝ} (hn : ∀ x, 0 ≤ m x) (hs : SymmetricDecreasing m)
    (hr : Integrable (fun y => Real.sqrt (m y))) {r : ℝ} (hrb : (∫ y, Real.sqrt (m y)) ≤ r)
    {x : ℝ} (hx : x ≠ 0) : m x ≤ r^2/(4*x^2) := by
  have h := radial_integral_bound hr (fun y => Real.sqrt_nonneg (m y)) hs.root x
  have hr0 : 0 ≤ r := (integral_nonneg (fun y => Real.sqrt_nonneg (m y))).trans hrb
  rw [le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_ne_zero hx))]
  have hm := Real.sq_sqrt (hn x)
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 2*|x| *Real.sqrt (m x)) (h.trans hrb)
  nlinarith [sq_abs x]

end
end jacobi.Variational
