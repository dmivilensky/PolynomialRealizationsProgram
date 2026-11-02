import jacobi.Reference.SpectralGaps
import jacobi.Bessel.SpectralBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
Article: jacobi, Appendix C.2 (norming ratios).
The norming ratios are the actual infinite products of the two original
spectral gap ratios. Every factor is positive. Absolute convergence of
the deviations from one, convergence of the logarithm series and strict
positivity of the genuine product are proved from the actual spectra.
Use: defines the original norming-ratio infinite product on the ordinary natural index type.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual source spectral-gap factor, with the omitted diagonal factor set to one.
Use: defines the original norming-ratio infinite product on the ordinary natural index type.
Article: jacobi, Proposition C.2.
-/
def normingFactor (a : ℝ) (ha : -1<a) (k l : ℕ) : ℝ :=
  if l=k then 1 else (eigenvalue a l-eigenvalue a k)/(jacobi.Bessel.sigma a ha l- jacobi.Bessel.sigma a ha k)

/-- The original source norming ratio, defined as its actual infinite product.
Use: supplies the actual spectral weights in the Gel'fand--Levitan kernel.
Article: jacobi, Appendix C.4 (target/support weight ratios).
-/
def normingRatio (a : ℝ) (ha : -1<a) (k : ℕ) : ℝ := ∏' l,normingFactor a ha k l

/-- Every genuine norming-product factor is strictly positive over the full original order range.
Use: the actual logarithm sum and product have their required real positive branch.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: both genuine spectra are strictly increasing, so both differences have the same strict sign off the omitted diagonal. -/
theorem normingFactor_pos {a : ℝ} (ha : -1<a) (k l : ℕ) : 0<normingFactor a ha k l := by
  unfold normingFactor
  split_ifs with h
  · norm_num
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact div_pos_of_neg_of_neg (sub_neg.mpr (eigenvalue_strictMono ha hlt))
        (sub_neg.mpr (jacobi.Bessel.sigma_strictMono ha hlt))
    · exact div_pos (sub_pos.mpr (eigenvalue_strictMono ha hgt))
        (sub_pos.mpr (jacobi.Bessel.sigma_strictMono ha hgt))

/-- All true spectral displacements are bounded by one fixed positive constant, including every small index.
Use: bounds the numerator of the actual norming-factor perturbation in the convergent infinite tail.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the proved inverse-square McMahon displacement is at most its fixed numerator because every original index is at least one. -/
theorem spectrum_error_bounded {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ k,|jacobi.Bessel.sigma a ha k-eigenvalue a k|≤C := by
  obtain ⟨C,hC,he⟩ := spectrum_error ha
  refine ⟨C,hC,fun k => (he k).trans ?_⟩
  apply div_le_self hC.le
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- The actual norming-factor perturbations have a summable inverse-square bound beyond twice the fixed original index.
Use: proves absolute convergence of the original norming-ratio product without adding a spectral-gap or asymptotic premise.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the actual quadratic Bessel gap dominates one half of its large
one-based index square. The numerator of factor-minus-one is the
difference of two genuine bounded spectral displacements. Divide by
the true positive gap to obtain one inverse-square tail majorant. -/
theorem normingFactor_tail {a : ℝ} (ha : -1<a) :
    ∃ K : ℝ,0<K ∧ ∀ k l : ℕ,2*k+1≤l →
      |normingFactor a ha k l-1|≤K/(l+1:ℝ)^2 := by
  -- The degree threshold depends on the original fixed index; every factor is the actual source gap ratio.
  obtain ⟨C,hC,he⟩ := spectrum_error_bounded ha
  obtain ⟨c,hc,hgap⟩ := bessel_spectral_gap ha
  refine ⟨4*C/c,by positivity,?_⟩
  intro k l hkl
  have hlt : k<l := by omega
  have hx : 0<(k+1:ℝ) := by positivity
  have hy : 0<(l+1:ℝ) := by positivity
  have hxy : 2*(k+1:ℝ)≤l+1 := by exact_mod_cast (show 2*(k+1)≤l+1 by omega)
  have hsq := (sq_le_sq₀ (by positivity : 0≤2*(k+1:ℝ)) hy.le).mpr hxy
  have hcsq := mul_le_mul_of_nonneg_left hsq hc.le
  have hden : (c/2)*(l+1:ℝ)^2≤ jacobi.Bessel.sigma a ha l- jacobi.Bessel.sigma a ha k := by
    nlinarith [hgap k l hlt.le]
  have hdp : 0< jacobi.Bessel.sigma a ha l- jacobi.Bessel.sigma a ha k :=
    sub_pos.mpr (jacobi.Bessel.sigma_strictMono ha hlt)
  have hnum : |(eigenvalue a l-eigenvalue a k)-(jacobi.Bessel.sigma a ha l- jacobi.Bessel.sigma a ha k)|≤2*C := by
    calc
      _ = |(jacobi.Bessel.sigma a ha k-eigenvalue a k)-(jacobi.Bessel.sigma a ha l-eigenvalue a l)| := by congr 1; ring
      _ ≤ |jacobi.Bessel.sigma a ha k-eigenvalue a k|+|jacobi.Bessel.sigma a ha l-eigenvalue a l| := abs_sub _ _
      _ ≤ _ := by linarith [he k,he l]
  simp only [normingFactor,hlt.ne',ite_false]
  rw [div_sub_one hdp.ne',abs_div,abs_of_pos hdp]
  apply (div_le_div_iff₀ hdp (sq_pos_of_pos hy)).mpr
  have hmul := mul_le_mul_of_nonneg_left hden (show 0≤4*C/c by positivity)
  have hid : (4*C/c)*((c/2)*(l+1:ℝ)^2)=2*C*(l+1:ℝ)^2 := by field_simp [hc.ne']; ring
  rw [hid] at hmul
  nlinarith [mul_le_mul_of_nonneg_right hnum (sq_nonneg (l+1:ℝ))]

/-- The deviations of the original norming-product factors from one are absolutely summable at every original index.
Use: gives genuine product and logarithm convergence for the literal source norming ratios.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the true tail perturbations are bounded by the proved inverse-square majorant, and the finite omitted prefix does not affect summability. -/
theorem normingFactor_summable {a : ℝ} (ha : -1<a) (k : ℕ) :
    Summable (fun l => |normingFactor a ha k l-1|) := by
  obtain ⟨K,hK,htail⟩ := normingFactor_tail ha
  have hsum := (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left K
  simp only [one_pow,mul_one_div] at hsum
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2*k+1)] with l hl
  simpa only [Real.norm_eq_abs,abs_abs] using htail k l hl

/-- The original positive norming factors have a genuinely convergent real logarithm series.
Use: establishes positivity of the actual infinite product and justifies its logarithmic estimates.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: absolute convergence of the true factor deviations gives summability; apply the community logarithm-series theorem. -/
theorem normingFactor_log_summable {a : ℝ} (ha : -1<a) (k : ℕ) :
    Summable (fun l => Real.log (normingFactor a ha k l)) := by
  have h := Real.summable_log_one_add_of_summable (normingFactor_summable ha k).of_abs
  simpa only [add_sub_cancel] using h

/-- The actual original norming-ratio product genuinely converges and is strictly positive.
Use: supplies the original positive source weights for the Gel'fand--Levitan construction, without assuming product convergence or nonvanishing.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: exponentiate the proved convergent real logarithm series of the actual positive factors. Its exponential is the actual infinite product and is strictly positive. -/
theorem normingRatio_properties {a : ℝ} (ha : -1<a) (k : ℕ) :
    HasProd (normingFactor a ha k) (normingRatio a ha k) ∧ 0<normingRatio a ha k := by
  have hsum := normingFactor_log_summable ha k
  have hpos := normingFactor_pos ha k
  have hm := Real.multipliable_of_summable_log hpos hsum
  refine ⟨hm.hasProd,?_⟩
  rw [normingRatio,← Real.rexp_tsum_eq_tprod hpos hsum]
  exact Real.exp_pos _

end
end jacobi.Reference
