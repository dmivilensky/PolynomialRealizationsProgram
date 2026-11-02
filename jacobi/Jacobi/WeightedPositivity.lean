import jacobi.Jacobi.Weight
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
Article: jacobi, Lemma C.1.
A nonzero polynomial nonnegative on the Jacobi interval has strictly
positive actual weighted integral. Its finitely many zeros have measure
zero; singular endpoint weights are already known to be integrable.
Source: positivity of orthogonal-polynomial measures and finite polynomial zero sets.
Use: rules out a lower-degree sign-correcting orthogonality test in finite zero location and repeated-root exclusion.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- A nonzero polynomial nonnegative on the open Jacobi interval has a strictly positive genuine Jacobi-weight integral.
Use: rules out a lower-degree sign-correcting orthogonality test in finite zero location and repeated-root exclusion.
Article: jacobi, Lemma C.1.
Proof: remove the irrelevant endpoints. The weight is positive on the
interior and the polynomial is positive there almost everywhere because
its actual zero set is finite. A zero integral of this nonnegative
integrable function would force it to vanish almost everywhere on an interval of measure one. -/
theorem weighted_polynomial_integral_pos {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {p : Polynomial ℝ} (hp : p≠0) (hpos : ∀ t∈Ioo (0:ℝ) 1,0≤p.eval t) :
    0<∫ t in (0:ℝ)..1,weight a b t*p.eval t := by
  -- The actual polynomial can vanish only on a finite null set.
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]
  let μ := volume.restrict (Ioo (0:ℝ) 1)
  have hi : Integrable (fun t => weight a b t*p.eval t) μ :=
    (weight_mul_integrable ha hb p.continuous).1.mono_set Ioo_subset_Ioc_self
  have hmem : ∀ᵐ t∂μ,t∈Ioo (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  have hnon : 0≤ᵐ[μ] (fun t => weight a b t*p.eval t) := by
    filter_upwards [hmem] with t ht
    exact mul_nonneg (weight_pos a b ht).le (hpos t ht)
  have hroot : ∀ᵐ t∂μ,p.eval t≠0 := (p.finite_setOfPred_isRoot hp).countable.ae_notMem μ
  apply lt_of_le_of_ne (integral_nonneg_of_ae hnon)
  intro hz
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnon hi).mp hz.symm
  have hfalse : ∀ᵐ t∂μ,False := by
    filter_upwards [hmem,hroot,hzero] with t ht hne he
    have hp : 0<p.eval t := lt_of_le_of_ne (hpos t ht) hne.symm
    exact (mul_pos (weight_pos a b ht) hp).ne' he
  have hμ : μ=0 := by simpa only [Filter.eventually_false_iff_eq_bot,ae_eq_bot] using hfalse
  have h := congrArg (fun ν : Measure ℝ => ν univ) hμ
  norm_num [μ] at h

end
end jacobi.Jacobi
