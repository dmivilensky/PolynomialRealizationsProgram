import jacobi.Variational.SecondMoment
import jacobi.Continuum.MomentBounds

/-!
Article: jacobi, Proposition D.2.
Explicit nonnegative finite-energy boxes have the prescribed mass. Their
second moment approaches the square of the mass as the width tends to zero;
the top eigenvalue approaches the mass by the proved spectral moment bound.
Consequently all strictly subcritical joint moment thresholds are feasible.
Source: elementary kernel comparison on a shrinking interval.
Use: proves feasibility of all strictly subcritical joint moment constraints.
-/
namespace jacobi.Variational
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal narrow box of mass M and positive half-width r.
Use: proves feasibility of all strictly subcritical joint moment constraints.
Article: jacobi, Proposition D.2.
-/
def narrowBox (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r) : Density where
  value := (Icc (-r) r).indicator (fun _ => M/(2*r))
  measurable := measurable_const.indicator measurableSet_Icc
  nonneg x := indicator_nonneg (fun _ _ => div_nonneg hM (by positivity)) x
  integrable := (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  energy_integrable := by
    have he : (fun x => ((Icc (-r) r).indicator (fun _ : ℝ => M/(2*r)) x)^(3/2 : ℝ))=
        (Icc (-r) r).indicator (fun _ : ℝ => (M/(2*r))^(3/2 : ℝ)) := by
      funext x
      by_cases hx : x ∈ Icc (-r) r <;> simp [hx,Real.zero_rpow (by norm_num : (3/2 : ℝ) ≠ 0)]
    rw [he]
    exact (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc

/-- The actual box has exactly its prescribed mass.
Use: the feasibility construction meets the original mass bound without slack.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: integrate its constant height over an interval of length 2r. -/
theorem narrowBox_mass (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r) :
    (narrowBox M r hM hr).mass=M := by
  rw [Density.mass,narrowBox,integral_indicator measurableSet_Icc,setIntegral_const,
    Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0 ≤ r- -r),smul_eq_mul]
  field_simp
  ring

/-- The actual box second moment has an explicit lower bound tending to M squared.
Use: proves subcritical second-moment feasibility and then top-eigenvalue feasibility.
Article: jacobi, Proposition D.2.
Proof: any two supported points are at distance at most 2r, so the kernel
exp(-2|x-y|) is at least exp(-4r). Integrate the independent density product. -/
theorem narrowBox_second_lower (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r) :
    exp (-4*r)*M^2 ≤ observe (narrowBox M r hM hr) .second := by
  -- The comparison is made on the genuine double integral of the actual operator spectrum.
  let b := narrowBox M r hM hr
  have hc (x y : ℝ) : exp (-4*r)*(b.value x*b.value y) ≤
      b.value x*b.value y*exp (-2*|x-y|) := by
    by_cases hx : x ∈ Icc (-r) r
    · by_cases hy : y ∈ Icc (-r) r
      · have hd : |x-y| ≤ 2*r := abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩
        have hk : exp (-4*r) ≤ exp (-2*|x-y|) := exp_le_exp.mpr (by linarith)
        rw [mul_comm (exp (-4*r))]
        exact mul_le_mul_of_nonneg_left hk (mul_nonneg (b.nonneg x) (b.nonneg y))
      · simp only [b,narrowBox,indicator_of_notMem hy,mul_zero,zero_mul,le_refl]
    · simp only [b,narrowBox,indicator_of_notMem hx,mul_zero,zero_mul,le_refl]
  have hi := integral_mono ((b.integrable.mul_prod b.integrable).const_mul (exp (-4*r)))
    (second_integrand_integrable b.integrable b.integrable b.measurable b.measurable)
    (fun z : ℝ × ℝ => hc z.1 z.2)
  rw [integral_const_mul,integral_prod_mul] at hi
  rw [← b.secondPairing_self]
  change exp (-4*r)*M^2 ≤
    ∫ z : ℝ × ℝ, b.value z.1*b.value z.2*exp (-2*|z.1-z.2|) ∂volume.prod volume
  change exp (-4*r)*(b.mass*b.mass) ≤ _ at hi
  have hm : b.mass=M := narrowBox_mass M r hM hr
  rw [hm] at hi
  simpa only [pow_two] using hi

/-- The largest actual box eigenvalue has a lower bound tending to M.
Use: proves feasibility of a joint top and second-moment constraint with one density.
Article: jacobi, Proposition D.2.
Proof: G_2≤G_infinity times mass, and the proved box lower bound gives the claim after division by M. -/
theorem narrowBox_top_lower (M r : ℝ) (hM : 0 < M) (hr : 0 < r) :
    exp (-4*r)*M ≤ observe (narrowBox M r hM.le hr) .top := by
  let b := narrowBox M r hM.le hr
  have h := jacobi.Continuum.kernel_moment_bound b.integrable b.nonneg 1
  change observe b .second ≤ observe b .top^1*b.mass at h
  rw [pow_one,narrowBox_mass] at h
  have hl := narrowBox_second_lower M r hM.le hr
  nlinarith

/-- Every joint collection of moment thresholds strictly below the concentrated mass limit is feasible.
Use: discharges the nonemptiness premise in the general moment minimizer existence theorem.
Article: jacobi, Proposition D.2.
Proof: exponential continuity gives a sufficiently small positive half-width
meeting both thresholds; the explicit narrow box meets the mass bound exactly. -/
theorem moment_feasible {M : ℝ} (hM : 0 < M) (S : Set Observation) (T : Observation → ℝ)
    (hT : ∀ i ∈ S, T i < match i with | .second => M^2 | .top => M) :
    ∃ m : Density, m.mass ≤ M ∧ ∀ i ∈ S, T i ≤ observe m i := by
  -- Both strict conditions hold in a neighborhood of zero; choose one positive width in their intersection.
  have hs : ∀ᶠ r : ℝ in 𝓝 0, ∀ i ∈ S,
      T i < match i with | .second => exp (-4*r)*M^2 | .top => exp (-4*r)*M := by
    apply (Filter.eventually_all_finite S.toFinite).mpr
    intro i hi
    have hc : Continuous (fun r : ℝ => match i with
        | .second => exp (-4*r)*M^2 | .top => exp (-4*r)*M) := by cases i <;> fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hT i hi))
  have hs' : ∀ᶠ r : ℝ in 𝓝[Ioi 0] 0, (∀ i ∈ S,
      T i < match i with | .second => exp (-4*r)*M^2 | .top => exp (-4*r)*M) ∧ r ∈ Ioi 0 :=
    (hs.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨r,hr,hrr⟩ := hs'.exists
  refine ⟨narrowBox M r hM.le hrr,(narrowBox_mass M r hM.le hrr).le,fun i hi => ?_⟩
  cases i with
  | second => exact (hr .second hi).le.trans (narrowBox_second_lower M r hM.le hrr)
  | top => exact (hr .top hi).le.trans (narrowBox_top_lower M r hM hrr)

end
end jacobi.Variational
