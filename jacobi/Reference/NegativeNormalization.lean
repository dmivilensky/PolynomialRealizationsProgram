import jacobi.Reference.NegativeLaplaceRepresentation
import jacobi.Reference.LaplaceTail

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The leading coefficient of the original reference beta integral is
computed by Watson's lemma with every analytic premise discharged for
the actual sine density. The opposite endpoint is allowed to be singular;
its actual contribution is exponentially small by genuine integrability.
Use: identifies the leading negative-energy coefficient of the original reference solution in wave_imaginary_leading.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized sine density has the exact leading Laplace coefficient Gamma(gamma)/B(gamma,gamma).
Use: identifies the leading negative-energy coefficient of the original reference solution in wave_imaginary_leading.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Watson's leading endpoint lemma, proved here in TruncatedLaplace and LaplaceTail.
Proof: on the first half of the original physical integration interval,
the exact regular coefficient is continuous and bounded. Its value at
zero is the original inverse beta normalization. The remaining actual
singular-endpoint integral is exponentially negligible. -/
theorem normalizedSine_laplace_limit {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) :
    Tendsto (fun x : ℝ => x^(gamma a)*
      ((betaNormalization (gamma a))⁻¹*(Real.sin (Real.pi*t)/Real.pi)^(1-gamma a)*
        (∫ s in (0:ℝ)..t,sineWeight (gamma a) t s*Real.exp (-(x*s)))))
      atTop (𝓝 (Real.Gamma (gamma a)/(betaNormalization (gamma a)))) := by
  -- The regular prefix coefficient belongs to the already defined original normalized sine density.
  let A := t/2
  let P := (betaNormalization (gamma a))⁻¹*(Real.sin (Real.pi*t)/Real.pi)^(1-gamma a)
  let D : ℝ → ℝ := fun s => P*sineWeight (gamma a) t s
  let h : ℝ → ℝ := fun s => betaDensityCoefficient a (t,s)
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hA : 0<A := by dsimp [A]; linarith [ht.1]
  have hAt : A<t := by dsimp [A]; linarith [ht.1]
  have hDm : IntervalIntegrable D volume 0 t := (sineWeight_integrable hg ht).const_mul P
  have hhm : Measurable h := by dsimp [h,betaDensityCoefficient]; fun_prop
  have hhc : ContinuousAt h 0 := betaDensityCoefficient_continuousAt ht ⟨le_rfl,ht.1⟩
  have hhI : ContinuousOn h (Icc (0:ℝ) A) := fun s hs =>
    (betaDensityCoefficient_continuousAt ht ⟨hs.1,hs.2.trans_lt hAt⟩).continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hhI
  have hhb : ∃ M : ℝ,0≤M ∧ ∀ s∈Icc (0:ℝ) A,|h s|≤M := by
    refine ⟨max M 0,le_max_right _ _,fun s hs => ?_⟩
    have hv : |h s|≤M := by simpa only [Real.norm_eq_abs] using hM s hs
    exact hv.trans (le_max_left _ _)
  have hpref := truncated_laplace_limit hg hA hhm hhc hhb
  rw [show h 0=(betaNormalization (gamma a))⁻¹ from betaDensityCoefficient_zero a ht,
    ← div_eq_mul_inv] at hpref
  have hprefix : Tendsto (fun x : ℝ => x^(gamma a)*
      (∫ s in (0:ℝ)..A,Real.exp (-(x*s))*D s))
      atTop (𝓝 (Real.Gamma (gamma a)/(betaNormalization (gamma a)))) := by
    apply hpref.congr'
    filter_upwards with x
    congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le hA.le
    intro s hs
    dsimp [D,P,h]
    rw [mul_assoc,← betaDensityCoefficient_identity a ht ⟨hs.1,hs.2.trans hAt⟩]
  have hsub : uIcc A t⊆uIcc (0:ℝ) t := by
    rw [uIcc_of_le hAt.le,uIcc_of_le ht.1.le]
    exact Icc_subset_Icc hA.le le_rfl
  have htail := laplace_tail_limit hA hAt.le (gamma a) (hDm.mono_set hsub)
  have hsum := hprefix.add htail
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards with x
  have hF : IntervalIntegrable (fun s : ℝ => Real.exp (-(x*s))*D s) volume 0 t :=
    hDm.continuousOn_mul (by fun_prop)
  have hsub0 : uIcc (0:ℝ) A⊆uIcc (0:ℝ) t := by
    rw [uIcc_of_le hA.le,uIcc_of_le ht.1.le]
    exact Icc_subset_Icc le_rfl hAt.le
  have hadj := intervalIntegral.integral_add_adjacent_intervals (hF.mono_set hsub0) (hF.mono_set hsub)
  rw [← mul_add,hadj]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp [D,P]
  ring

/-- The original imaginary-frequency reference function has its exact leading endpoint asymptotic at every physical interior point.
Use: supplies the actual leading coefficient of Delta_tau on the negative axis, independently of an assumed complex Gamma asymptotic.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the proved exact Laplace representation uses x=2*y. Its
leading coefficient is the genuine Gamma integral divided by the
original beta normalization; the positive dilation contributes 2^(-gamma). -/
theorem wave_imaginary_leading {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) :
    Tendsto (fun y : ℝ => y^(gamma a)*Real.exp (-(t*y))*(wave a (Complex.I*(y:ℂ)) t).re)
      atTop (𝓝 (Real.Gamma (gamma a)/((2:ℝ)^(gamma a)*betaNormalization (gamma a)))) := by
  -- The original normalization is preserved through the genuine positive frequency dilation.
  have htwo : Tendsto (fun y : ℝ => 2*y) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (B/2)] with y hy
    linarith
  have hh := ((normalizedSine_laplace_limit ha ht).comp htwo).const_mul ((2:ℝ)^(gamma a))⁻¹
  have he : ((2:ℝ)^(gamma a))⁻¹*(Real.Gamma (gamma a)/betaNormalization (gamma a))=
      Real.Gamma (gamma a)/((2:ℝ)^(gamma a)*betaNormalization (gamma a)) := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  dsimp only [Function.comp_apply]
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hy.le]
  simp only [← mul_assoc,inv_mul_cancel₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne',one_mul]
  rw [mul_assoc (y^(gamma a)) (Real.exp (-(t*y))),wave_imaginary_laplace ha ht]
  ring

end
end jacobi.Reference
