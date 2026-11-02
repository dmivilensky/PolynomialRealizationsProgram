import jacobi.Young.EnergyDual

/-!
Article: jacobi, Lemma D.3.
Positive spatial rescaling preserves the actual locally absolutely continuous
H1 representative, including its genuine a.e. derivative. The proof transfers
null sets explicitly and derives local absolute continuity from the rescaled
fundamental theorem. This avoids imposing C1 regularity on a weak H1 derivative.
Source: Lebesgue change of variables and the absolutely continuous FTC.
Use: rescales an arbitrary Sobolev slope in the full finite-energy Green construction.
-/
namespace jacobi.Young
noncomputable section
open Real MeasureTheory Filter Set chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false

/-- Spatial rescaling preserves real L2 membership without a continuity hypothesis.
Use: rescales an arbitrary Sobolev slope in the full finite-energy Green construction.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the scalar map preserves null sets and its Jacobian preserves finiteness of the squared integral. -/
theorem memLp_two_scale {f : ℝ → ℝ} (hf : MemLp f 2 volume) {t : ℝ} (ht : t≠0) :
    MemLp (fun x => f (t*x)) 2 volume := by
  have hq : Measure.QuasiMeasurePreserving (fun x : ℝ => t*x) volume volume :=
    Measure.quasiMeasurePreserving_smul volume ht
  apply (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable.comp_quasiMeasurePreserving hq)).mpr
  exact (integrable_comp_mul_left_iff (fun x => f x^2) ht).mpr hf.integrable_sq

/-- Every actual H1 representative rescales with its correct weak derivative.
Use: the non-L1 Green potential can be put in the article's exponent-two normalization.
Article: jacobi, Lemma D.3.
Proof: L2 membership follows by change of variables. The rescaled FTC
represents the value as an integral of its rescaled slope, proving local
absolute continuity. The scalar map's proved null-set preservation transfers
the original a.e. derivative before applying the chain rule. -/
theorem sobolev_scale {f d : ℝ → ℝ} (h : SobolevRegular f d) {t : ℝ} (ht : t≠0) (c : ℝ) :
    SobolevRegular (fun x => c*f (t*x)) (fun x => c*t*d (t*x)) := by
  -- The same rescaled slope occurs in the L2 proof, the FTC and the a.e. chain rule.
  have hd := memLp_two_scale h.derivative_memLp ht
  have hq : Measure.QuasiMeasurePreserving (fun x : ℝ => t*x) volume volume :=
    Measure.quasiMeasurePreserving_smul volume ht
  refine ⟨(memLp_two_scale h.value_memLp ht).const_mul c,hd.const_mul (c*t),?_,?_⟩
  · intro a b
    have hi : IntervalIntegrable (fun x => c*t*d (t*x)) volume a b :=
      (((hd.const_mul (c*t)).locallyIntegrable (by norm_num)).integrableOn_isCompact
        isCompact_uIcc).intervalIntegrable
    have ha := hi.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : a∈uIcc a b)
    have he (x : ℝ) : c*f (t*x)=c*f (t*a)+(∫ y in a..x, c*t*d (t*y)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left _ ht,
        smul_eq_mul,locallyAC_integral_eq_sub h.locally_ac h.derivative_ae]
      field_simp
      ring
    apply ((contDiff_const.contDiffOn.absolutelyContinuousOnInterval).add ha).congr
    intro x _
    exact (he x).symm
  · filter_upwards [hq.ae h.derivative_ae] with x hx
    convert (hx.comp x ((hasDerivAt_id x).const_mul t)).const_mul c using 1
    · funext y; rfl
    · ring

end
end jacobi.Young
