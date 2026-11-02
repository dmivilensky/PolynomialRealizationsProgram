import jacobi.Analysis.WeakSecondRegularity

/-!
Article: jacobi, Proposition 2.2.
The positive-part function has exactly a unit point source as weak second
derivative. Subtracting it turns the Green equation into a continuous forcing.
Source: integration by parts on the half line and the fundamental theorem of calculus.
Use: weak_point_source_regular produces actual C2 branches with precisely
the derivative jump required for the original exponential Green coordinate.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter Function MeasureTheory
open scoped Topology

/-- The positive part has distributional second derivative equal to the
unit point source, tested against arbitrary compactly supported C2 functions.
Use: weak_point_source_regular removes exactly the source from the actual
target Green column before applying continuous weak derivative regularity.
Article: jacobi, Proposition 2.2.
Source: integration by parts on (t,infinity).
Proof: the positive part is linear on its positive half line. Integration
by parts leaves the integral of the test derivative, whose value is minus
the test at t. Compact support removes the infinite endpoint term. -/
theorem positive_part_test {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (t : ℝ) :
    (∫ s : ℝ,max (s-t) 0*deriv (deriv g) s)=g t := by
  have hgd : ContDiff ℝ 1 (deriv g) := (show ContDiff ℝ (1+1) g from hg).deriv'
  have hgd2 := hgd.continuous_deriv (by norm_num)
  have hi1 : Integrable (fun s => (s-t)*deriv (deriv g) s) :=
    ((continuous_id.sub continuous_const).mul hgd2).integrable_of_hasCompactSupport
      hc.deriv.deriv.mul_left
  have hi2 : Integrable (fun s => (1:ℝ)*deriv g s) :=
    (continuous_const.mul hgd.continuous).integrable_of_hasCompactSupport hc.deriv.mul_left
  have hz : Tendsto (fun s => (s-t)*deriv g s) (𝓝[>] t) (𝓝 0) := by
    have hcont : Continuous (fun s : ℝ => (s-t)*deriv g s) :=
      (continuous_id.sub continuous_const).mul hgd.continuous
    have hh := hcont.tendsto t
    simpa only [sub_self,zero_mul] using hh.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun s => (s-t)*deriv g s) atTop (𝓝 0) := by
    have hh : HasCompactSupport (fun s => (s-t)*deriv g s) := hc.deriv.mul_left
    rw [hasCompactSupport_iff_eventuallyEq,Filter.coclosedCompact_eq_cocompact] at hh
    exact (hh.filter_mono atTop_le_cocompact).tendsto
  have he := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun s (_ : s∈Ioi t) => (hasDerivAt_id s).sub_const t)
    (fun s (_ : s∈Ioi t) => (hgd.differentiable (by norm_num) s).hasDerivAt)
    hi1.integrableOn hi2.integrableOn hz ht
  have hrestrict : (∫ s : ℝ,max (s-t) 0*deriv (deriv g) s)=
      ∫ s in Ioi t,(s-t)*deriv (deriv g) s := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ioi t) (fun s hs => by
        rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt hs)),zero_mul])]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    change max (s-t) 0*_= (s-t)*_
    rw [max_eq_left (sub_nonneg.mpr hs.le)]
  simp only [id_eq] at he
  rw [hrestrict,he]
  simp only [zero_sub,sub_zero,one_mul]
  rw [HasCompactSupport.integral_Ioi_deriv_eq (hg.of_le (by norm_num)) hc,neg_neg]

/-- A continuous kernel with a unit weak Green source is locally the
difference of a genuine C2 primitive and the positive part at its source.
Use: target Green columns have actual homogeneous C2 branches off their
source, with left slope minus right slope equal to exactly one.
Article: jacobi, Proposition 2.2.
Source: local regularity of the scalar one-dimensional Green equation.
Proof: add the positive part to cancel the unit source, then invoke the
proved weak second derivative theorem with continuous forcing. -/
theorem weak_point_source_regular {f Q : ℝ → ℝ} {a b t : ℝ}
    (hab : a<b) (hf : Continuous f) (hQ : Continuous Q)
    (hw : ∀ g : ℝ → ℝ,ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b →
        (∫ s : ℝ,f s*deriv (deriv g) s)=(∫ s : ℝ,Q s*g s)-g t) :
    ∃ F : ℝ → ℝ,ContDiff ℝ 2 F ∧ (∀ x,deriv (deriv F) x=Q x) ∧
      ∀ x∈Ioo a b,f x=F x-max (x-t) 0 := by
  have hc : Continuous (fun x : ℝ => f x+max (x-t) 0) :=
    hf.add ((continuous_id.sub continuous_const).max continuous_const)
  have he (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
      (hs : tsupport g ⊆ Ioo a b) :
      (∫ s : ℝ,(f s+max (s-t) 0)*deriv (deriv g) s)=∫ s : ℝ,Q s*g s := by
    have hgd : ContDiff ℝ 1 (deriv g) := (show ContDiff ℝ (1+1) g from hg).deriv'
    have hi1 : Integrable (fun s => f s*deriv (deriv g) s) :=
      (hf.mul (hgd.continuous_deriv (by norm_num))).integrable_of_hasCompactSupport
        hcg.deriv.deriv.mul_left
    have hi2 : Integrable (fun s => max (s-t) 0*deriv (deriv g) s) :=
      (((continuous_id.sub continuous_const).max continuous_const).mul
        (hgd.continuous_deriv (by norm_num))).integrable_of_hasCompactSupport
          hcg.deriv.deriv.mul_left
    simp_rw [add_mul]
    rw [integral_add hi1 hi2,hw g hg hcg hs,positive_part_test hg hcg t,sub_add_cancel]
  obtain ⟨F,hF,hFd,hFe⟩ := weak_second_regular hab hc hQ he
  exact ⟨F,hF,hFd,fun x hx => by linarith [hFe hx]⟩

end
end jacobi.Analysis
