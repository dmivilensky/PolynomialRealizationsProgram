import jacobi.Fredholm.ClosedForm

/-!
Article: jacobi, Theorem D.7.
The original zero-amplitude and zero-shape endpoints are evaluated.
Dominated continuity in chi gives strict positivity of the determinant
for every physical pair, before a candidate density is constructed.
Source: the exact common second-moment endpoint and dominated convergence.
Use: proves strict feasibility of every arbitrary physical parameter pair for the direct method.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The zero-shape mass and determinant equal the concentrated scalar mass and determinant.
Use: proves strict feasibility of every arbitrary physical parameter pair for the direct method.
Article: jacobi, Theorem D.7.
Proof: at tau=0 the second quadrature is independent of chi and equals
two thirds. Substitute it in the original formulas and simplify the actual logarithm. -/
theorem zero_shape (c : ℝ) :
    mass 0 c=c ∧ determinant 0 c=-log (1-c)-c := by
  -- The common exact endpoint integral is reused rather than recomputed.
  have hI : i2 0 c=i2 0 0 := by simp only [i2,quadratureWeight,P,r,q,mul_zero,zero_mul,add_zero]
  have hm : mass 0 c=c := by rw [mass,hI,i2_zero]; ring
  refine ⟨hm,?_⟩
  simp only [determinant,mul_zero,zero_mul,sub_zero,add_zero,one_div,log_inv,hm]

/-- The original determinant is continuous in chi on every compact physical chi interval, including zero.
Use: positivity and scalar feasibility of arbitrary printed candidate parameters do not assume a density realization.
Article: jacobi, Theorem D.7.
Proof: on chi<=b<1 the original core integrand has the common
integrable majorant endpointWeight/(1-b). Its pointwise denominator
is positive. Apply dominated convergence, then combine the true
continuous mass and logarithmic terms. -/
theorem determinant_parameter_continuous {t b : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hb : b∈Ico (0:ℝ) 1) :
    ContinuousOn (determinant t) (Icc (0:ℝ) b) := by
  -- Uniform domination is local in chi and includes the full-support shape.
  have hi := ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp
    endpointWeight_integrable).const_mul ((1-b)⁻¹)
  have hcore := MeasureTheory.continuousOn_of_dominated
    (μ := volume.restrict (Ioo (0:ℝ) 1)) (s := Icc (0:ℝ) b)
    (F := fun c v => determinantWeight t c v) (bound := fun v => (1-b)⁻¹*endpointWeight v)
    (fun _ _ => (show Measurable (determinantWeight t _) by
      unfold determinantWeight L nu P r q; fun_prop).aestronglyMeasurable)
    (fun c hc => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      have hcp : c∈Ico (0:ℝ) 1 := ⟨hc.1,hc.2.trans_lt hb.2⟩
      rw [Real.norm_eq_abs,abs_of_nonneg (determinantWeight_bound ht hcp hv).1]
      apply (determinantWeight_bound ht hcp hv).2.trans
      apply mul_le_mul_of_nonneg_right _ (by unfold endpointWeight; positivity)
      simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hb.2)
        (show 1-b≤1-c by linarith [hc.2])) hi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      intro c hc
      have hcp : c∈Ico (0:ℝ) 1 := ⟨hc.1,hc.2.trans_lt hb.2⟩
      have hN := nu_bounds ht hcp ⟨hv.1.le,hv.2.le⟩
      have hN0 : 0<1-c*t*(1-v) := hN.1.trans_le hN.2.1
      have hP := P_pos ht ⟨hcp.1,hcp.2.le⟩ hv
      apply ContinuousAt.continuousWithinAt
      unfold determinantWeight L nu P r q at *
      fun_prop (disch := positivity))
  have hcore' : ContinuousOn (fun c => ∫ v in (0:ℝ)..1,determinantWeight t c v) (Icc (0:ℝ) b) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      integral_Ioc_eq_integral_Ioo] using hcore
  have hlog : ContinuousOn (fun c => log ((1-c*t)/(1-c))) (Icc (0:ℝ) b) := by
    intro c hc
    have hc1 : 0<1-c := by linarith [hc.2,hb.2]
    have hnum : 0<1-c*t := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hc.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hM : ContinuousOn (mass t) (Icc (0:ℝ) b) := (mass_parameter_continuous ht).mono (fun _ hc => ⟨hc.1,hc.2.trans hb.2.le⟩)
  exact (hlog.add ((continuousOn_const.mul continuousOn_id).mul hcore')).sub hM

/-- The literal determinant is strictly positive at every nonzero physical candidate pair.
Use: the existing optimizer existence theorem applies to arbitrary candidate parameters, independently of an edge spectrum.
Article: jacobi, Theorem D.7.
Proof: the original chi-zero value is zero. On a closed interval from
zero to the given chi, dominated continuity and the proved strictly
positive interior derivative give strict increase. The free case uses
its separately proved ordinary derivative. -/
theorem determinant_pos {t c : ℝ} (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    0<determinant t c := by
  -- The determinant's sign is proved before constructing its proposed density.
  have hmono : StrictMonoOn (determinant t) (Icc (0:ℝ) c) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 c) (determinant_parameter_continuous
      ⟨ht.1.le,ht.2⟩ ⟨hc.1.le,hc.2⟩)
    intro k hk
    have hk' : k∈Ioo (0:ℝ) c := by simpa only [interior_Icc] using hk
    have hkp : k∈Ioo (0:ℝ) 1 := ⟨hk'.1,hk'.2.trans hc.2⟩
    rcases lt_or_eq_of_le ht.2 with hti | hte
    · exact determinant_parameter_deriv_pos ⟨ht.1,hti⟩ hkp
    · rw [hte]
      exact free_determinant_deriv_pos hkp
  have h := hmono ⟨le_rfl,hc.1.le⟩ ⟨hc.1.le,le_rfl⟩ hc.1
  simpa only [(zero_parameter t).2] using h

end
end jacobi.Fredholm
