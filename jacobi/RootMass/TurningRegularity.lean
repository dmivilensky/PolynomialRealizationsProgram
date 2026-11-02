import jacobi.RootMass.Substitution

/-!
Article: jacobi, Appendix D.5.
The inverse substitution proves convergence of the genuine turning integrals,
not just an identity between possibly undefined real integrals. In particular
the inverse square-root radicand is integrable at the upper turning endpoint.
Source: the actual inverse curve and integrability in the Lebesgue Jacobian theorem.
Use: continuous state observables compose continuously on the actual compact integration domain.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse-coordinate state remains in the full closed turning interval at every integration point.
Use: continuous state observables compose continuously on the actual compact integration domain.
Article: jacobi, Appendix D.5.
Proof: the actual inverse is at least one and the proved decreasing curve is bounded above by its u=0 value. -/
theorem node_mem {a y u : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) (hu : u∈Icc (0:ℝ) 1) :
    node a ha y u∈Icc (1:ℝ) (inverse a ha y) := by
  refine ⟨inverse_ge_one a ha _,?_⟩
  have hh := (node_strictAnti ha hy).antitoneOn (show (0:ℝ)∈Icc 0 1 by norm_num) hu hu.1
  rwa [node_zero] at hh

/-- Every continuous state observable has a genuinely convergent turning quadrature.
Use: validates all source quadratures at the singular turning endpoint, including general F in the profile lemma.
Article: jacobi, Appendix D.5.
Proof: the actual inverse curve composes F continuously on [0,1]. Its
nonsingular rational weight is continuous there, hence integrable. The
actual injective Jacobian theorem transfers that integrability to the true turning interval. -/
theorem turning_integrable {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Icc (1:ℝ) (inverse a ha y))) :
    IntegrableOn (fun n => F n*(3*n^2-1)/(n*sqrt (radicand a y n))) (Ioo (1:ℝ) (inverse a ha y)) := by
  -- Convergence is transferred by the actual measure substitution, with no improper-integral convention.
  have hder (u : ℝ) (hu : u∈Ioo (0:ℝ) 1) :
      HasDerivWithinAt (node a ha y) (-2*y*u/psiSlope a (node a ha y u)) (Ioo (0:ℝ) 1) u :=
    (node_hasDerivAt ha hy hu).hasDerivWithinAt
  have hh := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hder
    ((node_strictAnti ha hy).mono Ioo_subset_Icc_self).injOn
    (fun n => F n*(3*n^2-1)/(n*sqrt (radicand a y n)))
  rw [node_image ha hy] at hh
  apply hh.mpr
  have hn : Continuous (node a ha y) := (node_continuous a ha).comp (continuous_const.prodMk continuous_id)
  have hFc := hF.comp hn.continuousOn (fun _ hu => node_mem ha hy hu)
  have hw : Continuous (fun u => (p a (node a ha y u))^2/((node a ha y u)^3*q a (node a ha y u))) := by
    simpa only [W,pow_zero,one_mul,Function.comp_def,id_eq] using
      (W_node_continuous 0 a ha).comp (continuous_const.prodMk continuous_id)
  have hc : ContinuousOn (fun u => 2*y*(F (node a ha y u)*(p a (node a ha y u))^2/
      ((node a ha y u)^3*q a (node a ha y u)))) (Icc (0:ℝ) 1) := by
    convert (hFc.mul hw.continuousOn).const_mul (2*y) using 1
    funext u
    dsimp only [Pi.mul_apply,Function.comp_def]
    ring
  have hi : IntegrableOn (fun u => 2*y*(F (node a ha y u)*(p a (node a ha y u))^2/
      ((node a ha y u)^3*q a (node a ha y u)))) (Ioo (0:ℝ) 1) volume :=
    (hc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  simpa only [smul_eq_mul] using (node_jacobian ha hy hu F).symm

/-- The actual inverse-square-root turning singularity is Lebesgue integrable on its whole finite interval.
Use: justifies the simple turning endpoint in every compact-profile quadrature.
Article: jacobi, Appendix D.5.
Proof: apply the proved genuine observable-integrability theorem to
F(n)=n/(3*n²-1), a continuous function on [1,n_0]. Its exact weight cancels
to 1/sqrt(R_y); endpoint null sets do not alter integrability. -/
theorem inverse_sqrt_radicand_integrable {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) :
    IntegrableOn (fun n => 1/sqrt (radicand a y n)) (Icc (1:ℝ) (inverse a ha y)) := by
  -- The turning endpoint is included after proving integrability on the actual open interval.
  have hF : ContinuousOn (fun n : ℝ => n/(3*n^2-1)) (Icc (1:ℝ) (inverse a ha y)) :=
    continuousOn_id.div (by fun_prop) (fun n hn => by nlinarith [hn.1])
  have hi := turning_integrable ha hy _ hF
  have he : IntegrableOn (fun n => 1/sqrt (radicand a y n)) (Ioo (1:ℝ) (inverse a ha y)) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with n hn
    have hn0 : 0<n := zero_lt_one.trans hn.1
    have hd : 3*n^2-1≠0 := by nlinarith [hn.1]
    have hd' : n^2*3-1≠0 := by nlinarith [hn.1]
    field_simp [hd']
  exact (integrableOn_Icc_iff_integrableOn_Ioo (by finiteness) (by finiteness)).mpr he

end
end jacobi.RootMass
