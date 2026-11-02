import jacobi.Fredholm.Coordinate
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
The true zero first integral yields the negative normalized Jacobian on the
actual positive-density half-core. The Lebesgue change of variables then
evaluates every observable vanishing off that core, on both support branches.
Source: the genuine Green first integral and mathlib's one-dimensional Jacobian theorem.
Use: converts the actual optimizer's first integral into the printed square-root Jacobian.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Variational jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The literal clipped Green phase has exactly the common normalized elliptic polynomial on its core.
Use: converts the actual optimizer's first integral into the printed square-root Jacobian.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: the affine coordinate gives both Green factors, and the positive
parameter square-root amplitude has its defining square. Clear the proved
nonzero parameter denominators and use the exact polynomial identity for P. -/
theorem phase_affine {t c v : ℝ} (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1)
    (hv : 0≤v) :
    phase (amplitude t c) (jacobi.Fredholm.edge t c)
      (jacobi.Fredholm.edge t c+delta t c*v)=(2*peak c-1)^2*P t c v := by
  -- The clipped core is precisely the nonnegative normalized coordinate branch.
  have hd := (parameter_bounds ht hc).1
  have hmax : max (jacobi.Fredholm.edge t c+delta t c*v- jacobi.Fredholm.edge t c) 0=delta t c*v := by
    rw [add_sub_cancel_left,max_eq_left (mul_nonneg hd.le hv)]
  have hsqrt := sq_sqrt (div_pos (mul_pos (by norm_num : (0:ℝ)<3) hc.1) ht.1).le
  unfold phase amplitude
  rw [hmax,div_pow,hsqrt,P_identity]
  unfold jacobi.Fredholm.edge delta peak nu L
  field_simp [ht.1.ne',hc.1.ne',sub_ne_zero.mpr hc.2.ne']
  ring

/-- The actual coordinate has the exact negative printed Jacobian at every point of its genuine positive half-core.
Use: proves the coefficient in the whole-line quadrature from the original optimizer.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: substitute the actual inverse parameters into the genuine first
integral. The normalized polynomial is positive at every interior level.
Strict Green descent selects its negative square-root branch and fixes
the scalar factor (2*g_0-1)/delta=2/tau. -/
theorem Optimizer.coordinate_jacobian {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    {x : ℝ} (hx : x∈P.core hs) :
    HasDerivAt (P.coordinate hs) (-(2/P.tau hs)*sqrt (jacobi.Elliptic.P (P.tau hs) (P.chi hs) (P.coordinate hs x))) x := by
  -- The branch sign comes from the actual operator optimizer, not a chosen inverse.
  have hparams := P.parameters hs
  have hv : P.coordinate hs x∈Ioo (0:ℝ) 1 := by
    rw [← P.coordinate_image hs]
    exact mem_image_of_mem _ hx
  have hpos := sqrt_pos.mpr (P_pos ⟨hparams.1.1.le,hparams.1.2⟩ ⟨hparams.2.1.le,hparams.2.2.le⟩ hv)
  have hfirst := P.first_integral hs x
  have hinv := P.inverse_parameters hs
  have hphase := phase_affine hparams.1 hparams.2 hv.1.le
  rw [P.amplitude_eq hs,hinv.1,hinv.2.1,hinv.2.2,← P.coordinate_affine hs x] at hphase
  rw [hphase] at hfirst
  have hg : 0<2*P.g hs.le 0-1 := by
    have hh := (P.shape hs).1
    have he := (P.parameter_signs hs).1
    linarith
  have hd : 0<P.g hs.le 0-P.edge := sub_pos.mpr (P.shape hs).1
  have hneg := (P.shape hs).2.2.2 x hx.1
  have hroot := sq_sqrt (P_pos ⟨hparams.1.1.le,hparams.1.2⟩ ⟨hparams.2.1.le,hparams.2.2.le⟩ hv).le
  have hbranch : deriv (P.g hs.le) x=-(2*P.g hs.le 0-1)*sqrt (jacobi.Elliptic.P (P.tau hs) (P.chi hs) (P.coordinate hs x)) := by
    nlinarith [mul_pos hg hpos]
  convert P.coordinate_hasDerivAt hs x using 1
  rw [hbranch]
  unfold Optimizer.tau
  field_simp [hd.ne',hg.ne']

/-- The genuine optimizing profile has the exact printed whole-line quadrature for every core observable.
Use: supplies actual mass, energy and root-mass integrals without any assumed candidate certificate.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: on the measurable positive half-core the actual coordinate is
injective and maps onto (0,1). Its proved negative Jacobian gives the
factor 2/tau. Evenness doubles the half-line integral, and the observable
vanishes on the complement of the positive core. -/
theorem Optimizer.quadrature {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    (F : ℝ → ℝ) (hF : ∀ v,v≤0 → F v=0) :
    (∫ x,F (P.coordinate hs x))=P.tau hs*
      (∫ v in (0:ℝ)..1,F v/sqrt (jacobi.Elliptic.P (P.tau hs) (P.chi hs) v)) := by
  -- The genuine map and its genuine half-core discharge every Jacobian premise.
  let f := P.coordinate hs
  let W := fun v : ℝ => sqrt (jacobi.Elliptic.P (P.tau hs) (P.chi hs) v)
  have hder (x : ℝ) (hx : x∈P.core hs) :
      HasDerivWithinAt f (-(2/P.tau hs)*W (f x)) (P.core hs) x :=
    (P.coordinate_jacobian hs hx).hasDerivWithinAt
  have hinj : InjOn f (P.core hs) :=
    ((P.coordinate_strictAnti hs).mono fun _ hx => (mem_Ioi.mp hx.1).le).injOn
  have hchange := integral_image_eq_integral_abs_deriv_smul (P.core_measurable hs) hder hinj
    (fun v => F v/W v)
  rw [P.coordinate_image hs] at hchange
  have hjac (x : ℝ) (hx : x∈P.core hs) :
      |-(2/P.tau hs)*W (f x)| • (F (f x)/W (f x))=(2/P.tau hs)*F (f x) := by
    have hv : f x∈Ioo (0:ℝ) 1 := by rw [← P.coordinate_image hs]; exact mem_image_of_mem _ hx
    have hp := P.parameters hs
    have hw : 0<W (f x) := sqrt_pos.mpr (P_pos ⟨hp.1.1.le,hp.1.2⟩ ⟨hp.2.1.le,hp.2.2.le⟩ hv)
    have hc : 0<2/P.tau hs := div_pos (by norm_num) hp.1.1
    rw [smul_eq_mul,abs_of_neg (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hw)]
    field_simp
  have hright : (∫ x in P.core hs,|-(2/P.tau hs)*W (f x)| • (F (f x)/W (f x)))=
      (2/P.tau hs)*(∫ x in P.core hs,F (f x)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (P.core_measurable hs) hjac
  rw [hright] at hchange
  have habs (x : ℝ) : f |x|=f x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx]
      exact (P.coordinate_regular hs).2.1 x
  have hfull : (∫ x,F (f x))=2*(∫ x in Ioi (0:ℝ),F (f x)) := by
    simpa only [habs] using (integral_comp_abs (f := fun x => F (f x)))
  have hrestrict : (∫ x in Ioi (0:ℝ),F (f x))=∫ x in P.core hs,F (f x) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi inter_subset_left
    intro x hx
    apply hF
    by_contra! hpos
    exact hx.2 ⟨hx.1,hpos⟩
  rw [hfull,hrestrict]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]
  rw [hchange]
  field_simp [(P.parameters hs).1.1.ne']

end
end jacobi.Fredholm
