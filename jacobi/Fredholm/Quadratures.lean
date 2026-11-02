import jacobi.Fredholm.Parameters
import jacobi.Elliptic.RatioEndpoints

/-!
Article: jacobi, Theorem D.7.
Mass and energy reuse the actual common i2 and i3 integrals. The new Green
and root integrands have genuine uniform square-root endpoint majorants,
including tau=1. Every printed quantity is therefore a finite real integral.
Source: the already verified common weight inequalities in jacobi.
Use: the interior branch is selected by mass(tau,chi)=s*M.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The normalized actual Fredholm mass quadrature.
Use: the interior branch is selected by mass(tau,chi)=s*M.
Article: jacobi, Theorem D.7.
-/
def mass (t c : ℝ) : ℝ := (3/2:ℝ)*c*i2 t c

/-- The normalized actual Fredholm energy quadrature.
Use: both alternatives in the exact minimum use (2*s)^(-3/2)*energy.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def energy (t c : ℝ) : ℝ := (3*c)^(3/2:ℝ)/sqrt t*i3 t c

/-- The original nonsingular Green density in the normalized core coordinate.
Use: defines the determinant quadrature and its true continuous-parameter integral.
Article: jacobi, Theorem D.7.
-/
def determinantWeight (t c v : ℝ) : ℝ := L t v/(nu t c v*sqrt (P t c v))

/-- The normalized actual regularized determinant quadrature, including its exterior contribution.
Use: both branches satisfy determinant(tau,chi)=d_s(Lambda).
Article: jacobi, Theorem D.7.
-/
def determinant (t c : ℝ) : ℝ :=
  log ((1-c*t)/(1-c))+t*c*(∫ v in (0:ℝ)..1,determinantWeight t c v)-mass t c

/-- The actual normalized root-mass quadrature of a Fredholm profile.
Use: records all state integrals in the source's candidate-profile lemma.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def root (t c : ℝ) : ℝ := sqrt (3*c*t)*(∫ v in (0:ℝ)..1,v/sqrt (P t c v))

/-- The normalized energy-to-mass shape ratio.
Use: its two partial monotonicities give uniqueness on an actual constant-mass curve.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def shapeRatio (t c : ℝ) : ℝ := i3 t c/(sqrt t*(i2 t c)^(3/2:ℝ))

/-- The original determinant quadrature has a positive uniform integrable majorant through the full-support endpoint.
Use: proves its true convergence and controls local parameter differentiation.
Article: jacobi, Theorem D.7.
Proof: the common polynomial estimate gives sqrt(P)>=L*sqrt(1-v),
and N_chi>=1-chi>0. Cancel only positive actual factors in the open unit interval. -/
theorem determinantWeight_bound {t c v : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Ico (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) : 0≤determinantWeight t c v ∧
      determinantWeight t c v≤(1-c)⁻¹*endpointWeight v := by
  -- The sharper L² lower bound handles tau=1 without a false uniform lower bound for P(0).
  have hc' : c∈Icc (0:ℝ) 1 := ⟨hc.1,hc.2.le⟩
  have hL := (L_bounds ht ⟨hv.1.le,hv.2.le⟩).1
  have hLp : 0<L t v := hv.1.trans_le hL
  have hN := nu_bounds ht hc ⟨hv.1.le,hv.2.le⟩
  have hNp : 0<nu t c v := hN.1.trans_le hN.2.1
  have hS := sqrt_pos.mpr (P_pos ht hc' hv)
  have he := sqrt_pos.mpr (sub_pos.mpr hv.2)
  have hp : (1-v)*(L t v)^2≤P t c v := by
    have hw := weights_bounds ht hc' ⟨hv.1.le,hv.2.le⟩
    exact mul_le_mul_of_nonneg_left (hw.2.1.trans hw.2.2.1) (by linarith [hv.2])
  have hs := sqrt_le_sqrt hp
  rw [sqrt_mul (by linarith [hv.2]),sqrt_sq hLp.le] at hs
  refine ⟨div_nonneg hLp.le (mul_nonneg hNp.le hS.le),?_⟩
  unfold determinantWeight endpointWeight
  apply (div_le_iff₀ (mul_pos hNp hS)).mpr
  have hh := mul_le_mul_of_nonneg_left hs hNp.le
  have hbound : L t v*(1-c)*sqrt (1-v)≤nu t c v*sqrt (P t c v) := by
    nlinarith [mul_le_mul_of_nonneg_right hN.2.1 (mul_nonneg he.le hLp.le)]
  calc
    L t v = ((1-c)⁻¹*(sqrt (1-v))⁻¹)*(L t v*(1-c)*sqrt (1-v)) := by field_simp [hN.1.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (mul_nonneg (inv_nonneg.mpr hN.1.le) (inv_nonneg.mpr he.le))

/-- The determinant core quadrature is a genuine finite interval integral, including tau=1.
Use: validates the exact determinant value and all subsequent comparisons.
Article: jacobi, Theorem D.7.
Proof: the original measurable integrand is dominated on (0,1) by the
proved integrable endpoint majorant; the two endpoint representatives are null. -/
theorem determinantWeight_integrable {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Ico (0:ℝ) 1) :
    IntervalIntegrable (determinantWeight t c) volume 0 1 := by
  -- No smoothness of a candidate profile is needed to justify this integral.
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mpr
  have hi := ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp endpointWeight_integrable).const_mul ((1-c)⁻¹)
  have hm : Measurable (determinantWeight t c) := by unfold determinantWeight nu L P r q; fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (determinantWeight_bound ht hc hv).1]
  exact (determinantWeight_bound ht hc hv).2

/-- The normalized mass is strictly positive at every nonzero actual Fredholm parameter pair.
Use: the constant-mass curve and energy normalization divide only by positive quantities.
Article: jacobi, Theorem D.7.
Proof: the existing actual i2 quadrature is positive, and its scalar coefficient is positive. -/
theorem mass_pos {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Ioc (0:ℝ) 1) : 0<mass t c :=
  mul_pos (mul_pos (by norm_num) hc.1) (i2_pos ht ⟨hc.1.le,hc.2⟩)

/-- The zero-amplitude edge gives exactly zero normalized mass and determinant.
Use: the constant-mass defining curve starts at zero as chi tends to zero.
Article: jacobi, Theorem D.7.
Proof: substitute chi=0 in the literal normalized formulas. -/
theorem zero_parameter (t : ℝ) : mass t 0=0 ∧ determinant t 0=0 := by simp [mass,determinant]

end
end jacobi.Fredholm
