import jacobi.Fredholm.WeightedDifferentiation
import jacobi.Fredholm.EnvelopeTransport

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
The original Green core has actual parameter derivatives, obtained by
factoring out its parameter-independent endpoint singularity.
Source: ordinary quotient rules and compact dominated differentiation.
Use: permits dominated differentiation of the actual determinant quadrature.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The continuous coefficient after removing the common turning-endpoint weight from the Green core.
Use: permits dominated differentiation of the actual determinant quadrature.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def coreCoefficient (t c v : ℝ) : ℝ := t*c*L t v/nu t c v/sqrt (r t c v)

/-- The original core coefficient has the asserted ordinary shape derivative.
Use: supplies the pointwise derivative required by dominated differentiation.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the affine quotient and the inverse square root;
the literal polynomial derivative is minus N. Positive r justifies the
square root chain rule and the exact normalized cancellation. -/
theorem coreCoefficient_shape_hasDerivAt {t c v : ℝ} (hr : 0<r t c v)
    (hn : nu t c v≠0) :
    HasDerivAt (fun u => coreCoefficient u c v) (coreShapeSlope t c v/sqrt (r t c v)) t := by
  -- The coefficient is smooth even at the spatial endpoints below full support.
  have hL : HasDerivAt (fun u => L u v) (v-1) t := by
    convert ((hasDerivAt_id t).mul_const (v-1)).const_add 1 using 1 <;>
      (try funext u) <;> ((try dsimp [L]); ring)
  have hnD : HasDerivAt (fun u => nu u c v) (-c*(1-v)) t := by
    convert ((hasDerivAt_id t).const_mul (c*(1-v))).const_sub 1 using 1 <;>
      (try funext u) <;> ((try dsimp [nu]); ring)
  have hrD : HasDerivAt (fun u => r u c v) (-N t c v) t := by
    convert ((((hasDerivAt_id t).pow 2).const_sub 1).mul_const v |>.add_const (v^2)).add
      (((hasDerivAt_id t).const_sub 1).pow 2) |>.add
      ((hasDerivAt_id t).const_mul (c*v^3)) using 1 <;>
      (try funext u) <;> (dsimp [r,q,N,L]; ring)
  have h := (((hasDerivAt_id t).mul_const c).mul (hL.div hnD hn)).mul
    ((hrD.sqrt hr.ne').inv (sqrt_pos.mpr hr).ne')
  convert h using 1
  · funext u
    dsimp [coreCoefficient]
    ring
  · dsimp [coreShapeSlope,psi]
    field_simp
    rw [sq_sqrt hr.le]
    unfold nu L
    ring

/-- The original Green core coefficient has its ordinary determinant-parameter derivative.
Use: differentiates the actual compact-core determinant, rather than a formal numerator.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the affine denominator and cubic factor have literal polynomial
derivatives. Apply product, quotient and square-root rules and normalize
using the true positive square-root square. -/
theorem coreCoefficient_parameter_hasDerivAt {t c v : ℝ} (hr : 0<r t c v)
    (hn : nu t c v≠0) :
    HasDerivAt (fun u => coreCoefficient t u v) (coreParameterSlope t c v/sqrt (r t c v)) c := by
  -- The same smooth coefficient controls the actual chi derivative.
  have hnD : HasDerivAt (fun u => nu t u v) (-t*(1-v)) c := by
    convert ((hasDerivAt_id c).mul_const (t*(1-v))).const_sub 1 using 1 <;>
      (try funext u) <;> ((try dsimp [nu]); ring)
  have hrD : HasDerivAt (fun u => r t u v) (t*v^3) c := by
    convert ((hasDerivAt_id c).mul_const (t*v^3)).const_add (q t v) using 1 <;>
      (try funext u) <;> ((try dsimp [r]); ring)
  have h := (((hasDerivAt_id c).const_mul (t*L t v)).div hnD hn).mul
    ((hrD.sqrt hr.ne').inv (sqrt_pos.mpr hr).ne')
  convert h using 1
  · funext u
    dsimp [coreCoefficient]
    ring
  · dsimp [coreParameterSlope]
    field_simp
    rw [sq_sqrt hr.le]
    ring

/-- The literal Green core equals its continuous coefficient times the common endpoint weight.
Use: restores the original determinant integral after compact differentiation.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: factor sqrt(P)=sqrt(1-v)*sqrt(r) and rearrange the real divisions. -/
theorem coreCoefficient_weight {t c v : ℝ} (hv : v<1) :
    coreCoefficient t c v*endpointWeight v=t*c*determinantWeight t c v := by
  unfold coreCoefficient endpointWeight determinantWeight P
  rw [sqrt_mul (sub_pos.mpr hv).le]
  ring

/-- Both genuine shape and determinant-parameter core derivatives are continuous on every compact physical rectangle.
Use: compactness supplies the integrable dominating constants for the true envelope derivatives.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: all polynomial coefficients are continuous. The original affine
denominator and r are strictly positive on the compact-core physical
domain, including both spatial endpoints, so every displayed quotient is continuous. -/
theorem core_slopes_continuous {a b c : ℝ} (ha : 0<a) (hb : b<1)
    (hc : c∈Ico (0:ℝ) 1) :
    ContinuousOn (fun p : ℝ×ℝ => coreShapeSlope p.1 c p.2/sqrt (r p.1 c p.2))
      (Icc a b×ˢIcc (0:ℝ) 1) := by
  -- Positivity is local in the physical parameters and uniform by compactness.
  intro p hp
  have ht : p.1∈Ioo (0:ℝ) 1 := ⟨ha.trans_le hp.1.1,hp.1.2.trans_lt hb⟩
  have hr := r_closed_pos ht ⟨hc.1,hc.2.le⟩ hp.2
  have hn := nu_bounds ⟨ht.1.le,ht.2.le⟩ hc hp.2
  have hnpos : 0<1-c*p.1*(1-p.2) := hn.1.trans_le hn.2.1
  have hrpos : 0<q p.1 p.2+c*p.1*p.2^3 := hr
  apply ContinuousAt.continuousWithinAt
  simp only [coreShapeSlope,nu,L,psi,N,r,q] at *
  fun_prop (disch := positivity)

/-- The genuine chi core derivative is continuous on every compact interior parameter rectangle.
Use: provides an integrable local majorant without numerical constants.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the original affine and square-root denominators are positive
throughout the closed rectangle. Continuity follows by the ordinary
algebra rules for these literal expressions. -/
theorem core_parameter_slope_continuous {a b t : ℝ} (ha : 0≤a) (hb : b<1)
    (ht : t∈Ioo (0:ℝ) 1) :
    ContinuousOn (fun p : ℝ×ℝ => coreParameterSlope t p.1 p.2/sqrt (r t p.1 p.2))
      (Icc a b×ˢIcc (0:ℝ) 1) := by
  -- The closed spatial endpoints are harmless after the common weight is removed.
  intro p hp
  have hc : p.1∈Ico (0:ℝ) 1 := ⟨ha.trans hp.1.1,hp.1.2.trans_lt hb⟩
  have hr := r_closed_pos ht ⟨hc.1,hc.2.le⟩ hp.2
  have hn := nu_bounds ⟨ht.1.le,ht.2.le⟩ hc hp.2
  have hnpos : 0<1-p.1*t*(1-p.2) := hn.1.trans_le hn.2.1
  apply ContinuousAt.continuousWithinAt
  unfold coreParameterSlope nu L r q at *
  fun_prop (disch := positivity)

/-- The nonsingular Green core coefficient is continuous on the closed coordinate interval.
Use: establishes integrability at the base point for actual parameter differentiation.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the two original denominators are positive, including at zero,
so their inverses and the square root preserve continuity. -/
theorem coreCoefficient_continuous {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ico (0:ℝ) 1) :
    ContinuousOn (coreCoefficient t c) (Icc (0:ℝ) 1) := by
  -- Positivity at zero uses tau<1, rather than the strictly interior spatial bound.
  intro v hv
  have hr := r_closed_pos ht ⟨hc.1,hc.2.le⟩ hv
  have hn := nu_bounds ⟨ht.1.le,ht.2.le⟩ hc hv
  have hnpos : 0<1-c*t*(1-v) := hn.1.trans_le hn.2.1
  apply ContinuousAt.continuousWithinAt
  unfold coreCoefficient nu L r q at *
  fun_prop (disch := positivity)

/-- Restoring the original square-root denominator preserves the actual weighted integral.
Use: expresses all differentiated coefficients in the source's literal quadratures.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the factorization holds away from the two null endpoints;
sqrt(1-v) is positive there, and rearrangement is ordinary real algebra. -/
theorem weighted_integral_eq (f : ℝ → ℝ) (t c : ℝ) :
    (∫ v in (0:ℝ)..1,f v/sqrt (r t c v)*endpointWeight v)=
      ∫ v in (0:ℝ)..1,f v/sqrt (P t c v) := by
  -- Changing the endpoint representatives does not change an interval integral.
  apply intervalIntegral.integral_congr_uIoo
  intro v hv
  have hv' : v∈Ioo (0:ℝ) 1 := by
    simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hv
  dsimp only
  unfold endpointWeight P
  rw [sqrt_mul (sub_pos.mpr hv'.2).le]
  ring

/-- The weighted continuous coefficient integrates to the original determinant core for all real parameters.
Use: converts the differentiated auxiliary representation back to the actual function in the article.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: use the pointwise factorization off the null endpoints, then
move the constant tau*chi outside the genuine interval integral. -/
theorem core_integral_eq (t c : ℝ) :
    (∫ v in (0:ℝ)..1,coreCoefficient t c v*endpointWeight v)=
      t*c*(∫ v in (0:ℝ)..1,determinantWeight t c v) := by
  -- This identity is global, so it can rewrite the function being differentiated.
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro v hv
  exact coreCoefficient_weight (by
    have : v∈Ioo (0:ℝ) 1 := by
      simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hv
    exact this.2)

/-- The original determinant core has a genuine ordinary shape derivative on the compact-support branch.
Use: provides the determinant partial needed by the full envelope identity.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: apply compact dominated differentiation on a closed interval
strictly inside the physical shape domain, then restore the original
integrand and its actual derivative numerator. -/
theorem core_shape_hasDerivAt {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    IntervalIntegrable (fun v => coreShapeSlope t c v/sqrt (P t c v)) volume 0 1 ∧
    HasDerivAt (fun u => u*c*(∫ v in (0:ℝ)..1,determinantWeight u c v))
      (∫ v in (0:ℝ)..1,coreShapeSlope t c v/sqrt (P t c v)) t := by
  -- Compactness bounds the derivative before the parameter-independent singular weight is restored.
  have h := compact_weight_hasDerivAt
    (fun u v => coreCoefficient u c v) (fun u v => coreShapeSlope u c v/sqrt (r u c v))
    (fun _ => by unfold coreCoefficient nu L r q; fun_prop)
    (fun _ => by simp only [coreShapeSlope,nu,L,psi,N,r,q]; fun_prop)
    (a := t/2) (b := (1+t)/2) (by constructor <;> linarith [ht.1,ht.2])
    (coreCoefficient_continuous ht ⟨hc.1.le,hc.2⟩)
    (core_slopes_continuous (by linarith [ht.1]) (by linarith [ht.2]) ⟨hc.1.le,hc.2⟩)
    (fun u hu v hv => coreCoefficient_shape_hasDerivAt
      (r_closed_pos ⟨by linarith [hu.1,ht.1],by linarith [hu.2,ht.2]⟩
        ⟨hc.1.le,hc.2.le⟩ ⟨hv.1.le,hv.2.le⟩)
      (by
        have hn := nu_bounds (t := u) (c := c) ⟨by linarith [hu.1,ht.1],by linarith [hu.2,ht.2]⟩
          ⟨hc.1.le,hc.2⟩ ⟨hv.1.le,hv.2.le⟩
        exact (hn.1.trans_le hn.2.1).ne'))
  refine ⟨h.1.congr_uIoo (fun v hv => ?_),?_⟩
  · dsimp only
    unfold endpointWeight P
    rw [sqrt_mul (sub_nonneg.mpr (by
      have : v∈Ioo (0:ℝ) 1 := by simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hv
      exact this.2.le))]
    ring
  · simpa only [core_integral_eq,weighted_integral_eq] using h.2

/-- The original determinant core has a genuine ordinary chi derivative on the compact-support branch.
Use: supplies the second determinant partial for the actual envelope one-form.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: keep tau fixed and apply compact dominated differentiation in
an interior chi interval. The verified coefficient derivative has no
spatial denominator zero on this compact rectangle. Restore the literal core. -/
theorem core_parameter_hasDerivAt {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    IntervalIntegrable (fun v => coreParameterSlope t c v/sqrt (P t c v)) volume 0 1 ∧
    HasDerivAt (fun u => t*u*(∫ v in (0:ℝ)..1,determinantWeight t u v))
      (∫ v in (0:ℝ)..1,coreParameterSlope t c v/sqrt (P t c v)) c := by
  -- The common endpoint factor remains unchanged as chi varies.
  have h := compact_weight_hasDerivAt
    (fun u v => coreCoefficient t u v) (fun u v => coreParameterSlope t u v/sqrt (r t u v))
    (fun _ => by unfold coreCoefficient nu L r q; fun_prop)
    (fun _ => by unfold coreParameterSlope nu L r q; fun_prop)
    (a := c/2) (b := (1+c)/2) (by constructor <;> linarith [hc.1,hc.2])
    (coreCoefficient_continuous ht ⟨hc.1.le,hc.2⟩)
    (core_parameter_slope_continuous (by linarith [hc.1]) (by linarith [hc.2]) ht)
    (fun u hu v hv => coreCoefficient_parameter_hasDerivAt
      (r_closed_pos ht ⟨by linarith [hu.1,hc.1],by linarith [hu.2,hc.2]⟩ ⟨hv.1.le,hv.2.le⟩)
      (by
        have hn := nu_bounds (c := u) ⟨ht.1.le,ht.2.le⟩
          ⟨by linarith [hu.1,hc.1],by linarith [hu.2,hc.2]⟩ ⟨hv.1.le,hv.2.le⟩
        exact (hn.1.trans_le hn.2.1).ne'))
  refine ⟨h.1.congr_uIoo (fun v hv => ?_),?_⟩
  · dsimp only
    unfold endpointWeight P
    rw [sqrt_mul (sub_nonneg.mpr (by
      have : v∈Ioo (0:ℝ) 1 := by simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hv
      exact this.2.le))]
    ring
  · simpa only [core_integral_eq,weighted_integral_eq] using h.2

end
end jacobi.Fredholm
