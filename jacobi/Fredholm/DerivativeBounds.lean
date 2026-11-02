import jacobi.Fredholm.MassOrder
import jacobi.Fredholm.RootIntegral

/-!
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
The genuine shape and determinant derivatives of the original state weight
share a parameter-uniform integrable endpoint majorant. The estimates retain
the physical endpoint tau=1 without assuming an extension beyond that domain.
Source: the common elliptic polynomial bounds, positivity and root-weight majorant.
Use: supplies the parameter-uniform integrable derivative majorant in Lemma mono2.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The original shape logarithmic derivative is bounded by the reciprocal coordinate.
Use: supplies the parameter-uniform integrable derivative majorant in Lemma mono2.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: N<=2*L, v<=L and L²<=r imply v*N<=2*r;
all rational denominators are strictly positive on the actual interval. -/
theorem psi_bound {t c v : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) : psi t c v≤1/v := by
  -- Compare the numerator after multiplying only by the positive physical denominators.
  have hw := weights_bounds ht hc ⟨hv.1.le,hv.2.le⟩
  have hL := (L_bounds ht ⟨hv.1.le,hv.2.le⟩).1
  have hLp : 0≤L t v := hv.1.le.trans hL
  apply (le_div_iff₀ hv.1).mpr
  unfold psi
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos (by norm_num) (r_pos ht hc ⟨hv.1,hv.2.le⟩))).mpr
  unfold N
  nlinarith [mul_le_mul_of_nonneg_left hL hLp,
    mul_nonneg (mul_nonneg hc.1 (pow_nonneg hv.1.le 3)) hv.1.le]

/-- The original shape derivative of the second-power weight has a uniform integrable majorant.
Use: justifies shape differentiation of both i2 and i3 throughout the interior parameter interval.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: write the derivative as (v*psi)*(v/sqrt(P)); the factors are
nonnegative and bounded by one and the endpoint weight respectively. -/
theorem shapeWeight_bound {t c v : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) :
    0≤psi t c v*quadratureWeight t c v ∧
      psi t c v*quadratureWeight t c v≤endpointWeight v := by
  -- Split off one coordinate power to retain the sharp bound at tau=1.
  have hp := (psi_pos ht hc ⟨hv.1,hv.2.le⟩).le
  have hw := rootWeight_bound ht hc hv
  have hpsi : psi t c v*v≤1 := (le_div_iff₀ hv.1).mp (psi_bound ht hc hv)
  have he : psi t c v*quadratureWeight t c v=(psi t c v*v)*(v/sqrt (P t c v)) := by
    unfold quadratureWeight
    ring
  rw [he]
  exact ⟨mul_nonneg (mul_nonneg hp hv.1.le) hw.1,
    (mul_le_mul hpsi hw.2 hw.1 (by norm_num)).trans_eq (one_mul _)⟩

/-- The original determinant-parameter derivative has the same uniform endpoint majorant.
Use: differentiates the actual i2 and i3 with respect to chi, including tau=1.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: tau/2, h and the actual weight are nonnegative and bounded by
one, one and the endpoint weight respectively. -/
theorem parameterWeight_bound {t c v : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) :
    |-(t/2)*(v^3/r t c v)*quadratureWeight t c v|≤endpointWeight v := by
  -- Each nonnegative factor has its own uniform bound on the closed physical box.
  have hh := h_bounds ht hc hv
  have hw := quadratureWeight_bound ht hc hv
  rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg (div_nonneg ht.1 (by norm_num : (0:ℝ)≤2)),
    abs_of_nonneg hh.1,abs_of_nonneg hw.1]
  have hcoef : t/2*(v^3/r t c v)≤1 := by
    have ht2 : t/2≤1 := by linarith [ht.2]
    exact (mul_le_mul ht2 (hh.2.trans hv.2.le) hh.1 (by norm_num)).trans_eq (one_mul 1)
  exact (mul_le_mul hcoef hw.2 hw.1 (by norm_num)).trans_eq (one_mul _)

end
end jacobi.Fredholm
