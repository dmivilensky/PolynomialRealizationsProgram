import jacobi.Fredholm.Moments

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Integration by parts is justified for the actual singular Fredholm weight.
The primitive is written with sqrt(1-v) in the numerator, so its turning
endpoint is genuinely continuous. A continuous coefficient times the
already integrable endpoint weight proves convergence of its derivative.
Source: the fundamental theorem of calculus for integrable endpoint derivatives.
Use: the weighted divergence in the envelope integration-by-parts identity.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The literal spatial derivative of the common polynomial factor r.
Use: the weighted divergence in the envelope integration-by-parts identity.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def spatialSlope (t c v : ℝ) : ℝ := 2*v+(1-t^2)+3*c*t*v^2

/-- The weighted divergence corresponding to the primitive U*sqrt(1-v)/sqrt(r).
Use: expresses the difference of the Fredholm, mass and energy parameter derivatives as an integrable exact derivative.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def weightedDivergence (t c v U D : ℝ) : ℝ :=
  (1-v)*D-U/2-(1-v)*U*spatialSlope t c v/(2*r t c v)

/-- The literal spatial polynomial has its exact ordinary derivative.
Use: differentiates the genuine endpoint primitive in the envelope identity.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate each polynomial term and collect its actual coefficients. -/
theorem r_spatial_hasDerivAt (t c v : ℝ) : HasDerivAt (r t c) (spatialSlope t c v) v := by
  convert ((((hasDerivAt_id v).pow 2).add ((hasDerivAt_id v).mul_const (1-t^2))).add_const ((1-t)^2)).add
    (((hasDerivAt_id v).pow 3).const_mul (c*t)) using 1 <;>
    (try funext x) <;> (dsimp [r,q,spatialSlope]; ring)

/-- Below the full-support shape, r is positive even at both integration endpoints.
Use: gives actual continuous denominator inverses in the interior envelope argument.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: L>=1-tau>0 and the common verified bound r>=L² apply throughout [0,1]. -/
theorem r_closed_pos {t c v : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1)
    (hv : v∈Icc (0:ℝ) 1) : 0<r t c v := by
  have hw := weights_bounds ⟨ht.1.le,ht.2.le⟩ hc hv
  have hL : 0<L t v := by unfold L; nlinarith [ht.2,mul_nonneg ht.1.le hv.1]
  exact (sq_pos_of_pos hL).trans_le (hw.2.1.trans hw.2.2.1)

/-- The continuous endpoint primitive has the exact weighted divergence as its genuine derivative.
Use: the envelope integration-by-parts proof retains the actual sqrt(P) denominator.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the original product and quotient at an interior
coordinate. Positivity licenses both square-root derivatives; their actual
squares and P=(1-v)*r give the exact normalized expression. -/
theorem divergence_hasDerivAt {t c v : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) {U : ℝ → ℝ} {D : ℝ} (hU : HasDerivAt U D v) :
    HasDerivAt (fun x => U x*sqrt (1-x)/sqrt (r t c x))
      (weightedDivergence t c v (U v) D/sqrt (P t c v)) v := by
  -- Square-root cancellations use their positive values at this same actual interior point.
  have he : 0<1-v := sub_pos.mpr hv.2
  have hr := r_pos ht hc ⟨hv.1,hv.2.le⟩
  have hse := sqrt_pos.mpr he
  have hsr := sqrt_pos.mpr hr
  have h := (hU.mul (((hasDerivAt_id v).const_sub 1).sqrt he.ne')).div
    ((r_spatial_hasDerivAt t c v).sqrt hr.ne') hsr.ne'
  convert h using 1
  · rfl
  unfold weightedDivergence P
  rw [sqrt_mul he.le]
  dsimp only [id_eq,Pi.mul_apply]
  field_simp
  ring_nf
  simp only [sq_sqrt he.le,sq_sqrt hr.le]
  ring

/-- The actual weighted divergence integrates to its exact nonsingular boundary value on the compact-core parameter domain.
Use: removes the interior envelope remainder by a genuine convergent integral identity.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the primitive is continuous on [0,1], with zero value at one.
Its derivative is an actual continuous coefficient times the integrable
endpoint weight. The fundamental theorem of calculus applies, and
sqrt(r(0))=1-tau gives the precise remaining boundary value. -/
theorem divergence_integral {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1)
    (U D : ℝ → ℝ) (hU : ContinuousOn U (Icc (0:ℝ) 1))
    (hD : ContinuousOn D (Icc (0:ℝ) 1))
    (hder : ∀ v∈Ioo (0:ℝ) 1,HasDerivAt U (D v) v) :
    (∫ v in (0:ℝ)..1,weightedDivergence t c v (U v) (D v)/sqrt (P t c v))=-U 0/(1-t) := by
  -- Continuity and integrability are established before evaluating the singular-endpoint primitive.
  let F := fun v : ℝ => U v*sqrt (1-v)/sqrt (r t c v)
  have hr (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : r t c v≠0 := (r_closed_pos ht hc hv).ne'
  have hs (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : sqrt (r t c v)≠0 := (sqrt_pos.mpr (r_closed_pos ht hc hv)).ne'
  have hrc : ContinuousOn (r t c) (Icc (0:ℝ) 1) := by unfold r q; fun_prop
  have hec : ContinuousOn (fun v : ℝ => 1-v) (Icc (0:ℝ) 1) := continuousOn_const.sub continuousOn_id
  have hsc : ContinuousOn (spatialSlope t c) (Icc (0:ℝ) 1) := by unfold spatialSlope; fun_prop
  have hFc : ContinuousOn F (Icc (0:ℝ) 1) := (hU.mul hec.sqrt).div hrc.sqrt hs
  have hcoef : ContinuousOn (fun v => weightedDivergence t c v (U v) (D v)/sqrt (r t c v)) (Icc (0:ℝ) 1) :=
    (((hec.mul hD).sub (hU.div_const 2)).sub
      (((hec.mul hU).mul hsc).div (continuousOn_const.mul hrc)
        (fun v hv => mul_ne_zero (by norm_num) (hr v hv)))).div hrc.sqrt hs
  have hi : IntervalIntegrable (fun v => weightedDivergence t c v (U v) (D v)/sqrt (P t c v)) volume 0 1 := by
    have hcoef' : ContinuousOn (fun v => weightedDivergence t c v (U v) (D v)/sqrt (r t c v)) (uIcc (0:ℝ) 1) := by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hcoef
    apply (endpointWeight_integrable.continuousOn_mul hcoef').congr_uIoo
    intro v hv
    have hv' : v∈Ioo (0:ℝ) 1 := by simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hv
    dsimp only
    unfold P endpointWeight
    rw [sqrt_mul (sub_pos.mpr hv'.2).le]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1) hFc
    (fun v hv => divergence_hasDerivAt ⟨ht.1.le,ht.2.le⟩ hc hv (hder v hv)) hi
  rw [h]
  dsimp only [F]
  have he : 0≤1-t := (sub_pos.mpr ht.2).le
  simp [r,q,sqrt_sq he,neg_div]

end
end jacobi.Fredholm
