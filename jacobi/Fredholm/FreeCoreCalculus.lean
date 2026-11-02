import jacobi.Fredholm.FreeEnvelopePrimitive

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
The actual full-support Green core has a continuous coefficient after
the removable zero-coordinate factor is cancelled. Compact dominated
differentiation applies to that coefficient on the original unit interval.
Source: r(1,chi,v)=v^2*(1+chi*v) and ordinary quotient rules.
Use: differentiates the free branch without inverting r at its zero endpoint.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The continuous coefficient of the true full-support Green integral.
Use: differentiates the free branch without inverting r at its zero endpoint.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def freeCoreCoefficient (c v : ℝ) : ℝ := c/nu 1 c v/sqrt (1+c*v)

/-- The numerator of the actual free-core chi derivative after removing its regular square root.
Use: a continuous local derivative coefficient for dominated differentiation.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def freeCoreSlope (c v : ℝ) : ℝ :=
  1/nu 1 c v+c*(1-v)/(nu 1 c v)^2-c*v/(2*nu 1 c v*(1+c*v))

/-- The regularized free core has its literal ordinary chi derivative.
Use: supplies the genuine derivative under the original free-branch integral.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the quotient and the positive inverse square root.
Clear the actual nonzero affine denominators and use the same square-root square. -/
theorem freeCoreCoefficient_hasDerivAt {c v : ℝ} (hn : nu 1 c v≠0) (hr : 0<1+c*v) :
    HasDerivAt (fun u => freeCoreCoefficient u v) (freeCoreSlope c v/sqrt (1+c*v)) c := by
  -- Only the regular factor 1+chi*v occurs in this square-root derivative.
  have hN : HasDerivAt (fun u => nu 1 u v) (-(1-v)) c := by
    convert ((hasDerivAt_id c).mul_const (1-v)).const_sub 1 using 1 <;>
      (try funext u) <;> ((try dsimp [nu]); ring)
  have h := ((hasDerivAt_id c).div hN hn).mul
    (((((hasDerivAt_id c).mul_const v).const_add 1).sqrt hr.ne').inv (sqrt_pos.mpr hr).ne')
  convert h using 1
  · funext u
    dsimp [freeCoreCoefficient]
    ring
  · have hr' : 0<1+v*c := by simpa only [mul_comm c v] using hr
    simp only [id_eq,Pi.inv_apply,Pi.div_apply]
    unfold freeCoreSlope
    simp only [mul_comm c v]
    field_simp [hn,hr'.ne',(sqrt_pos.mpr hr').ne']
    unfold nu
    rw [sq_sqrt hr.le]
    ring

/-- The regularized free coefficient is exactly the original Green core off the null endpoints.
Use: identifies the differentiated function with the article's determinant, for every chi.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the true square-root factorization cancels positive v. The other
real divisions may be zero; the identity still holds with Lean's total division. -/
theorem freeCoreCoefficient_weight (c : ℝ) {v : ℝ} (hv : v∈Ioo (0:ℝ) 1) :
    freeCoreCoefficient c v*endpointWeight v=c*determinantWeight 1 c v := by
  unfold freeCoreCoefficient endpointWeight determinantWeight
  rw [free_sqrt hv]
  simp only [L,sub_self,zero_add,one_mul]
  field_simp [hv.1.ne']

/-- The regularized free derivative is the original chi-core derivative on the open integration interval.
Use: restores the original derivative numerator after dominated differentiation.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: use r=v^2*(1+chi*v), clear the positive spatial and affine factors,
and check the remaining real polynomial identity exactly. -/
theorem freeCoreSlope_weight {c v : ℝ} (hc : c∈Ioo (0:ℝ) 1) (hv : v∈Ioo (0:ℝ) 1) :
    freeCoreSlope c v/sqrt (1+c*v)*endpointWeight v=
      coreParameterSlope 1 c v/sqrt (P 1 c v) := by
  -- No equality at the arbitrary zero-endpoint representative is needed.
  have hn := nu_bounds (by norm_num : (1:ℝ)∈Icc 0 1) ⟨hc.1.le,hc.2⟩ ⟨hv.1.le,hv.2.le⟩
  have hn0 := (hn.1.trans_le hn.2.1).ne'
  have hR : 0<1+c*v := by nlinarith [mul_pos hc.1 hv.1]
  have hr : r 1 c v=v^2*(1+c*v) := by unfold r q; ring
  rw [free_sqrt hv]
  unfold freeCoreSlope coreParameterSlope endpointWeight
  rw [hr]
  field_simp [hv.1.ne',hn0,hR.ne']
  unfold L nu
  ring

/-- The genuine full-support Green core has its ordinary chi derivative and an integrable original derivative integrand.
Use: closes every analytic differentiation premise of the free envelope and its unique determinant root.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: regularize the removable zero-coordinate factor. Its derivative
is continuous on a compact chi-coordinate rectangle with positive
denominators. Apply dominated differentiation and restore both original
integrands away from the two null endpoint representatives. -/
theorem free_core_hasDerivAt {c : ℝ} (hc : c∈Ioo (0:ℝ) 1) :
    IntervalIntegrable (fun v => coreParameterSlope 1 c v/sqrt (P 1 c v)) volume 0 1 ∧
      HasDerivAt (fun u => u*(∫ v in (0:ℝ)..1,determinantWeight 1 u v))
        (∫ v in (0:ℝ)..1,coreParameterSlope 1 c v/sqrt (P 1 c v)) c := by
  -- The compact rectangle excludes chi=1 but includes both spatial endpoints.
  have hn (u v : ℝ) (hu : u∈Ico (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) : 0<nu 1 u v := by
    have h := nu_bounds (by norm_num : (1:ℝ)∈Icc 0 1) hu hv
    exact h.1.trans_le h.2.1
  have hr (u v : ℝ) (hu : 0≤u) (hv : 0≤v) : 0<1+u*v := by nlinarith [mul_nonneg hu hv]
  have h := compact_weight_hasDerivAt
    freeCoreCoefficient (fun u v => freeCoreSlope u v/sqrt (1+u*v))
    (u := c)
    (fun _ => by unfold freeCoreCoefficient nu; fun_prop)
    (fun _ => by unfold freeCoreSlope nu; fun_prop)
    (a := c/2) (b := (1+c)/2) (by constructor <;> linarith [hc.1,hc.2])
    (by
      intro v hv
      have hn0 : 0<1-c*1*(1-v) := hn c v ⟨hc.1.le,hc.2⟩ hv
      have hr0 := hr c v hc.1.le hv.1
      apply ContinuousAt.continuousWithinAt
      unfold freeCoreCoefficient nu
      fun_prop (disch := positivity))
    (by
      intro p hp
      have hu : p.1∈Ico (0:ℝ) 1 := ⟨by linarith [hp.1.1,hc.1],by linarith [hp.1.2,hc.2]⟩
      have hn0 : 0<1-p.1*1*(1-p.2) := hn p.1 p.2 hu hp.2
      have hr0 := hr p.1 p.2 hu.1 hp.2.1
      apply ContinuousAt.continuousWithinAt
      unfold freeCoreSlope nu
      fun_prop (disch := positivity))
    (fun u hu v hv => freeCoreCoefficient_hasDerivAt
      (hn u v ⟨by linarith [hu.1,hc.1],by linarith [hu.2,hc.2]⟩ ⟨hv.1.le,hv.2.le⟩).ne'
      (hr u v (by linarith [hu.1,hc.1]) hv.1.le))
  have heq (u : ℝ) : (∫ v in (0:ℝ)..1,freeCoreCoefficient u v*endpointWeight v)=
      u*(∫ v in (0:ℝ)..1,determinantWeight 1 u v) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro v hv
    exact freeCoreCoefficient_weight u (by
      simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hv)
  have hd : (∫ v in (0:ℝ)..1,freeCoreSlope c v/sqrt (1+c*v)*endpointWeight v)=
      ∫ v in (0:ℝ)..1,coreParameterSlope 1 c v/sqrt (P 1 c v) :=
    intervalIntegral.integral_congr_uIoo (fun v hv => freeCoreSlope_weight hc (by
      simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hv))
  refine ⟨h.1.congr_uIoo (fun v hv => freeCoreSlope_weight hc (by
    simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hv)),?_⟩
  simpa only [heq,hd] using h.2

end
end jacobi.Fredholm
