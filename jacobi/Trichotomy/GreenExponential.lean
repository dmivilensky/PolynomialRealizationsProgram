import jacobi.Trichotomy.GreenFactors
import jacobi.Trichotomy.PackingCoordinate

/-!
Article: jacobi, Proposition 2.2.
The actual positive Green factors have Wronskian one. Their logarithmic
ratio therefore has derivative 1/phi_alpha and differs from the original
packing coordinate by a constant only. This identifies the full original
kernel, with its exact printed scale.
Source: the elementary logarithmic Green-coordinate transformation.
Use: the packed-density operator is unitarily conjugate to 2*H_alpha^(-1)
by this actual kernel identity and the proved coordinate substitution.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The actual real-coordinate Green diagonal equals half the original profile.
Use: targetGreen_exponential identifies the logarithmic-factor Jacobian
with the already constructed intrinsic packing coordinate.
Article: jacobi, Proposition 2.2.
Proof: projection fixes the original physical point, so the proved spectral
diagonal identity applies unchanged. -/
theorem physicalGreen_diagonal (a : ℝ) (ha : -1<a) {t : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) :
    2*physicalGreenKernel a ha t t=physicalProfile a ha t := by
  rw [physicalProfile_eq a ha ⟨ht.1.le,ht.2.le⟩]
  simpa only [physicalGreenKernel,projIcc_of_mem (by norm_num) ⟨ht.1.le,ht.2.le⟩] using
    targetGreen_diagonal a ha ⟨t,⟨ht.1.le,ht.2.le⟩⟩

/-- The original full target Green kernel is exactly the exponential kernel
in its original intrinsic coordinate, at every pair of interior points.
Use: supplies the kernel identity for the genuine packed-density spectral
identification, preserving the entire nonzero spectrum with multiplicities.
Article: jacobi, Proposition 2.2.
Proof: on an interval containing the two points, the positive C2 factors
have Wronskian one. Their logarithmic ratio and the actual packing coordinate
have identical derivatives. Exponentiating their difference gives the
ordered Green product; symmetry covers the opposite ordering. -/
theorem targetGreen_exponential (a : ℝ) (ha : -1<a) {t s : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hs : s∈Ioo (0:ℝ) 1) :
    2*physicalGreenKernel a ha t s=
      sqrt (physicalProfile a ha t*physicalProfile a ha s)*
        exp (-|packingCoordinate a ha t-packingCoordinate a ha s|) := by
  have ordered (t s : ℝ) (ht : t∈Ioo (0:ℝ) 1) (hs : s∈Ioo (0:ℝ) 1)
      (hts : t≤s) :
      2*physicalGreenKernel a ha t s=
        sqrt (physicalProfile a ha t*physicalProfile a ha s)*
          exp (-|packingCoordinate a ha t-packingCoordinate a ha s|) := by
    let l := t/2
    let r := (s+1)/2
    have hl : 0<l := by dsimp [l]; linarith [ht.1]
    have hr : r<1 := by dsimp [r]; linarith [hs.2]
    have hlr : l<r := by dsimp [l,r]; linarith [hts]
    have htu : t∈Ioo l r := by dsimp [l,r]; constructor <;> linarith [ht.1,hs.2,hts]
    have hsu : s∈Ioo l r := by dsimp [l,r]; constructor <;> linarith [ht.1,hs.2,hts]
    obtain ⟨L,R,hLc,hRc,hpos,hW,hprod⟩ := targetGreen_local_factors a ha hl hr hlr
    have hin (x : ℝ) (hx : x∈Ioo l r) : x∈Ioo (0:ℝ) 1 :=
      ⟨hl.trans hx.1,hx.2.trans hr⟩
    have hphi (x : ℝ) (hx : x∈Ioo l r) : physicalProfile a ha x=2*(L x*R x) := by
      rw [← physicalGreen_diagonal a ha (hin x hx),hprod x hx x hx le_rfl]
    -- The normalized Wronskian makes this logarithmic coordinate have
    -- exactly the original reciprocal-profile derivative.
    let χ := fun x => (log (L x)-log (R x))/2
    have hχ (x : ℝ) (hx : x∈Ioo l r) : HasDerivAt χ (1/physicalProfile a ha x) x := by
      have hL := (hLc.differentiable (by norm_num) x).hasDerivAt
      have hR := (hRc.differentiable (by norm_num) x).hasDerivAt
      have hh := ((hL.log (hpos x hx).1.ne').sub (hR.log (hpos x hx).2.ne')).div_const 2
      convert hh using 1
      rw [hphi x hx]
      field_simp [(hpos x hx).1.ne',(hpos x hx).2.ne']
      nlinarith [hW x hx]
    have hd (x : ℝ) (hx : x∈Ioo l r) :
        HasDerivAt (fun y => packingCoordinate a ha y-χ y) 0 x := by
      have hh := (packingCoordinate_hasDerivAt a ha (hin x hx)).sub (hχ x hx)
      simpa only [Pi.sub_def,sub_self] using hh
    have he := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hd x hx).deriv) htu hsu
    have he2 : 2*(packingCoordinate a ha t-packingCoordinate a ha s)=
        (log (L t)-log (R t))-(log (L s)-log (R s)) := by
      dsimp only [χ] at he
      linarith
    have hxts := (packingCoordinate_strictMono a ha).monotoneOn ht hs hts
    rw [abs_of_nonpos (sub_nonpos.mpr hxts),neg_neg]
    have hexp : (exp (packingCoordinate a ha t-packingCoordinate a ha s))^2=
        (L t/R t)/(L s/R s) := by
      rw [← exp_nat_mul,show (2:ℕ)=2 from rfl]
      norm_num only [Nat.cast_ofNat]
      rw [he2,exp_sub,exp_sub,exp_sub,exp_log (hpos t htu).1,
        exp_log (hpos t htu).2,exp_log (hpos s hsu).1,exp_log (hpos s hsu).2]
    have hp : 0≤physicalProfile a ha t*physicalProfile a ha s :=
      mul_nonneg (physicalProfile_pos a ha ht).le (physicalProfile_pos a ha hs).le
    -- Squaring removes the square root; positivity then selects the
    -- actual positive kernel value, with no sign ambiguity.
    have hsq : (sqrt (physicalProfile a ha t*physicalProfile a ha s)*
        exp (packingCoordinate a ha t-packingCoordinate a ha s))^2=
          (2*(L t*R s))^2 := by
      rw [mul_pow,sq_sqrt hp,hexp,hphi t htu,hphi s hsu]
      field_simp [(hpos t htu).2.ne',(hpos s hsu).1.ne',(hpos s hsu).2.ne']
    rw [hprod t htu s hsu hts]
    nlinarith [sqrt_nonneg (physicalProfile a ha t*physicalProfile a ha s),
      exp_pos (packingCoordinate a ha t-packingCoordinate a ha s),
      mul_nonneg (sqrt_nonneg (physicalProfile a ha t*physicalProfile a ha s))
        (exp_pos (packingCoordinate a ha t-packingCoordinate a ha s)).le,
      mul_pos (hpos t htu).1 (hpos s hsu).2]
  rcases le_total t s with hts | hst
  · exact ordered t s ht hs hts
  · rw [physicalGreenKernel, targetGreenKernel_symmetric]
    have he := ordered s t hs ht hst
    simpa only [physicalGreenKernel,mul_comm,abs_sub_comm] using he

end
end jacobi.Trichotomy
