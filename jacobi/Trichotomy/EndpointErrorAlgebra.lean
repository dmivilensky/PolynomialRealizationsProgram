import jacobi.Trichotomy.EndpointEnvelope

/-!
Article: jacobi, Proposition C.4.
Use: endpoint_profile_difference_bound substitutes the actual eigenvalues, norming constants and waves, discharging every hypothesis from their proved bounds.
-/
namespace jacobi.Trichotomy
noncomputable section

/-- Coefficient errors of order n^-4 and wave errors of order t give a summable normalized profile error whenever the true squared envelope obeys its two endpoint bounds.
Use: endpoint_profile_difference_bound substitutes the actual eigenvalues, norming constants and waves, discharging every hypothesis from their proved bounds.
Article: jacobi, Proposition C.4.
Proof: write the numerator as (L*rho-T)*u^2+T*(u-v)*(u+v). The two wave envelopes bound its absolute value. Multiply by the index power p, use p*e^2<=n*t and p*e^2<=1, then use the actual norm lower bound c<=N*p and divide by the positive N*t. -/
theorem endpoint_error_algebra {L rho T u v N n t p c C D B e : ℝ}
    (hn : 0<n) (ht : 0<t) (hp : 0<p) (hc : 0<c) (hC : 0<C)
    (hD : 0<D) (hB : 0<B) (he : 0≤e) (hT : 0≤T)
    (hN : c/p≤N) (hcoeff : |L*rho-T|≤D/n^4) (hTB : T≤B/n^2)
    (hu : |u|≤C*e) (hv : |v|≤C*e) (hdiff : |u-v|≤C*t*e)
    (he1 : p*e^2≤1) (het : p*e^2≤n*t) :
    |(L*rho*u^2/N-T*v^2/N)/t|≤(D*C^2/c)/n^3+(2*B*C^2/c)/n^2 := by
  -- The norm lower bound is used after the two endpoint envelope bounds, so no physical power is discarded prematurely.
  let R := (D*C^2/c)/n^3+(2*B*C^2/c)/n^2
  have hNp : c≤N*p := (div_le_iff₀ hp).mp hN
  have hNp0 : 0<N := (div_pos hc hp).trans_le hN
  have hR : 0≤R := by dsimp only [R]; positivity
  have hsum : |u+v|≤2*C*e := (abs_add_le u v).trans (by linarith)
  have hsq : u^2≤(C*e)^2 := by nlinarith [sq_abs u,pow_le_pow_left₀ (abs_nonneg u) hu 2]
  have hnum : |L*rho*u^2-T*v^2|≤(D/n^4)*(C*e)^2+
      (B/n^2)*((C*t*e)*(2*C*e)) := by
    rw [show L*rho*u^2-T*v^2=(L*rho-T)*u^2+T*((u-v)*(u+v)) by ring]
    apply (abs_add_le _ _).trans
    simp only [abs_mul,abs_pow,abs_of_nonneg hT]
    exact add_le_add (mul_le_mul hcoeff (by simpa only [sq_abs] using hsq)
      (by positivity) (by positivity))
      (mul_le_mul hTB (mul_le_mul hdiff hsum (abs_nonneg _) (by positivity))
        (by positivity) (by positivity))
  have hbound : |L*rho*u^2-T*v^2| * p≤R*c*t := by
    calc
      _ ≤ ((D/n^4)*(C*e)^2+(B/n^2)*((C*t*e)*(2*C*e)))*p :=
        mul_le_mul_of_nonneg_right hnum hp.le
      _ = (D*C^2/n^4)*(p*e^2)+(2*B*C^2/n^2)*t*(p*e^2) := by ring
      _ ≤ (D*C^2/n^4)*(n*t)+(2*B*C^2/n^2)*t*1 :=
        add_le_add (mul_le_mul_of_nonneg_left het (by positivity))
          (mul_le_mul_of_nonneg_left he1 (by positivity))
      _ = R*c*t := by dsimp only [R]; field_simp [hn.ne',hc.ne']
  have hboundN : |L*rho*u^2-T*v^2| * p≤(R*(N*t))*p := by
    calc
      _ ≤ R*c*t := hbound
      _ ≤ R*(N*p)*t := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNp hR) ht.le
      _ = _ := by ring
  have hquot := (div_le_iff₀ (mul_pos hNp0 ht)).mpr
    ((mul_le_mul_iff_left₀ hp).mp hboundN)
  have hid : (L*rho*u^2/N-T*v^2/N)/t=(L*rho*u^2-T*v^2)/(N*t) := by ring
  rw [hid,abs_div,abs_of_pos (mul_pos hNp0 ht)]
  exact hquot

end
end jacobi.Trichotomy
