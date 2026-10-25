import chebyshev1.SineJacobi.ProfileDerivatives

/-!
Article: chebyshev1, Theorem E.3.
The explicit profile solves the singular ODE with actual first and second derivatives.
Result: `chebyshev1.SineJacobi.sineProfile_ode` supplies the stated article conclusion.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set Filter Topology

/--
Exact identity `C*((-p^2*s/(2*w)-p^2*c^2/(4*w^3))*H + 2*(p*c/(2*w))*(H₁*((p/2)*q)) +
w*(H₂*((p/2)*q)^2+H₁*(-(p^2/4)*k))) + p^2/(4*s^2)*(C*w*H) =
(C*p^2*q/(2*w))*(k*(1-k^2)*H₂+(1-3*k^2)*H₁-k*H)`.

Use: `chebyshev1.SineJacobi.sineProfile_explicit_ode` uses this identity to establish exact
identity `sineProfile₂ t + Real.pi^2/(4*sin (Real.pi*t)^2)*sineProfile t = 0`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem profile_transform_algebra (p s c k q w H H₁ H₂ C : ℝ)
    (hw : w ≠ 0) (hws : w^2 = s) (_hs : s ≠ 0) (hskq : s = 2*k*q)
    (htrig : s^2+c^2 = 1) (hq : q^2 = 1-k^2) (hc : c = 1-2*k^2) :
    C*((-p^2*s/(2*w)-p^2*c^2/(4*w^3))*H +
      2*(p*c/(2*w))*(H₁*((p/2)*q)) +
      w*(H₂*((p/2)*q)^2+H₁*(-(p^2/4)*k))) + p^2/(4*s^2)*(C*w*H) =
        (C*p^2*q/(2*w))*(k*(1-k^2)*H₂+(1-3*k^2)*H₁-k*H) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h0 : -p^2*s/(2*w)-p^2*c^2/(4*w^3)+p^2/(4*s^2)*w = -p^2*w/4 := by
    have hcs : c^2 = 1-s^2 := by linarith
    rw [hcs, ← hws]
    field_simp [hw]
    ring
  have h1 : p^2*c*q/(2*w)-p^2*w*k/4 = p^2*q/(2*w)*(1-3*k^2) := by
    rw [hc]
    field_simp [hw]
    rw [hws, hskq]
    ring
  have h2 : p^2*w*q^2/4 = p^2*q/(2*w)*(k*(1-k^2)) := by
    field_simp [hw]
    rw [hws, hskq, hq]
    ring
  have h3 : -p^2*w/4 = p^2*q/(2*w)*(-k) := by
    field_simp [hw]
    rw [hws, hskq]
    ring
  calc
    _ = C*((-p^2*s/(2*w)-p^2*c^2/(4*w^3)+p^2/(4*s^2)*w)*H +
      (p^2*c*q/(2*w)-p^2*w*k/4)*H₁+(p^2*w*q^2/4)*H₂) := by ring
    _ = _ := by rw [h0, h1, h2, h3]; ring

/--
Exact identity `sineProfile₂ t + Real.pi^2/(4*sin (Real.pi*t)^2)*sineProfile t = 0`.

Use: `chebyshev1.SineJacobi.sineProfile_ode` uses this identity to establish the identity
`deriv (deriv sineProfile) t + Real.pi^2/(4*sin (Real.pi*t)^2)*sineProfile t = 0`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.profileWeight_pos`,
`_private.chebyshev1.SineJacobi.ProfileODE.0.chebyshev1.SineJacobi.profile_transform_algebra`,
`chebyshev1.SineJacobi.ellipticK_ode` with the arguments shown in the proof.
-/
theorem sineProfile_explicit_ode {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    sineProfile₂ t + Real.pi^2/(4*sin (Real.pi*t)^2)*sineProfile t = 0 := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.profileWeight_pos`,
  -- `_private.chebyshev1.SineJacobi.ProfileODE.0.chebyshev1.SineJacobi.profile_transform_algebra`,
  -- `chebyshev1.SineJacobi.ellipticK_ode` with the arguments shown in the proof.
  have hw := (profileWeight_pos ht).ne'
  have hws : profileWeight t^2 = sin (Real.pi*t) :=
    Real.sq_sqrt (Real.sqrt_pos.mp (profileWeight_pos ht)).le
  have hs : sin (Real.pi*t) ≠ 0 := (Real.sqrt_pos.mp (profileWeight_pos ht)).ne'
  have hskq : sin (Real.pi*t) = 2*profileModulus t*cos (Real.pi*t/2) := by
    unfold profileModulus
    rw [← sin_two_mul]
    congr 1
    ring
  have hq : cos (Real.pi*t/2)^2 = 1-profileModulus t^2 := by
    unfold profileModulus
    nlinarith [sin_sq_add_cos_sq (Real.pi*t/2)]
  have hc : cos (Real.pi*t) = 1-2*profileModulus t^2 := by
    unfold profileModulus
    conv_lhs => rw [show Real.pi*t = 2*(Real.pi*t/2) by ring, cos_two_mul]
    nlinarith [sin_sq_add_cos_sq (Real.pi*t/2)]
  have halg := profile_transform_algebra Real.pi (sin (Real.pi*t)) (cos (Real.pi*t))
    (profileModulus t) (cos (Real.pi*t/2)) (profileWeight t)
    (ellipticK (profileModulus t)) (ellipticK₁ (profileModulus t))
    (ellipticK₂ (profileModulus t)) (2/(Real.pi*Real.sqrt Real.pi))
    hw hws hs hskq (sin_sq_add_cos_sq _) hq hc
  have hODE := ellipticK_ode (profileModulus_lt_one ht)
  rw [hODE, mul_zero] at halg
  simpa only [sineProfile₂, sineProfile, profileWeight₁, profileWeight₂,
    profileElliptic, profileElliptic₁, profileElliptic₂, profileModulus₁,
    profileModulus₂, profileModulus, profileWeight] using halg

/--
The explicit profile solves the singular ODE with actual first and second derivatives.

Exact identity `deriv (deriv sineProfile) t + Real.pi^2/(4*sin (Real.pi*t)^2)*sineProfile t =
0`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem E.3.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineProfile_ode {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    deriv (deriv sineProfile) t + Real.pi^2/(4*sin (Real.pi*t)^2)*sineProfile t = 0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have he : deriv sineProfile =ᶠ[𝓝 t] sineProfile₁ := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact (sineProfile_deriv hu).deriv
  have hd := (sineProfile₁_deriv ht).congr_of_eventuallyEq he
  rw [hd.deriv]
  exact sineProfile_explicit_ode ht

end
end chebyshev1.SineJacobi
