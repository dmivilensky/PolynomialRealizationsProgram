import jacobi.Complex.SimplePole

/-!
Article: jacobi, Proposition C.2.
An actual quotient of entire functions extends across every common
simple zero by the ratio of their genuine derivatives. Matching simple
zero sets make the extended quotient entire and nowhere zero. This is
the analytic division step for the original midpoint characteristic
product; constancy requires the separate growth comparison.
Source: removable singularities via analytic divided differences.
Use: midpointProductQuotient compares the actual original separated characteristic product with Delta_sigma, without a pole or zero-set assumption left in its application.
-/
namespace jacobi.Complex
noncomputable section
open Set Filter _root_.Complex
open scoped Topology

/-- The genuine quotient with its actual removable value assigned at each simple zero of its denominator.
Use: midpointProductQuotient compares the actual original separated characteristic product with Delta_sigma, without a pole or zero-set assumption left in its application.
Article: jacobi, Proposition C.2.
-/
def simpleZeroQuotient (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if g z=0 then deriv f z/deriv g z else f z/g z

/-- Near a common simple zero the globally patched quotient is the actual ratio of analytic divided differences.
Use: simpleZeroQuotient_analytic proves the original removable characteristic quotient analytic at each actual spectral zero.
Article: jacobi, Proposition C.2.
Proof: the denominator divided difference is nonzero on a neighborhood of the base point. Thus its original denominator has no other zero there, and both original functions factor by the same genuine linear factor. At the base point the assigned quotient is exactly the ratio of their derivatives. -/
theorem simpleZeroQuotient_eq_near {f g : ℂ → ℂ} {p : ℂ}
    (hg : AnalyticAt ℂ g p) (hf0 : f p=0) (hg0 : g p=0) (hg' : deriv g p≠0) :
    simpleZeroQuotient f g =ᶠ[𝓝 p] fun z => dslope f p z/dslope g p z := by
  -- Nonvanishing is obtained from the actual analytic denominator derivative, not a chosen neighborhood free of unverified poles.
  have hn : ∀ᶠ z in 𝓝 p,dslope g p z≠0 :=
    (analyticAt_dslope hg).continuousAt.eventually_ne (by simpa only [dslope_same] using hg')
  filter_upwards [hn] with z hz
  by_cases hp : z=p
  · subst z
    rw [simpleZeroQuotient,ite_eq_left hg0,dslope_same,dslope_same]
  · have hgfact : g z=(z-p)*dslope g p z := by
      simpa only [smul_eq_mul,hg0,sub_zero] using (sub_smul_dslope g p z).symm
    have hffact : f z=(z-p)*dslope f p z := by
      simpa only [smul_eq_mul,hf0,sub_zero] using (sub_smul_dslope f p z).symm
    have hgz : g z≠0 := by rw [hgfact]; exact mul_ne_zero (sub_ne_zero.mpr hp) hz
    rw [simpleZeroQuotient,ite_eq_right hgz,hffact,hgfact,mul_div_mul_left _ _ (sub_ne_zero.mpr hp)]

/-- The actual quotient patched by its true derivative ratios is analytic wherever its denominator is nonzero or has a genuine common simple zero.
Use: midpointProductQuotient_analytic applies this theorem to the original proved characteristic zero sets and derivatives at every complex energy.
Article: jacobi, Proposition C.2.
Proof: at a genuine zero use the proved analytic divided-difference quotient. Away from zeros the actual patched function agrees locally with ordinary analytic division. -/
theorem simpleZeroQuotient_analytic {f g : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hz : g p=0 → f p=0 ∧ deriv g p≠0) :
    AnalyticAt ℂ (simpleZeroQuotient f g) p := by
  -- At each genuine simple zero the divided differences provide the analytic quotient; elsewhere ordinary analytic division applies.
  by_cases hg0 : g p=0
  · obtain ⟨hf0,hg'⟩ := hz hg0
    have hd := (analyticAt_dslope hf).div (analyticAt_dslope hg)
      (by simpa only [dslope_same] using hg')
    exact hd.congr (simpleZeroQuotient_eq_near hg hf0 hg0 hg').symm
  · have hn := hg.continuousAt.eventually_ne hg0
    exact (hf.div hg hg0).congr (hn.mono (fun z hz => by
      change f z/g z=simpleZeroQuotient f g z
      rw [simpleZeroQuotient,ite_eq_right hz]))

/-- The actual extended quotient multiplies its genuine denominator back to the original numerator, including every common zero.
Use: midpointProductQuotient_factor gives a global identity for the unchanged original entire characteristics before their growth comparison.
Article: jacobi, Proposition C.2.
Proof: ordinary division cancels off the denominator zeros; on each genuine common zero both sides vanish. -/
theorem simpleZeroQuotient_mul {f g : ℂ → ℂ} (hz : ∀ z,g z=0 → f z=0) (z : ℂ) :
    simpleZeroQuotient f g z*g z=f z := by
  by_cases hg : g z=0
  · simp only [hg,mul_zero,hz z hg]
  · rw [simpleZeroQuotient,ite_eq_right hg,div_mul_cancel₀ _ hg]

/-- Matching genuine simple zero sets make the actual extended entire quotient nowhere zero.
Use: midpointProductQuotient_ne_zero retains the exact zero multiplicities of both original midpoint parity characteristics.
Article: jacobi, Proposition C.2.
Proof: off the zeros both original factors are nonzero; at a common zero both genuine first derivatives are nonzero. -/
theorem simpleZeroQuotient_ne_zero {f g : ℂ → ℂ} (hz : ∀ z,f z=0 ↔ g z=0)
    (hf : ∀ z,f z=0 → deriv f z≠0) (hg : ∀ z,g z=0 → deriv g z≠0) (z : ℂ) :
    simpleZeroQuotient f g z≠0 := by
  by_cases hg0 : g z=0
  · rw [simpleZeroQuotient,ite_eq_left hg0]
    exact div_ne_zero (hf z ((hz z).mpr hg0)) (hg z hg0)
  · rw [simpleZeroQuotient,ite_eq_right hg0]
    exact div_ne_zero (fun h => hg0 ((hz z).mp h)) hg0

end
end jacobi.Complex
