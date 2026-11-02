import krylov.Correction.PairingOrders
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), real observed curvature quotients.
Use: propagate true quadratic field differences through the actual inner
products and nonsingular quotients used by history-only trial policies.
Source: real bilinear difference identities and reciprocal continuity.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Filter Topology Asymptotics krylov.Correction
variable {α : Type*} {f : Filter α}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual pairings preserve the common order of two actual field
differences when the true outer fields are bounded.
Use: compare the recorded and native descent and curvature observations.
Article: main_krylov, thm:local(a), genuine pairing comparison.
Proof: split the real bilinear difference and apply Cauchy--Schwarz to
its two actual error terms, using their genuine bounded outer factors. -/
theorem inner_difference_order (u v U V : α → E) (r : α → ℝ)
    (hu : (fun z => u z-U z) =O[f] r) (hv : (fun z => v z-V z) =O[f] r)
    (hU : U =O[f] (fun _ => (1 : ℝ))) (hvb : v =O[f] (fun _ => (1 : ℝ))) :
    (fun z => inner ℝ (u z) (v z)-inner ℝ (U z) (V z)) =O[f] r := by
  have h1 : (fun z => inner ℝ (u z-U z) (v z)) =O[f] r := by
    simpa only [mul_one] using inner_order _ _ _ _ hu hvb
  have h2 : (fun z => inner ℝ (U z) (v z-V z)) =O[f] r := by
    simpa only [one_mul] using inner_order _ _ _ _ hU hv
  have h : (fun z => inner ℝ (u z-U z) (v z)+inner ℝ (U z) (v z-V z)) =O[f] r := by
    exact h1.add h2
  apply h.congr_left
  intro z
  rw [inner_sub_left,inner_sub_right]
  ring

/-- Actual nonsingular scalar quotients preserve the common order of
their real numerator and denominator differences.
Use: an implemented known-curvature trial inherits the genuine native
quotient jet, without an assumed smooth or equal recorded virtual pair.
Article: main_krylov, thm:local(a), actual quotient comparison.
Proof: real reciprocal continuity bounds both denominators on their true
nonzero domains. Split the exact quotient difference into the numerator
error and denominator error multiplied by these actual bounded factors. -/
theorem quotient_difference_order (a b c d : α → ℝ) (r : α → ℝ)
    (b0 d0 : ℝ) (hb0 : b0≠0) (hd0 : d0≠0)
    (hb : Tendsto b f (𝓝 b0)) (hd : Tendsto d f (𝓝 d0))
    (hc : c =O[f] (fun _ => (1 : ℝ)))
    (hac : (fun z => a z-c z) =O[f] r) (hbd : (fun z => b z-d z) =O[f] r) :
    (fun z => a z/b z-c z/d z) =O[f] r := by
  have hib : (fun z => (b z)⁻¹) =O[f] (fun _ => (1 : ℝ)) := (hb.inv₀ hb0).isBigO_one ℝ
  have hid : (fun z => (d z)⁻¹) =O[f] (fun _ => (1 : ℝ)) := (hd.inv₀ hd0).isBigO_one ℝ
  have h : (fun z => (a z-c z)*(b z)⁻¹-c z*(b z-d z)*(b z)⁻¹*(d z)⁻¹) =O[f] r := by
    have h1 : (fun z => (a z-c z)*(b z)⁻¹) =O[f] r := by simpa only [mul_one] using hac.mul hib
    have h2 : (fun z => c z*(b z-d z)*(b z)⁻¹*(d z)⁻¹) =O[f] r := by
      simpa only [one_mul,mul_one] using ((hc.mul hbd).mul hib).mul hid
    exact h1.sub h2
  apply h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hb.eventually_ne hb0,hd.eventually_ne hd0] with z hbz hdz
  field_simp
  ring

end
end krylov.LinearAlgebra
