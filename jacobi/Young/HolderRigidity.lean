import jacobi.Young.Sharp
import chebyshev2.GroundState.Variational

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
An exact nonnegative cubic defect proves the equality condition needed in
the Holder step: sqrt(m) is proportional to the actual Green potential.
The two inequalities in the existing sharp proof force this equality;
no independent extremizer or Euler equation is assumed.
Source: the equality case of Holder, here proved by a cubic polynomial identity.
Use: identifies sqrt(m) with a scalar multiple of its actual Green potential.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real Filter jacobi.Variational chebyshev2.Continuum
set_option backward.isDefEq.respectTransparency false

/-- The nonnegative cubic Holder defect determines equality almost everywhere.
Use: identifies sqrt(m) with a scalar multiple of its actual Green potential.
Article: jacobi, Section 3.2 (sharp Young inequality).
Source: the elementary identity 2a³+b³-3a²b=(a-b)²(2a+b).
Proof: integrate this nonnegative defect with b=cg. Equality of the cubic
moments makes its integral zero; its factors force f=cg almost everywhere. -/
theorem cubic_holder_rigidity {f g : ℝ → ℝ}
    (hf : ∀ x, 0≤f x) (hg : ∀ x, 0≤g x)
    (hi : Integrable (fun x => f x^3)) (hj : Integrable (fun x => g x^3))
    (hk : Integrable (fun x => f x^2*g x))
    {c : ℝ} (hc : 0<c)
    (he : 2*(∫ x, f x^3)+c^3*(∫ x, g x^3)-3*c*(∫ x, f x^2*g x)=0) :
    f =ᵐ[volume] (fun x => c*g x) := by
  -- Rewrite the defect using integrable cubic terms before applying integral-zero rigidity.
  let d (x : ℝ) := (f x-c*g x)^2*(2*f x+c*g x)
  have hd (x : ℝ) : d x=2*f x^3+c^3*g x^3-3*c*(f x^2*g x) := by dsimp [d]; ring
  have hdi : Integrable d := by
    apply (((hi.const_mul 2).add (hj.const_mul (c^3))).sub (hk.const_mul (3*c))).congr
    exact Eventually.of_forall fun x => (hd x).symm
  have hzero : (∫ x, d x)=0 := by
    simp_rw [hd]
    have hsub := integral_sub ((hi.const_mul 2).add (hj.const_mul (c^3))) (hk.const_mul (3*c))
    have hadd := integral_add (hi.const_mul 2) (hj.const_mul (c^3))
    simp only [Pi.add_apply] at hsub hadd
    rw [hsub,hadd]
    simpa only [integral_const_mul] using he
  have hdae := (integral_eq_zero_iff_of_nonneg (fun x =>
    mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg (by norm_num) (hf x))
      (mul_nonneg hc.le (hg x)))) hdi).mp hzero
  filter_upwards [hdae] with x hx
  change (f x-c*g x)^2*(2*f x+c*g x)=0 at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
  · nlinarith [hf x,hg x]

/-- A nonzero actual density has a strictly positive second spectral moment.
Use: all equality normalizations divide by genuine positive quantities.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: its positive leading eigenvalue contributes a strictly positive square to the second moment. -/
theorem second_pos_of_mass_pos (m : Density) (hm : 0<m.mass) : 0<observe m .second := by
  have hp : 0<m.spectrum 0 := (chebyshev2.GroundState.top_density_attained m.integrable m.nonneg hm).1
  have hs : Summable (fun j => m.spectrum j^2) := jacobi.Continuum.summable_powers
    (kernelSpectralData m.integrable m.nonneg).eigenvalue_summable
    (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg (by decide : 0<2)
  exact (sq_pos_of_pos hp).trans_le (hs.le_tsum 0 (fun _ _ => sq_nonneg _))

/-- Equality in the sharp polynomial bound forces equality in the two-step Holder/Sobolev chain.
Use: both finite-mass and unrestricted finite-energy sources use the same equality propagation.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: if G³<E²S, squaring and combining 18S²≤5G³ would make
18G³<5E⁴. Positivity excludes cancellation at zero. -/
theorem young_chain_rigid {G E S : ℝ} (hG : 0<G) (hE0 : 0≤E) (hS : 0≤S)
    (hc : G^3≤E^2*S) (hs : 18*S^2≤5*G^3) (he : 18*G^3=5*E^4) : G^3=E^2*S := by
  -- Both inequalities are exactly those used in sharp_young_cubed.
  have hE : 0<E := by
    by_contra! h
    have hz : E=0 := le_antisymm h hE0
    rw [hz] at he
    norm_num at he
    nlinarith [pow_pos hG 3]
  apply le_antisymm hc
  have hmul := mul_le_mul_of_nonneg_left hs (pow_nonneg hE0 4)
  have hge : (E^2*S)^2≤(G^3)^2 := by nlinarith [he]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hge

/-- Equality in sharp Young forces equality in its actual Holder step.
Use: the source density becomes a continuous square of its Green potential.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: apply the common rigidity lemma to the actual proved Holder/Sobolev chain. -/
theorem young_equality_holder (m : Density) (hm : 0<m.mass)
    (he : 18*(observe m .second)^3=5*m.energy^4) :
    (observe m .second)^3=m.energy^2*(∫ x, potential m x^3) :=
  young_chain_rigid (second_pos_of_mass_pos m hm) m.energy_nonneg
    (integral_nonneg (fun x => pow_nonneg (potential_nonneg m x) _))
    (young_chain m).1 (young_chain m).2 he

/-- Every nonzero sharp Young equality density is the square of its own potential, with fixed coefficient.
Use: regularizes all equality densities and yields their semilinear classical Green equation.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: set c=E/G>0 and integrate the cubic Holder defect. The forced
identity G³=E²S makes its integral zero, so sqrt(m)=cu almost everywhere. -/
theorem young_equality_potential (m : Density) (hm : 0<m.mass)
    (he : 18*(observe m .second)^3=5*m.energy^4) :
    ∃ c : ℝ, 0<c ∧ (fun x => Real.sqrt (m.value x))=ᵐ[volume] (fun x => c*potential m x) ∧
      m.value=ᵐ[volume] (fun x => c^2*potential m x^2) := by
  -- The coefficient uses ordinary positive energies and observations, so no real-power branch is chosen.
  let G := observe m .second
  let E := m.energy
  let S := ∫ x, potential m x^3
  have hG : 0<G := second_pos_of_mass_pos m hm
  have hE : 0<E := by
    have hE0 : 0≤E := m.energy_nonneg
    change 18*G^3=5*E^4 at he
    by_contra! h
    have hz : E=0 := le_antisymm h hE0
    rw [hz] at he
    norm_num at he
    nlinarith [pow_pos hG 3]
  have hpair : (∫ x, m.value x*potential m x)=G := by
    dsimp only [G]
    rw [← m.secondPairing_self,secondPairing_iterated m.integrable m.integrable m.measurable m.measurable]
    simp_rw [potential_kernel]
  have hmul : Integrable (fun x => m.value x*potential m x) := by
    have hi := (second_integrand_integrable m.integrable m.integrable m.measurable m.measurable).integral_prod_left
    apply hi.congr
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [potential_kernel,← integral_const_mul]
      congr 1
      funext y
      ring
  have hp (x : ℝ) : Real.sqrt (m.value x)^3=m.value x^(3/2 : ℝ) := by
    rw [Real.rpow_div_two_eq_sqrt 3 (m.nonneg x),Real.rpow_ofNat]
  have hroot : Integrable (fun x => Real.sqrt (m.value x)^3) := by simp_rw [hp]; exact m.energy_integrable
  have hcross : Integrable (fun x => Real.sqrt (m.value x)^2*potential m x) := by
    simp_rw [Real.sq_sqrt (m.nonneg _)]
    exact hmul
  have hEq : G^3=E^2*S := young_equality_holder m hm he
  let c := E/G
  have hc : 0<c := div_pos hE hG
  have hzero : 2*(∫ x, Real.sqrt (m.value x)^3)+c^3*S-
      3*c*(∫ x, Real.sqrt (m.value x)^2*potential m x)=0 := by
    simp_rw [hp,Real.sq_sqrt (m.nonneg _)]
    rw [hpair]
    change 2*E+c^3*S-3*c*G=0
    dsimp only [c]
    field_simp
    nlinarith [hEq]
  have h := cubic_holder_rigidity (fun x => Real.sqrt_nonneg _) (potential_nonneg m)
    hroot (potential_cube_integrable m) hcross hc hzero
  refine ⟨c,hc,h,?_⟩
  filter_upwards [h] with x hx
  have hh := congrArg (fun r : ℝ => r^2) hx
  rwa [Real.sq_sqrt (m.nonneg x),mul_pow] at hh

end
end jacobi.Young
