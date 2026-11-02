import jacobi.Young.Potential

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
All inputs are actual finite-energy densities and all observations use their
actual ordered kernel spectra. The Green potential, its H1 energy, the sharp
Sobolev inequality and mathlib's Holder theorem discharge the analytic chain.
The polynomial form 18 G_2³≤5 E⁴ is also retained for exact algebraic use.
Equality classification and the elliptic calibration are separate assertions.
Use: verifies both Holder hypotheses from the density's energy and the potential's cube.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real jacobi.Variational
open chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false

/-- A finite nonnegative p-power integral supplies genuine Lp membership.
Use: verifies both Holder hypotheses from the density's energy and the potential's cube.
Article: jacobi, Section 3.2 (sharp Young inequality).
Source: mathlib's equivalence between the Lp seminorm and the norm-power integral.
Proof: nonnegativity removes the pointwise norm and ofReal(p) has real value p. -/
theorem memLp_of_power_integrable {f : ℝ → ℝ} (hm : AEStronglyMeasurable f volume)
    (hn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p) (hi : Integrable (fun x => f x^p)) :
    MemLp f (ENNReal.ofReal p) volume := by
  apply (integrable_norm_rpow_iff hm (by simpa using hp) ENNReal.ofReal_ne_top).mp
  have he : (fun x => ‖f x‖^(ENNReal.ofReal p).toReal)=(fun x => f x^p) := by
    funext x
    rw [ENNReal.toReal_ofReal hp.le,Real.norm_of_nonneg (hn x)]
  rw [he]
  exact hi

/-- Cubing a nonnegative real one-third power cancels its denominator exactly.
Use: the sharp inequalities can be combined in polynomial form without numerical constants.
Article: jacobi, Section 3.2 (sharp Young inequality).
Source: mathlib's real-power multiplication theorem.
Proof: combine the exponents k/3 and 3, then use the natural-power identity. -/
theorem third_power_cube {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x^((k : ℝ)/3))^3=x^k := by
  rw [← rpow_natCast,← rpow_mul hx]
  norm_num

/-- The actual potential's cube is integrable, so Holder has no unproved L3 premise.
Use: combines the potential with the original density in the sharp Young proof.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the scaled H1 evaluation bound bounds u uniformly, and u³≤C u². -/
theorem potential_cube_integrable (m : Density) : Integrable (fun x => potential m x^3) := by
  apply cube_integrable (potential_sobolev m) (potential_nonneg m)
  intro x
  change (1/2 : ℝ)*H1.rep (chebyshev2.GroundState.convolution (source m)) (2*x) ≤ _
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (H1.evaluation_bound _ (2*x))) (by norm_num : (0 : ℝ) ≤ 1/2)

/-- The common sharp Holder/Sobolev chain for an actual nonnegative Green pair.
Use: the finite-mass and full L^(3/2) domains reuse the same sharp proof and equality tracking.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: apply Holder to the source and actual Sobolev potential, then apply
sharp Sobolev and substitute the Green energy identity established by each construction. -/
theorem young_chain_of_green {m u d : ℝ → ℝ}
    (hmm : AEStronglyMeasurable m volume) (hn : ∀ x, 0≤m x)
    (hE : Integrable (fun x => m x^(3/2 : ℝ))) (hU : SobolevRegular u d)
    (hU0 : ∀ x, 0≤u x) (hU3 : Integrable (fun x => u x^3)) {G : ℝ}
    (hpair : (∫ x, m x*u x)=G)
    (henergy : (∫ x, d x^2)+4*(∫ x, u x^2)=4*G) :
    G^3≤(∫ x, m x^(3/2 : ℝ))^2*(∫ x, u x^3) ∧
      18*(∫ x, u x^3)^2≤5*G^3 := by
  -- Every analytic quantity below comes from this literal density and its constructed potential.
  let E := ∫ x, m x^(3/2 : ℝ)
  let S := ∫ x, u x^3
  have hG0 : 0 ≤ G := hpair ▸ integral_nonneg (fun x => mul_nonneg (hn x) (hU0 x))
  have hE0 : 0 ≤ E := integral_nonneg (fun x => Real.rpow_nonneg (hn x) _)
  have hS0 : 0 ≤ S := integral_nonneg (fun x => pow_nonneg (hU0 x) _)
  have hm := memLp_of_power_integrable hmm hn (by norm_num : (0 : ℝ) < 3/2) hE
  have hu := memLp_of_power_integrable hU.value_memLp.aestronglyMeasurable
    hU0 (by norm_num : (0 : ℝ) < 3) (by simpa only [rpow_ofNat] using hU3)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (3/2 : ℝ)) (q := 3) (by norm_num [holderConjugate_iff])
    (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall hU0) hm hu
  norm_num only [one_div_div,div_one,one_mul,rpow_ofNat] at hholder
  rw [hpair] at hholder
  change G ≤ E^(2/3 : ℝ)*S^(1/3 : ℝ) at hholder
  have hc := pow_le_pow_left₀ hG0 hholder 3
  have hcube2 (x : ℝ) (hx : 0 ≤ x) : (x^(2/3 : ℝ))^3=x^2 := by
    simpa only [Nat.cast_ofNat] using third_power_cube hx 2
  have hcube1 : (S^(1/3 : ℝ))^3=S := by
    simpa only [Nat.cast_one,pow_one] using third_power_cube hS0 1
  rw [mul_pow,hcube2 E hE0,hcube1] at hc
  -- Sobolev and the exact Green identity use the same actual potential and second moment.
  have hs := sharp_sobolev_nonneg hU hU0
  rw [henergy] at hs
  change (32/5 : ℝ)*(15*S/16)^(2/3 : ℝ) ≤ 4*G at hs
  have hs3 := pow_le_pow_left₀ (by positivity : 0 ≤ (32/5 : ℝ)*(15*S/16)^(2/3 : ℝ)) hs 3
  rw [mul_pow,hcube2 (15*S/16) (by positivity)] at hs3
  exact ⟨hc,by nlinarith⟩

/-- The two actual inequalities in the sharp Young proof, retaining their intermediate integral.
Use: proves the global bound and tracks equality through both Holder and sharp Sobolev.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: identify the literal density-potential pairing with the actual second
spectral moment, and discharge every Green hypothesis of the shared analytic argument. -/
theorem young_chain (m : Density) :
    (observe m .second)^3≤m.energy^2*(∫ x, potential m x^3) ∧
      18*(∫ x, potential m x^3)^2≤5*(observe m .second)^3 := by
  have hp : (∫ x, m.value x*potential m x)=observe m .second := by
    rw [← m.secondPairing_self,secondPairing_iterated m.integrable m.integrable m.measurable m.measurable]
    simp_rw [potential_kernel]
  exact young_chain_of_green m.integrable.aestronglyMeasurable m.nonneg m.energy_integrable
    (potential_sobolev m) (potential_nonneg m) (potential_cube_integrable m) hp (potential_energy m)

/-- The exact algebraic form of sharp Young for every actual finite-energy density.
Use: yields the sharp second-moment lower bound and rules out weaker unproved analytic premises.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: multiply the two proved Holder/Sobolev chain inequalities and cancel
the positive second moment, handling a zero second moment separately. -/
theorem sharp_young_cubed (m : Density) : 18*(observe m .second)^3 ≤ 5*m.energy^4 := by
  -- Retaining the chain separately lets the equality proof use exactly these inequalities.
  let G := observe m .second
  let E := m.energy
  let S := ∫ x, potential m x^3
  have hG0 : 0 ≤ G := tsum_nonneg (fun _ => sq_nonneg _)
  have hE0 : 0 ≤ E := m.energy_nonneg
  obtain ⟨hc,hSG⟩ := young_chain m
  have hc2 := mul_self_le_mul_self (pow_nonneg hG0 3) hc
  have hmul := mul_le_mul_of_nonneg_left hSG (pow_nonneg hE0 4)
  change 18*G^3 ≤ 5*E^4
  by_cases hz : G=0
  · rw [hz,zero_pow (by decide : 3 ≠ 0),mul_zero]
    positivity
  · have hp : 0 < G := lt_of_le_of_ne hG0 (Ne.symm hz)
    have he : G^3*(18*G^3) ≤ G^3*(5*E^4) := by nlinarith
    exact (mul_le_mul_iff_of_pos_left (pow_pos hp 3)).mp he

/-- The sharp Young inequality with exactly the constant printed in the article.
Use: the global lower bound for the second-moment calibration, including the Young regime.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: take the increasing nonnegative cube root of the proved polynomial inequality. -/
theorem sharp_young (m : Density) :
    observe m .second ≤ (5/18 : ℝ)^(1/3 : ℝ)*m.energy^(4/3 : ℝ) := by
  -- All cube-root factors are nonnegative, so the order-preserving real-power rules apply.
  have hG0 : 0 ≤ observe m .second := tsum_nonneg (fun _ => sq_nonneg _)
  have hc : (observe m .second)^3 ≤ (5/18 : ℝ)*m.energy^4 := by
    nlinarith [sharp_young_cubed m]
  have h := rpow_le_rpow (pow_nonneg hG0 3) hc (by norm_num : (0 : ℝ) ≤ 1/3)
  rw [← rpow_natCast_mul hG0,Real.mul_rpow (by norm_num) (pow_nonneg m.energy_nonneg 4),
    ← rpow_natCast_mul m.energy_nonneg] at h
  norm_num at h
  exact h

end
end jacobi.Young
