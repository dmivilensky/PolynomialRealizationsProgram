import jacobi.RootMass.Problem
import jacobi.Variational.MomentFeasibility

/-!
Article: jacobi, Theorem D.8.
Actual objective bounds control all three norms needed in the reused direct
method. A literal narrow box proves feasibility at every T>0. Rearrangement
preserves the complete objective, including its possibly negative mass term.
Source: exact scalar square inequalities, finite-interval integration and equimeasurability.
Use: validates the extended integral and Fatou for the whole objective, including a negative mass multiplier.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false

/-- The true inner polynomial is nonnegative at every nonnegative root argument throughout the parameter range.
Use: validates the extended integral and Fatou for the whole objective, including a negative mass multiplier.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: use the proved positive coercivity coefficient and nonnegative cubic/root terms. -/
theorem f_nonneg {a b n : ℝ} (ha : -2*sqrt 3<a) (hb : 0≤b) (hn : 0≤n) : 0≤f a b n :=
  (mul_nonneg (coercivity_pos ha).le (add_nonneg (pow_nonneg hn 3) (mul_nonneg (sq_nonneg b) hn))).trans
    (f_coercive a hb hn)

/-- The genuine root-mass integral is nonnegative.
Use: justifies real/extended objective conversions and all coercive estimates.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: integrate the nonnegative actual square root. -/
theorem RootDensity.rootIntegral_nonneg (m : RootDensity) : 0≤m.rootIntegral := integral_nonneg (fun _ => sqrt_nonneg _)

/-- The true root mass is exactly ofReal of its finite actual integral.
Use: transfers existing root tightness and rearrangement identities to the inner finite domain.
Article: jacobi, Theorem D.8.
Proof: use actual integrability and the nonnegative integral/lintegral identity. -/
theorem RootDensity.rootMass_eq (m : RootDensity) : m.rootMass=ENNReal.ofReal m.rootIntegral :=
  (ofReal_integral_eq_lintegral_ofReal m.root_integrable (Eventually.of_forall fun _ => sqrt_nonneg _)).symm

/-- The actual inner objective is nonnegative throughout the theorem's parameter range.
Use: ofReal of the objective loses no information in minimizing-sequence comparisons.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: integrate the proved nonnegative scalar polynomial. -/
theorem RootDensity.objective_nonneg (m : RootDensity) {a b : ℝ} (ha : -2*sqrt 3<a) (hb : 0≤b) :
    0≤m.objective a b := integral_nonneg (fun _ => f_nonneg ha hb (sqrt_nonneg _))

/-- The extended cost has exactly the true real objective as its finite real value.
Use: turns the monotone sequence of actual costs into coercive real bounds.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: ofReal/toReal cancel on the proved nonnegative objective. -/
theorem RootDensity.cost_toReal (m : RootDensity) {a b : ℝ} (ha : -2*sqrt 3<a) (hb : 0≤b) :
    (m.cost a b).toReal=m.objective a b := ENNReal.toReal_ofReal (m.objective_nonneg ha hb)

/-- The literal complete inner cost is its true nonnegative extended integral.
Use: Fatou applies to the whole polynomial rather than incorrectly treating a negative mass term separately.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: actual integrability and the proved nonnegative integrand identify the real and extended integrals. -/
theorem RootDensity.cost_eq_lintegral (m : RootDensity) {a b : ℝ} (ha : -2*sqrt 3<a) (hb : 0≤b) :
    m.cost a b=∫⁻ x,ENNReal.ofReal (f a b (sqrt (m.value x))) :=
  ofReal_integral_eq_lintegral_ofReal (m.f_integrable a b) (Eventually.of_forall fun _ => f_nonneg ha hb (sqrt_nonneg _))

/-- Ordinary mass is controlled by the same energy/root-mass combination, with no Holder hypothesis.
Use: closes the uniform mass bound required by the existing compactness theorem.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: integrate 2*b*n²<=n³+b²*n, whose difference is the exact nonnegative square n*(n-b)². -/
theorem RootDensity.mass_bound (m : RootDensity) (b : ℝ) :
    2*b*m.mass≤m.energy+b^2*m.rootIntegral := by
  -- Integrate the nonnegative scalar square n*(n-b)^2 at n=sqrt(m).
  have hp (x : ℝ) : 2*b*m.value x≤m.value x^(3/2:ℝ)+b^2*sqrt (m.value x) := by
    rw [rpow_div_two_eq_sqrt 3 (m.nonneg x),rpow_ofNat]
    have hs := sq_sqrt (m.nonneg x)
    have hh := mul_nonneg (sqrt_nonneg (m.value x)) (sq_nonneg (sqrt (m.value x)-b))
    nlinarith [congrArg (fun r : ℝ => 2*b*r) hs]
  have hi := integral_mono (m.integrable.const_mul (2*b))
    (m.energy_integrable.add (m.root_integrable.const_mul (b^2))) hp
  have hj := integral_add m.energy_integrable (m.root_integrable.const_mul (b^2))
  dsimp only [Pi.add_apply] at hi hj
  rw [integral_const_mul,hj,integral_const_mul] at hi
  exact hi

/-- A single actual objective bound gives uniform energy, root-mass and ordinary-mass bounds.
Use: the existing Helly/Fatou compactness theorem applies to the actual inner minimizing sequence.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: the whole polynomial dominates a positive energy/root combination;
both its summands are nonnegative, and the proved scalar square estimate controls mass. -/
theorem RootDensity.objective_bounds (m : RootDensity) {a b C : ℝ}
    (ha : -2*sqrt 3<a) (hb : 0<b) (hC : m.objective a b≤C) :
    m.energy≤C/coercivity a ∧ m.rootIntegral≤C/(coercivity a*b^2) ∧ m.mass≤C/(2*b*coercivity a) := by
  -- Every division uses a genuinely positive parameter or the proved positive coercivity constant.
  have hc := coercivity_pos ha
  have hco := (m.objective_coercive a b hb.le).trans hC
  have hE := m.toDensity.energy_nonneg
  have hR := m.rootIntegral_nonneg
  have hM := m.mass_bound b
  refine ⟨(le_div_iff₀ hc).mpr ?_,(le_div_iff₀ (mul_pos hc (sq_pos_of_pos hb))).mpr ?_,
    (le_div_iff₀ (by positivity : 0<2*b*coercivity a)).mpr ?_⟩
  · nlinarith [mul_nonneg hc.le (mul_nonneg (sq_nonneg b) hR)]
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hM hc.le]

/-- An actual radial rearrangement preserves the complete inner objective and improves the true spectral constraint.
Use: constructs the radial minimizing sequence without assuming a favorable rearranged optimizer.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: use the complete earlier equimeasurable rearrangement. Its preserved
finite root mass proves root integrability of the new density. The actual
mass, energy and root integrals then identify the entire polynomial objective. -/
theorem RootDensity.radial_replacement (m : RootDensity) (a b : ℝ) :
    ∃ q : RootDensity,SymmetricDecreasing q.value ∧ q.objective a b=m.objective a b ∧
      observe m.toDensity .second≤observe q.toDensity .second := by
  -- Exact equality, not termwise inequality, is needed when the mass multiplier is negative.
  obtain ⟨q,hs,hM,hE,hR,_hd,hO,_hF,_hP⟩ := jacobi.Rearrangement.exists_equimeasurable_rearrangement m.toDensity
  have hb : q.rootMass≤ENNReal.ofReal m.rootIntegral := by rw [hR,m.rootMass_eq]
  obtain ⟨hi,_hbound⟩ := q.root_integrable_of_bound m.rootIntegral_nonneg hb
  let w : RootDensity := ⟨q,hi⟩
  have hr : w.rootIntegral=m.rootIntegral := by
    have he : ENNReal.ofReal w.rootIntegral=ENNReal.ofReal m.rootIntegral :=
      w.rootMass_eq.symm.trans (hR.trans m.rootMass_eq)
    simpa only [ENNReal.toReal_ofReal w.rootIntegral_nonneg,ENNReal.toReal_ofReal m.rootIntegral_nonneg]
      using congrArg ENNReal.toReal he
  refine ⟨w,hs,?_,hO .second⟩
  rw [w.objective_terms,m.objective_terms,hr]
  change q.energy+(a*b/2)*q.mass+_=_
  rw [hM,hE]

end
end jacobi.RootMass
