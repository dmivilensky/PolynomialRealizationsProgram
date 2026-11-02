import jacobi.Young.Sharp
import jacobi.Young.EqualityFamily

/-!
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
The global sharp inequality and the explicitly checked equality-family candidate
identify the actual root-free second-moment infimum throughout the Young regime,
with attainment. At U the actual distinguished density also satisfies root mass
one, giving the stronger root-constrained infimum exactly 2/15.
No rearrangement, minimizer-existence or equality-classification premise is used
for these statements: the matching lower bound and attaining candidate are proved.
Use: the exact value of the second-moment infimum in the Young regime.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real Set jacobi.Variational
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The printed sharp Young calibration value as a function of its moment threshold.
Use: the exact value of the second-moment infimum in the Young regime.
Article: jacobi, Theorem D.5.
-/
def youngValue (T : ℝ) : ℝ := (18/5 : ℝ)^(1/4 : ℝ)*T^(3/4 : ℝ)

/-- The printed Young value is nonnegative for every nonnegative threshold.
Use: takes fourth roots in the exact calibration comparison.
Article: jacobi, Theorem D.5.
Proof: both real-power factors have nonnegative bases. -/
theorem youngValue_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ youngValue T := by
  dsimp [youngValue]
  positivity

/-- The fourth power of the printed sharp value is a rational polynomial.
Use: compares the calibration lower bound with the actual spectral inequality exactly.
Article: jacobi, Theorem D.5.
Proof: combine the positive real exponents before simplifying their integer powers. -/
theorem youngValue_four {T : ℝ} (hT : 0 ≤ T) : (youngValue T)^4=(18/5 : ℝ)*T^3 := by
  have hc : ((18/5 : ℝ)^(1/4 : ℝ))^4=(18/5 : ℝ) := by
    rw [← rpow_natCast,← rpow_mul (by norm_num : (0 : ℝ) ≤ 18/5)]
    norm_num
  have ht : (T^(3/4 : ℝ))^4=T^3 := by
    rw [← rpow_natCast,← rpow_mul hT]
    norm_num
  rw [youngValue,mul_pow,hc,ht]

/-- The previously constructed candidate has exactly the printed sharp energy.
Use: converts explicit sqrt-amplitude computations into the article's closed formula.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: both nonnegative quantities have fourth power (18/5)T_2³. -/
theorem young_candidate_energy_eq {T : ℝ} (hT : 0 ≤ T) :
    (16/15 : ℝ)*(sqrt (45*T/32))^(3/2 : ℝ)=youngValue T := by
  -- Comparing fourth powers avoids any approximate evaluation of fractional powers.
  let b := sqrt (45*T/32)
  have hb : 0 ≤ b := sqrt_nonneg _
  have hb2 : b^2=45*T/32 := sq_sqrt (by positivity)
  have hp : (b^(3/2 : ℝ))^4=b^6 := by
    rw [← rpow_natCast,← rpow_mul hb]
    norm_num
  apply (pow_left_inj₀ (by positivity) (youngValue_nonneg hT) (by decide : 4 ≠ 0)).mp
  change ((16/15 : ℝ)*b^(3/2 : ℝ))^4=(youngValue T)^4
  rw [mul_pow,hp,show b^6=(b^2)^3 by ring,hb2,youngValue_four hT]
  ring

/-- Sharp Young supplies the exact energy lower bound for any density above the threshold.
Use: the lower half of the infimum identity, without an assumed minimizer or symmetry.
Article: jacobi, Theorem D.5.
Proof: monotonicity of cubing transfers the threshold to 18G_2³≤5E⁴,
then take the order-preserving fourth root of the exact printed-value identity. -/
theorem second_energy_lower (m : Density) {T : ℝ} (hT : 0 ≤ T)
    (ht : T ≤ observe m .second) : youngValue T ≤ m.energy := by
  have hc := pow_le_pow_left₀ hT ht 3
  apply (pow_le_pow_iff_left₀ (youngValue_nonneg hT) m.energy_nonneg (by decide : 4 ≠ 0)).mp
  rw [youngValue_four hT]
  nlinarith [sharp_young_cubed m]

/-- The Young-regime calibration is attained at a literal sech^4 density.
Use: supplies an actual optimizer, rather than a conditional energy formula.
Article: jacobi, Theorem D.5.
Proof: the fully checked candidate has the required mass and exact spectral moment,
and its computed energy agrees with the printed value. -/
theorem young_attained {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (hregime : 5*T ≤ 2*M^2) :
    ∃ m : Density, m.mass ≤ M ∧ observe m .second=T ∧ m.energy=youngValue T := by
  obtain ⟨m,hm,ht,he⟩ := young_candidate_feasible hM hT hregime
  exact ⟨m,hm,ht,he.trans (young_candidate_energy_eq hT)⟩

/-- Exact root-free second-moment calibration throughout the complete Young regime.
Use: the finished first regime of the article's second-moment variational problem.
Article: jacobi, Theorem D.5.
Proof: sharp Young bounds every actual admissible density from below; the explicit
candidate gives the reverse infimum inequality and proves attainment. -/
theorem second_calibration_young {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hregime : 5*T ≤ 2*M^2) :
    relaxedInfimum {Observation.second} M (fun _ => T)=ENNReal.ofReal (youngValue T) := by
  -- Both inequalities concern exactly the admissible set used in the article's relaxation.
  apply le_antisymm
  · simpa only [young_candidate_energy_eq hT] using relaxed_second_upper hM hT hregime
  · apply le_sInf
    rintro a ⟨m,hm,rfl⟩
    exact ENNReal.ofReal_le_ofReal (second_energy_lower m hT (hm.2 .second (by simp)))

/-- The printed Young value at U is exactly 2/15.
Use: identifies the rational common-point calibration without decimal or root evaluation.
Article: jacobi, Theorem D.5.
Proof: the nonnegative fourth powers agree exactly as rational numbers. -/
theorem youngValue_at_U : youngValue (2/45 : ℝ)=2/15 := by
  apply (pow_left_inj₀ (youngValue_nonneg (by norm_num)) (by norm_num : (0 : ℝ) ≤ 2/15)
    (by decide : 4 ≠ 0)).mp
  rw [youngValue_four (by norm_num)]
  norm_num

/-- The genuine root-free second-moment infimum at U has the exact value 2/15.
Use: the first exact calibration at the distinguished density.
Article: jacobi, Theorem D.5.
Proof: specialize the full Young-regime theorem at mass 1/3 and moment 2/45. -/
theorem second_calibration_at_U :
    relaxedInfimum {Observation.second} (1/3) (fun _ => 2/45)=(2/15 : ℝ≥0∞) := by
  rw [second_calibration_young (by norm_num) (by norm_num) (by norm_num),youngValue_at_U]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- The root-constrained second-moment infimum at U also equals 2/15 and is attained.
Use: the stronger root-mass relaxation has its exact, unconditional value at U.
Article: jacobi, Theorem D.5.
Proof: dropping constraints gives the proved lower bound; the actual distinguished
density has mass 1/3, root mass one, second moment 2/45 and energy 2/15. -/
theorem root_second_calibration_at_U :
    rootInfimum {Observation.second} (1/3) (fun _ => 2/45)=(2/15 : ℝ≥0∞) := by
  -- The upper witness satisfies the original root-mass condition, not just the relaxed problem.
  apply le_antisymm
  · rw [← distinguished_cost]
    apply sInf_le
    refine ⟨distinguishedDensity,⟨distinguished_mass,?_,?_⟩,rfl⟩
    · exact distinguished_rootMass.le
    · intro i hi
      have he : i=Observation.second := Set.mem_singleton_iff.mp hi
      subst i
      exact distinguished_second.ge
  · rw [← second_calibration_at_U]
    exact relaxed_le_root _ _ _

end
end jacobi.Young
