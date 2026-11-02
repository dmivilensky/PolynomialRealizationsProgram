import jacobi.RootMass.Polynomials
import jacobi.Variational.ExtendedEnergy
import jacobi.Variational.InfimumSequence
import jacobi.Variational.Amplitude
import jacobi.Variational.Compactness
import jacobi.Rearrangement.RadialReduction
import jacobi.Young.PotentialRegularity

/-!
Article: jacobi, Theorem D.8.
The cubic root-density objective is nonnegative and coercive throughout
the source's parameter range. Its finite domain carries genuine integrable
root mass as well as mass and energy. The literal integral, its extended
cost and the inner infimum all use this same original objective.
Source: the supplement's scalar coercivity estimate and nonnegative Lebesgue integration.
Use: every root integral below is a genuine finite integral, and compactness must prove membership of its limit.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual finite domain of the inner root-mass objective.
Use: every root integral below is a genuine finite integral, and compactness must prove membership of its limit.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
structure RootDensity extends Density where
  /-- The actual nonnegative square root is integrable on the whole line. -/
  root_integrable : Integrable (fun x => sqrt (value x))

/-- Inclusion of finite root-energy densities in the previously formalized actual density domain.
Use: reuses spectral observations, rearrangement, scaling and Green potentials without changing their operators.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
instance : Coe RootDensity Density := ⟨RootDensity.toDensity⟩

/-- The literal root-mass integrand with a=eta/2.
Use: both the inner minimization and the weak dual bound use the same polynomial functional.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
def f (a b n : ℝ) : ℝ := n^3+(a*b/2)*n^2+b^2*n

/-- The exact positive coercivity coefficient.
Use: uniform objective bounds imply energy, root-mass and ordinary mass bounds for the direct method.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
def coercivity (a : ℝ) : ℝ := 1-max 0 (-a)/4

/-- The source's entire smooth profile parameter range has a strictly positive coercivity coefficient.
Use: division by the coefficient in all compactness estimates is justified.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: a>-4, so max(0,-a)<4. -/
theorem coercivity_pos {a : ℝ} (ha : -2*sqrt 3<a) : 0<coercivity a := by
  have hab := (parameter_bounds ha).1
  unfold coercivity
  have hh : max 0 (-a)<4 := max_lt (by norm_num) (by linarith)
  linarith

/-- The literal inner integrand has the exact coercive lower bound on all nonnegative root densities.
Use: proves actual convergence, compactness and positivity of the inner objective, including negative mass multipliers.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: for negative a, the difference is (-a)/4 times n*(n-b)²;
for nonnegative a the extra quadratic term is nonnegative. -/
theorem f_coercive (a : ℝ) {b n : ℝ} (hb : 0≤b) (hn : 0≤n) :
    coercivity a*(n^3+b^2*n)≤f a b n := by
  -- The exact square identity handles the negative multiplier, where termwise integral Fatou would fail.
  by_cases ha : 0≤a
  · rw [coercivity,max_eq_left (by linarith : -a≤0)]
    unfold f
    norm_num
    have hh : 0≤(a*b/2)*n^2 := mul_nonneg (div_nonneg (mul_nonneg ha hb) (by norm_num)) (sq_nonneg n)
    linarith
  · rw [coercivity,max_eq_right (by linarith : 0≤-a)]
    have hh := mul_nonneg (mul_nonneg (show 0≤-a/4 by linarith) hn) (sq_nonneg (n-b))
    unfold f
    nlinarith

/-- The actual inner polynomial is positive for every positive root-density value when b>0.
Use: rules out zero-cost nonzero competitors and establishes strict constraint activity.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: the positive coercivity coefficient times the strictly positive cubic is a positive lower bound. -/
theorem f_pos {a b n : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (hn : 0<n) : 0<f a b n :=
  (mul_pos (coercivity_pos ha) (add_pos_of_pos_of_nonneg (pow_pos hn 3) (mul_nonneg (sq_nonneg b) hn.le))).trans_le
    (f_coercive a hb.le hn.le)

/-- The inner objective's actual polynomial integral is finite on its stated finite domain.
Use: every ordinary integral manipulation in the needle variation and weak duality has its integrability premise discharged.
Article: jacobi, Theorem D.8.
Proof: the square of sqrt(m) is m and its cube is m^(3/2); all three polynomial terms are integrable. -/
theorem RootDensity.f_integrable (m : RootDensity) (a b : ℝ) : Integrable (fun x => f a b (sqrt (m.value x))) := by
  have h2 (x : ℝ) : (sqrt (m.value x))^2=m.value x := sq_sqrt (m.nonneg x)
  have h3 (x : ℝ) : (sqrt (m.value x))^3=m.value x^(3/2:ℝ) := by
    rw [rpow_div_two_eq_sqrt 3 (m.nonneg x),rpow_ofNat]
  unfold f
  simp_rw [h2,h3]
  exact (m.energy_integrable.add (m.integrable.const_mul _)).add (m.root_integrable.const_mul _)

/-- The genuine finite root-mass integral of a root-energy density.
Use: the inner objective's linear root term and all coercive compactness estimates.
Article: jacobi, Theorem D.8.
-/
def RootDensity.rootIntegral (m : RootDensity) : ℝ := ∫ x,sqrt (m.value x)

/-- The real value of the original inner objective on its actual finite domain.
Use: the exact inner optimum is later evaluated by the compact-profile quadratures.
Article: jacobi, Theorem D.8.
-/
def RootDensity.objective (m : RootDensity) (a b : ℝ) : ℝ := ∫ x,f a b (sqrt (m.value x))

/-- The actual objective equals its three original mass, energy and root-mass terms.
Use: identifies the attained inner value with the printed Lagrangian expression.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: the proved integrability justifies linearity for every polynomial summand. -/
theorem RootDensity.objective_terms (m : RootDensity) (a b : ℝ) :
    m.objective a b=m.energy+(a*b/2)*m.mass+b^2*m.rootIntegral := by
  -- Nonnegative square-root identities identify exactly the original energy normalization.
  have h2 (x : ℝ) : (sqrt (m.value x))^2=m.value x := sq_sqrt (m.nonneg x)
  have h3 (x : ℝ) : (sqrt (m.value x))^3=m.value x^(3/2:ℝ) := by rw [rpow_div_two_eq_sqrt 3 (m.nonneg x),rpow_ofNat]
  unfold RootDensity.objective f
  simp_rw [h2,h3]
  have hi := integral_add (m.energy_integrable.add (m.integrable.const_mul (a*b/2))) (m.root_integrable.const_mul (b^2))
  have hj := integral_add m.energy_integrable (m.integrable.const_mul (a*b/2))
  dsimp only [Pi.add_apply] at hi hj
  rw [hi,hj,integral_const_mul,integral_const_mul]
  rfl

/-- The actual inner objective dominates its positive energy and root-mass combination.
Use: obtains all uniform bounds required for actual minimizer extraction.
Article: jacobi, Theorem D.8.
Proof: integrate the literal pointwise coercivity inequality with all terms already integrable. -/
theorem RootDensity.objective_coercive (m : RootDensity) (a b : ℝ) (hb : 0≤b) :
    coercivity a*(m.energy+b^2*m.rootIntegral)≤m.objective a b := by
  -- Integrate the pointwise coercivity inequality using the actual three integrable terms.
  have hp (x : ℝ) : coercivity a*(m.value x^(3/2:ℝ)+b^2*sqrt (m.value x))≤f a b (sqrt (m.value x)) := by
    rw [rpow_div_two_eq_sqrt 3 (m.nonneg x),rpow_ofNat]
    exact f_coercive a hb (sqrt_nonneg _)
  have hh := integral_mono ((m.energy_integrable.add (m.root_integrable.const_mul (b^2))).const_mul (coercivity a))
    (m.f_integrable a b) hp
  have hi := integral_add m.energy_integrable (m.root_integrable.const_mul (b^2))
  dsimp only [Pi.add_apply] at hi hh
  rw [integral_const_mul,hi,
    integral_const_mul] at hh
  exact hh

/-- The nonnegative extended inner cost on the genuine finite root-energy domain.
Use: the complete ordered-space infimum handles empty admissible sets correctly.
Article: jacobi, Theorem D.8.
-/
def RootDensity.cost (m : RootDensity) (a b : ℝ) : ℝ≥0∞ := ENNReal.ofReal (m.objective a b)

/-- The actual inner variational infimum at a prescribed positive spectral second moment.
Use: the root-mass theorem evaluates this problem before weak duality is applied.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
def inner (a b T : ℝ) : ℝ≥0∞ :=
  sInf ((fun m : RootDensity => m.cost a b) '' {m | T≤observe m.toDensity .second})

end
end jacobi.RootMass
