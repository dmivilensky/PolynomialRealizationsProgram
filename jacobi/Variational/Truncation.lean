import jacobi.Variational.Tails
import jacobi.Variational.SecondMoment
import jacobi.Continuum.ExponentialKernel

/-!
Article: jacobi, Lemma D.1.
The truncated density belongs to the same finite-energy variational domain.
Pointwise radial bounds and the exact mass of exp(-2|.|) give the stronger
estimate |G_2(m)-G_2(m_R)|≤M²/R, hence also the article's stated 3M²/R.
No unproved rearrangement or compactness result is used here.
Use: turns local L1 compactness into convergence of the full spectral observations.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set
set_option backward.isDefEq.respectTransparency false

/-- Restriction of a finite-energy density to the centered interval [-R,R].
Use: turns local L1 compactness into convergence of the full spectral observations.
Article: jacobi, Lemma D.1.
-/
def Density.truncate (m : Density) (R : ℝ) : Density where
  value := (Icc (-R) R).indicator m.value
  measurable := m.measurable.indicator measurableSet_Icc
  nonneg x := indicator_nonneg (fun _ _ => m.nonneg _) x
  integrable := m.integrable.indicator measurableSet_Icc
  energy_integrable := by
    have he : (fun x => ((Icc (-R) R).indicator m.value x)^(3/2 : ℝ)) =
        (Icc (-R) R).indicator (fun x => m.value x^(3/2 : ℝ)) := by
      funext x
      by_cases hx : x ∈ Icc (-R) R <;> simp [hx]
    rw [he]
    exact m.energy_integrable.indicator measurableSet_Icc

/-- Truncation decreases the density pointwise.
Use: establishes positivity of the removed tail and monotonicity of its mass.
Article: jacobi, Lemma D.1.
Proof: the indicator either keeps m or replaces it by zero. -/
theorem Density.truncate_le (m : Density) (R x : ℝ) : (m.truncate R).value x ≤ m.value x := by
  exact indicator_le_self' (fun _ _ => m.nonneg _) x

/-- The truncated mass is no larger than the full mass.
Use: controls both cross terms in the spectral truncation estimate.
Article: jacobi, Lemma D.1.
Proof: integrate the pointwise indicator inequality. -/
theorem Density.truncate_mass_le (m : Density) (R : ℝ) : (m.truncate R).mass ≤ m.mass :=
  integral_mono (m.truncate R).integrable m.integrable (m.truncate_le R)

/-- The removed radial tail has an explicit uniform pointwise upper bound.
Use: bounds its convolution potential independently of its total mass.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the tail is zero inside the interval and the mass tail estimate applies outside. -/
theorem truncation_tail_bound (m : Density) (hs : SymmetricDecreasing m.value)
    {M R : ℝ} (hM : m.mass ≤ M) (hR : 0 < R) (x : ℝ) :
    m.value x-(m.truncate R).value x ≤ M/(2*R) := by
  -- Only points outside the interval need the radial estimate; their absolute radius exceeds R.
  have hM0 : 0 ≤ M := (integral_nonneg m.nonneg).trans hM
  by_cases hx : x ∈ Icc (-R) R
  · change m.value x-(Icc (-R) R).indicator m.value x ≤ _
    rw [indicator_of_mem hx,sub_self]
    positivity
  · have hrad : R < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
    have hx0 : x ≠ 0 := abs_pos.mp (hR.trans hrad)
    change m.value x-(Icc (-R) R).indicator m.value x ≤ _
    rw [indicator_of_notMem hx,sub_zero]
    exact (mass_tail m.integrable m.nonneg hs hM hx0).trans
      (div_le_div_of_nonneg_left hM0 (by positivity) (by linarith))

/-- Each fixed-center signed exponential potential is absolutely integrable.
Use: proves convolution bounds pointwise rather than only at almost every center.
Article: jacobi, Lemma D.1.
Proof: the exponential factor is at most one, so |q| is an L1 majorant. -/
theorem second_inner_integrable {q : ℝ → ℝ} (hq : Integrable q) (x : ℝ) :
    Integrable (fun y => q y*exp (-2*|x-y|)) := by
  apply hq.abs.mono'
  · exact hq.aestronglyMeasurable.mul
      (by have h : Continuous (fun y : ℝ => exp (-2*|x-y|)) := by fun_prop
          exact h.aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (exp_le_one_iff.mpr (by linarith [abs_nonneg (x-y)]))

/-- A uniformly bounded nonnegative tail has an equally bounded exponential potential.
Use: the exponential second-moment kernel has L1 mass exactly one.
Article: jacobi, Lemma D.1.
Proof: compare with B exp(-2|x-y|) and use its exact integral. -/
theorem second_potential_le {q : ℝ → ℝ} (hq : Integrable q) {B : ℝ}
    (hB : ∀ y, q y ≤ B) (x : ℝ) : (∫ y, q y*exp (-2*|x-y|)) ≤ B := by
  have h := integral_mono (second_inner_integrable hq x)
    ((jacobi.Continuum.exponential_shift_integrable (by norm_num : (0 : ℝ) < 2) x).const_mul B)
    (fun y => mul_le_mul_of_nonneg_right (hB y) (exp_pos _).le)
  simpa only [integral_const_mul,jacobi.Continuum.exponential_shift_integral (by norm_num : (0 : ℝ) < 2),
    div_self (by norm_num : (2 : ℝ) ≠ 0),mul_one] using h

/-- A bilinear cross term is at most the mass times the bound on the other density.
Use: controls the two cross terms in the exact G_2 truncation difference.
Article: jacobi, Lemma D.1.
Proof: Fubini gives an integrable outer potential; integrate its pointwise upper bound. -/
theorem secondPairing_le_mass {m q : ℝ → ℝ} (hm : Integrable m) (hq : Integrable q)
    (hmm : Measurable m) (hqm : Measurable q) (hn : ∀ x, 0 ≤ m x)
    {B : ℝ} (hB : ∀ y, q y ≤ B) : secondPairing m q ≤ B*(∫ x, m x) := by
  -- Fubini supplies integrability before the potential is estimated pointwise.
  have hi := (second_integrand_integrable hm hq hmm hqm).integral_prod_left
  have he : Integrable (fun x => m x*(∫ y, q y*exp (-2*|x-y|))) := by
    apply hi.congr
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
  rw [secondPairing_iterated hm hq hmm hqm,← integral_const_mul]
  apply integral_mono he (hm.const_mul B)
  intro x
  exact (mul_le_mul_of_nonneg_left (second_potential_le hq hB x) (hn x)).trans_eq (mul_comm _ _)

/-- Positive densities have nonnegative second-moment interactions.
Use: G_2 cannot decrease when a nonnegative tail is restored.
Article: jacobi, Lemma D.1.
Proof: every factor of the actual double integrand is nonnegative. -/
theorem secondPairing_nonneg {m q : ℝ → ℝ} (hm : ∀ x, 0 ≤ m x) (hq : ∀ x, 0 ≤ q x) :
    0 ≤ secondPairing m q :=
  integral_nonneg (fun z => mul_nonneg (mul_nonneg (hm z.1) (hq z.2)) (exp_pos _).le)

/-- Exact tail decomposition of the actual second spectral moment.
Use: both positivity and quantitative bounds reduce to two signed bilinear terms.
Article: jacobi, Lemma D.1.
Proof: expand both subtractions and cancel the common cross term. -/
theorem second_truncation_identity (m : Density) (R : ℝ) :
    observe m .second-observe (m.truncate R) .second =
      secondPairing m.value (m.value-(m.truncate R).value)+
        secondPairing (m.value-(m.truncate R).value) (m.truncate R).value := by
  rw [secondPairing_sub_right m.integrable m.integrable (m.truncate R).integrable
      m.measurable m.measurable (m.truncate R).measurable,
    secondPairing_sub_left m.integrable (m.truncate R).integrable (m.truncate R).integrable
      m.measurable (m.truncate R).measurable (m.truncate R).measurable,
    m.secondPairing_self,(m.truncate R).secondPairing_self]
  ring

/-- A quantitative truncation estimate for the genuine second spectral moment.
Use: removes the tails uniformly in the Compactness lemma's local-to-global limit.
Article: jacobi, Lemma D.1.
Proof: both cross terms are nonnegative and each is bounded by M times M/(2R). -/
theorem second_truncation_bound (m : Density) (hs : SymmetricDecreasing m.value)
    {M R : ℝ} (hM : m.mass ≤ M) (hR : 0 < R) :
    0 ≤ observe m .second-observe (m.truncate R) .second ∧
      |observe m .second-observe (m.truncate R) .second| ≤ M^2/R := by
  -- The same signed tail is used in the exact identity and in the convolution estimate.
  let p := m.truncate R
  have htail := m.integrable.sub p.integrable
  have hmeas := m.measurable.sub p.measurable
  have hn (x : ℝ) : 0 ≤ m.value x-p.value x := sub_nonneg.mpr (m.truncate_le R x)
  have hb := truncation_tail_bound m hs hM hR
  have h1 := secondPairing_le_mass m.integrable htail m.measurable hmeas m.nonneg hb
  have h2 := secondPairing_le_mass p.integrable htail p.measurable hmeas p.nonneg hb
  have hsym := secondPairing_symm htail p.integrable hmeas p.measurable
  have hpos : 0 ≤ secondPairing m.value (m.value-p.value)+secondPairing (m.value-p.value) p.value :=
    add_nonneg (secondPairing_nonneg m.nonneg hn) (secondPairing_nonneg hn p.nonneg)
  rw [second_truncation_identity]
  refine ⟨hpos, ?_⟩
  change |secondPairing m.value (m.value-p.value)+secondPairing (m.value-p.value) p.value| ≤ _
  rw [abs_of_nonneg hpos,hsym]
  calc
    _ ≤ M/(2*R)*m.mass+M/(2*R)*p.mass := add_le_add h1 h2
    _ ≤ M/(2*R)*M+M/(2*R)*M := by
      have hM0 : 0 ≤ M := (integral_nonneg m.nonneg).trans hM
      exact add_le_add (mul_le_mul_of_nonneg_left hM (by positivity))
        (mul_le_mul_of_nonneg_left ((m.truncate_mass_le R).trans hM) (by positivity))
    _ = _ := by field_simp; ring

end
end jacobi.Variational
