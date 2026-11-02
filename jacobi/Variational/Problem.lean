import jacobi.Variational.SpectralStability
import jacobi.Continuum.MomentBounds

/-!
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
The variational problems use the actual kernel spectra and finite-energy
nonnegative densities. Costs and root mass take extended nonnegative values;
in particular the infimum of an empty admissible set is infinity. Excluding
infinite-energy candidates from the domain leaves precisely the finite costs.
Source: the direct method of the calculus of variations, with ENNReal infima.
Use: the full domain of the Fredholm operator, Green and variation lemmas.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real chebyshev2.Continuum
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

/-- An arbitrary nonnegative integrable source, with no energy assumption.
Use: the full domain of the Fredholm operator, Green and variation lemmas.
Article: jacobi, Section 3.5 (edge data and the lower constant).
-/
structure L1Source where
  /-- The literal measurable density on the real line. -/
  value : ℝ → ℝ
  /-- Measurability required for rearrangement and multiple integrals. -/
  measurable : Measurable value
  /-- Positivity of the actual density, fixing square-root and real-power branches. -/
  nonneg : ∀ x, 0 ≤ value x
  /-- Finite mass, without a normalization to one. -/
  integrable : Integrable value

/-- A nonnegative finite-energy density in the actual variational domain.
Use: the common domain for the moment, root-mass and Fredholm relaxations.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
structure Density extends L1Source where
  /-- Finite energy; candidates with infinite cost cannot lower an infimum. -/
  energy_integrable : Integrable (fun x => value x^(3/2 : ℝ))

/-- A variational density is an actual L1 source after forgetting its energy bound.
Use: reuses the full-domain operator theorems without duplicating any variational proof.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
instance : Coe Density L1Source := ⟨Density.toL1Source⟩

/-- The actual ordered spectrum of an arbitrary nonnegative L1 source.
Use: the same genuine kernel eigenvalues govern the operator and variational results.
Article: jacobi, Appendix D.1 (ground parameter).
-/
def L1Source.spectrum (m : L1Source) : ℕ → ℝ := kernelEigenvalue m.integrable m.nonneg

/-- The literal mass of an arbitrary integrable source.
Use: mass compactness and full-domain rearrangement require no energy assumption.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def L1Source.mass (m : L1Source) : ℝ := ∫ x,m.value x

namespace Density

/-- Actual mass of a finite-energy density.
Use: the common linear constraint in every relaxation.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def mass (m : Density) : ℝ := ∫ x, m.value x

/-- Actual integral energy, with its L^(3/2) integrability stored in the domain.
Use: objective of every relaxation and calibration.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def energy (m : Density) : ℝ := ∫ x, m.value x^(3/2 : ℝ)

/-- Root mass in the extended nonnegative reals, allowing an infinite value.
Use: expresses the root-mass constraint without Bochner-integral junk values.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def rootMass (m : Density) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.sqrt (m.value x))

/-- Finite-energy cost in the complete ordered space used for infima.
Use: empty admissible sets have infinite infimum and all genuine energy costs stay finite.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def cost (m : Density) : ℝ≥0∞ := ENNReal.ofReal m.energy

/-- The energy integrand and its integral are nonnegative.
Use: relates extended costs to the actual real-valued energy.
Article: jacobi, Lemma D.1.
Proof: a nonnegative real base has nonnegative real powers, then integrate. -/
theorem energy_nonneg (m : Density) : 0 ≤ m.energy :=
  integral_nonneg (fun x => Real.rpow_nonneg (m.nonneg x) _)

/-- The extended cost recovers exactly the real energy.
Use: transfers infimum inequalities back to the printed real normalization.
Article: jacobi, Section 3.5 (edge data and the lower constant).
Proof: ofReal and toReal are inverse on nonnegative reals. -/
theorem cost_toReal (m : Density) : m.cost.toReal = m.energy :=
  ENNReal.toReal_ofReal m.energy_nonneg

end Density

/-- An arbitrary positive summable ordered edge spectrum, without Bessel assumptions.
Use: supplies all thresholds in the general Transfer theorem.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
structure EdgeSpectrum where
  /-- The eigenvalues, with zero-based indexing. -/
  value : ℕ → ℝ
  /-- Every edge eigenvalue is strictly positive. -/
  positive : ∀ k, 0 < value k
  /-- Descending order, counted with multiplicities. -/
  antitone : Antitone value
  /-- Finite total mass. -/
  summable : Summable value

namespace EdgeSpectrum

/-- Total mass of the arbitrary edge spectrum.
Use: the mass constraint in all limiting variational problems.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def mass (S : EdgeSpectrum) : ℝ := ∑' j, S.value j

/-- The second limiting spectral moment.
Use: threshold for the second-moment relaxation and its two calibration regimes.
Article: jacobi, Section 3.5 (edge data and the lower constant).
-/
def second (S : EdgeSpectrum) : ℝ := ∑' j, S.value j^2

/-- Every admissible edge spectrum has positive mass.
Use: proves that all calibration mass normalizations are meaningful.
Article: jacobi, Section 3.5 (edge data and the lower constant).
Proof: the first eigenvalue is positive and is bounded by the total mass. -/
theorem mass_pos (S : EdgeSpectrum) : 0 < S.mass :=
  (S.positive 0).trans_le (S.summable.le_tsum 0 (fun j _ => (S.positive j).le))

/-- The top eigenvalue is strictly below the mass for every edge spectrum.
Use: verifies the strict feasibility threshold for ground-state minimizers.
Article: jacobi, Section 3.5 (edge data and the lower constant).
Proof: the sum contains the positive second eigenvalue in addition to the first. -/
theorem top_lt_mass (S : EdgeSpectrum) : S.value 0 < S.mass := by
  have h := S.summable.sum_le_tsum ({0,1} : Finset ℕ) (fun j _ => (S.positive j).le)
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton] at h
  exact lt_of_lt_of_le (lt_add_of_pos_right _ (S.positive 1)) h

/-- The second threshold is strictly below the square of the mass.
Use: verifies strict feasibility for second-moment and joint minimizers.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the general moment bound gives T_2 ≤ lambda_0 M, and lambda_0 < M. -/
theorem second_lt_mass_sq (S : EdgeSpectrum) : S.second < S.mass^2 := by
  have h := jacobi.Continuum.moment_bound S.summable (fun j => (S.positive j).le) S.antitone 1
  simp only [pow_one] at h
  change S.second ≤ S.value 0 * S.mass at h
  exact h.trans_lt (by nlinarith [mul_lt_mul_of_pos_right S.top_lt_mass S.mass_pos])

end EdgeSpectrum

/-- The two spectral observations retained by the moment relaxations.
Use: permits the individual and joint constraints in one common definition.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
inductive Observation
  /-- The quadratic spectral moment G_2. -/
  | second
  /-- The largest eigenvalue G_infinity. -/
  | top
  deriving DecidableEq, Fintype

/-- The actual observation attached to an arbitrary nonnegative L1 source.
Use: all admissible sets below constrain this spectrum, rather than a model sequence.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def observe (m : L1Source) : Observation → ℝ
  | .second => ∑' j, m.spectrum j^2
  | .top => m.spectrum 0

/-- Spectral thresholds extracted from the arbitrary limiting edge spectrum.
Use: specializes the general mass/threshold problems to the article's Lambda.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def threshold (S : EdgeSpectrum) : Observation → ℝ
  | .second => S.second
  | .top => S.value 0

/-- The full moment relaxation with only an upper mass bound.
Use: the objective identified by the Young, elliptic and Keller calibrations.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def relaxedInfimum (S : Set Observation) (M : ℝ) (T : Observation → ℝ) : ℝ≥0∞ :=
  sInf (Density.cost '' {m | m.mass ≤ M ∧ ∀ i ∈ S, T i ≤ observe m i})

/-- The moment relaxation with exact mass and bounded root mass.
Use: the stronger continuum bound produced directly by finite packing.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def rootInfimum (S : Set Observation) (M : ℝ) (T : Observation → ℝ) : ℝ≥0∞ :=
  sInf (Density.cost '' {m | m.mass = M ∧ m.rootMass ≤ 1 ∧ ∀ i ∈ S, T i ≤ observe m i})

/-- Dropping the root-mass condition and relaxing exact mass can only lower the infimum.
Use: the middle inequality in the full Transfer theorem.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: inclusion of admissible sets reverses the order of their infima. -/
theorem relaxed_le_root (S : Set Observation) (M : ℝ) (T : Observation → ℝ) :
    relaxedInfimum S M T ≤ rootInfimum S M T := by
  apply sInf_le_sInf
  apply Set.image_mono
  intro m hm
  exact ⟨hm.1.le, hm.2.2⟩

/-- Adding spectral constraints cannot decrease the relaxed infimum.
Use: compares joint calibrations to the sharp individual second-moment calibration.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: a density satisfying the larger set of constraints satisfies the smaller one. -/
theorem relaxed_mono_constraints {S Q : Set Observation} (hSQ : S ⊆ Q) (M : ℝ)
    (T : Observation → ℝ) : relaxedInfimum S M T ≤ relaxedInfimum Q M T := by
  apply sInf_le_sInf
  apply Set.image_mono
  intro m hm
  exact ⟨hm.1, fun i hi => hm.2 i (hSQ hi)⟩

end
end jacobi.Variational
