import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Positivity

/-!
Article: main_krylov, thm:B, the mixed Christoffel criterion on all probability measures.
Use: define the genuine variational objective without an invertible moment-matrix
premise; prove nonnegativity, degree monotonicity and upper semicontinuity.
Source: KieferWolfowitz60 and Pukelsheim93, variational definition of c-information;
mathlib supplies weak convergence and continuity of bounded continuous integrals.
-/

namespace krylov.Design
noncomputable section
open Set MeasureTheory Polynomial

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- Polynomials of degree at most m, normalized at the extrapolation point a.
Use: retain all competitors even for singular moment matrices.
Article: main_krylov, thm:B. -/
def Competitor (m : ℕ) (a : ℝ) := {p : ℝ[X] // p.natDegree ≤ m ∧ p.eval a = 1}

instance (m : ℕ) (a : ℝ) : Nonempty (Competitor m a) :=
  ⟨⟨1, by simp⟩⟩

/-- The actual polynomial-square integral on a compact spectral space.
Use: specialize X to the physical closed spectral interval and x to its inclusion.
Article: main_krylov, thm:B, Christoffel variational criterion. -/
def polynomialEnergy (x : C(X, ℝ)) (ν : ProbabilityMeasure X) (p : ℝ[X]) : ℝ :=
  ∫ t, (p.eval (x t)) ^ 2 ∂ν

/-- Christoffel c-information, defined on every probability measure.
Use: singular and finitely supported measures require no totalized inverse.
Article: main_krylov, thm:B. -/
def christoffel (m : ℕ) (a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X) : ℝ :=
  ⨅ p : Competitor m a, polynomialEnergy x ν p.val

/-- Polynomial-square energy is nonnegative for the genuine measure integral.
Article: main_krylov, thm:B. Proof: pointwise nonnegativity of a square. -/
theorem polynomialEnergy_nonneg (x : C(X, ℝ)) (ν : ProbabilityMeasure X) (p : ℝ[X]) :
    0 ≤ polynomialEnergy x ν p := integral_nonneg fun _ => sq_nonneg _

/-- The real infimum defining Christoffel information is bounded below.
Use: justify all conditionally complete infimum operations.
Article: main_krylov, thm:B. -/
theorem energy_bddBelow (m : ℕ) (a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X) :
    BddBelow (range fun p : Competitor m a => polynomialEnergy x ν p.val) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact polynomialEnergy_nonneg x ν p.val⟩

/-- Christoffel information is nonnegative, including singular measures.
Article: main_krylov, thm:B. Proof: every competitor has nonnegative energy. -/
theorem christoffel_nonneg (m : ℕ) (a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X) :
    0 ≤ christoffel m a x ν := le_ciInf fun p => polynomialEnergy_nonneg x ν p.val

/-- Every normalized polynomial supplies a valid Christoffel upper bound.
Article: main_krylov, thm:B. Proof: use the bounded-below real infimum. -/
theorem christoffel_le (m : ℕ) (a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X)
    (p : Competitor m a) : christoffel m a x ν ≤ polynomialEnergy x ν p.val :=
  ciInf_le (energy_bddBelow m a x ν) p

/-- The constant competitor bounds information by one for every probability measure.
Article: main_krylov, thm:B. Proof: integrate the constant polynomial one. -/
theorem christoffel_le_one (m : ℕ) (a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X) :
    christoffel m a x ν ≤ 1 := by
  simpa [polynomialEnergy] using christoffel_le m a x ν ⟨1, by simp⟩

/-- Increasing the degree enlarges the feasible set and decreases the information.
Article: main_krylov, lem:chebyshev-design, the mixed lower majorant.
Proof: compare against each lower-degree competitor before taking the infimum. -/
theorem christoffel_antitone_degree {m n : ℕ} (hmn : m ≤ n) (a : ℝ)
    (x : C(X, ℝ)) (ν : ProbabilityMeasure X) :
    christoffel n a x ν ≤ christoffel m a x ν := by
  apply le_ciInf
  intro p
  exact christoffel_le n a x ν ⟨p.val, p.property.1.trans hmn, p.property.2⟩

variable [CompactSpace X] [BorelSpace X]

/-- Each polynomial energy is continuous for the weak topology on probability measures.
Article: main_krylov, thm:B. Proof: import mathlib's bounded-continuous integral theorem. -/
theorem continuous_polynomialEnergy (x : C(X, ℝ)) (p : ℝ[X]) :
    Continuous (fun ν : ProbabilityMeasure X => polynomialEnergy x ν p) := by
  let f : C(X, ℝ) := ⟨fun t => (p.eval (x t)) ^ 2, (p.continuous.comp x.continuous).pow 2⟩
  exact ProbabilityMeasure.continuous_integral_continuousMap f

/-- The variational Christoffel criterion is upper semicontinuous even at rank loss.
Article: main_krylov, thm:B. Proof: it is a bounded-below infimum of continuous energies. -/
theorem upperSemicontinuous_christoffel (m : ℕ) (a : ℝ) (x : C(X, ℝ)) :
    UpperSemicontinuous (christoffel m a x) :=
  upperSemicontinuous_ciInf (energy_bddBelow m a x)
    fun p => (continuous_polynomialEnergy x p.val).upperSemicontinuous

end
end krylov.Design
