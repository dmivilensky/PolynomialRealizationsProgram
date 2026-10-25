import chebyshev2.GroundState.Variational
import chebyshev2.Continuum.Fredholm

/-!
Article: chebyshev2, Definition 3.
Definition 3, with exactly the article's constraints.
Use: `chebyshev2.Filters.CompactDensity.relaxed_iff` feeds
`chebyshev2.DualCertificate.AnalyticData.relaxed_energy_ge_target` (Theorem 3.6(i), once the
state criterion has been supplied).
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real chebyshev2.Continuum chebyshev2.GroundState

/--
A bounded, compactly supported probability density with pointwise nonnegativity. Its proof
fields enable embedding into the broader measurable relaxed density class.

Use: `chebyshev2.Filters.CompactDensity.H` uses this record of data and proof obligations
in the displayed construction of `H`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.
-/
structure CompactDensity where
  /-- The compactly supported density to be embedded into the relaxed class. -/
  value : ℝ → ℝ
  /-- Its total mass and associated integral operators are well-defined. -/
  integrable : Integrable value
  /-- Pointwise nonnegativity needed for positive Green/filter operators. -/
  nonneg : ∀ x, 0 ≤ value x
  /-- A finite upper bound for the density, used in regularity and approximation arguments. -/
  bounded : ∃ B : ℝ, ∀ x, value x ≤ B
  /-- The density vanishes outside a compact set. -/
  compactSupport : HasCompactSupport value
  /-- The probability normalization of the density. -/
  mass_one : (∫ x, value x)=1

namespace CompactDensity

/--
Defines `coupling` of type `ℝ` by `groundParameter m.integrable m.nonneg`.

Use: `chebyshev2.Filters.CompactDensity.observations` uses this definition in the displayed
construction of `observations`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.
-/
def coupling (m : CompactDensity) : ℝ := groundParameter m.integrable m.nonneg
/--
Defines `spectrum` of type `ℕ → ℝ` by `kernelEigenvalue m.integrable m.nonneg`.

Use: `chebyshev2.Filters.CompactDensity.H` uses this definition in the displayed
construction of `H`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.
-/
def spectrum (m : CompactDensity) : ℕ → ℝ := kernelEigenvalue m.integrable m.nonneg
/--
Defines `H` of type `ℝ` by `logDeterminant m.spectrum s`.

Use: `chebyshev2.Filters.CompactDensity.observations` uses this definition in the displayed
construction of `observations`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.
-/
def H (m : CompactDensity) (s : ℝ) : ℝ := logDeterminant m.spectrum s

/--
Defines `observations` of type `ℝ × ℝ × ℝ × ℝ` by `(m.H 32,m.H 64,m.H (sigma*m.coupling),∑' j,
(m.spectrum j)^2)`.

Use: `chebyshev2.Filters.CompactDensity.relaxed` uses this definition in the displayed
construction of `relaxed`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.
-/
def observations (m : CompactDensity) (sigma : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (m.H 32,m.H 64,m.H (sigma*m.coupling),∑' j, (m.spectrum j)^2)

/--
Defines `target` of type `ℝ × ℝ × ℝ × ℝ` by `(log (cosh (sqrt 32)),log (cosh (sqrt 64)),log
(cosh (sqrt (sigma*(Real.pi^2/4)))),2/3)`.

Use: `chebyshev2.Filters.CompactDensity.relaxed` uses this definition in the displayed
construction of `relaxed`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.
-/
def target (sigma : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (log (cosh (sqrt 32)),log (cosh (sqrt 64)),log (cosh (sqrt (sigma*(Real.pi^2/4)))),2/3)

/--
Defines `relaxed` of type `Set CompactDensity` by `{m | m.coupling=Real.pi^2/4 ∧ m.observations
sigma=target sigma}`.

Use: `chebyshev2.Filters.CompactDensity.relaxed_iff` rewrites with this definition to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.
-/
def relaxed (sigma : ℝ) : Set CompactDensity :=
  {m | m.coupling=Real.pi^2/4 ∧ m.observations sigma=target sigma}

/--
The stated quantitative bound `0 < m.coupling`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Definition 3.

Proof: Use the identities/estimates `chebyshev2.GroundState.groundParameter_positive` with
the arguments shown in the proof.
-/
theorem coupling_positive (m : CompactDensity) : 0 < m.coupling :=
  groundParameter_positive m.integrable m.nonneg (by rw [m.mass_one]; norm_num)

/--
Equivalence of the displayed criteria: `m ∈ relaxed sigma ↔ m.coupling=Real.pi^2/4 ∧ m.H 32=log
(cosh (sqrt 32)) ∧ m.H 64=log (cosh (sqrt 64)) ∧ m.H (sigma*m.coupling)=log (cosh (sqrt
(sigma*(Real.pi^2/4)))) ∧ (∑' j, (m.spectrum j)^2)=2/3`.

Use: `chebyshev2.DualCertificate.AnalyticData.relaxed_energy_ge_target` uses this identity
to prove the bound `A.targetValue ≤ ∫ x, (sqrt (m.value x))^3`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem relaxed_iff (m : CompactDensity) (sigma : ℝ) : m ∈ relaxed sigma ↔
    m.coupling=Real.pi^2/4 ∧ m.H 32=log (cosh (sqrt 32)) ∧ m.H 64=log (cosh (sqrt 64)) ∧
    m.H (sigma*m.coupling)=log (cosh (sqrt (sigma*(Real.pi^2/4)))) ∧ (∑' j, (m.spectrum j)^2)=2/3 := by simp only [relaxed,mem_ofPred_eq,observations,target,Prod.mk.injEq]

end CompactDensity
end
end chebyshev2.Filters
