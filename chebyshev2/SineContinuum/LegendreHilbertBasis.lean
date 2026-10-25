import chebyshev2.SineContinuum.LegendreNorm
import chebyshev2.SineContinuum.LegendrePolynomialBasis
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Article: chebyshev2, Proposition 2.
An actual complete Hilbert basis, with exact normalized polynomial representatives in Lebesgue L².
Use: `chebyshev2.SineContinuum.legendreHilbertBasis_apply` feeds
`chebyshev2.SineContinuum.standardLegendreHilbertBasis_ae` (standard Legendre Hilbert Basis ae).
Proof chain: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` — chebyshev2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Polynomial Real MeasureTheory Set
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Measure.Subtype.measureSpace

/--
Defines `LegendreInterval` of type `` by `Icc (0:ℝ) 1`.

Use: `chebyshev2.SineContinuum.polynomialL2` uses this definition in the displayed
construction of `polynomialL2`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
abbrev LegendreInterval := Icc (0:ℝ) 1
/--
Defines `LegendreSpace` of type `` by `Lp ℝ 2 (volume : Measure LegendreInterval)`.

Use: `chebyshev2.SineContinuum.normalizedLegendre_span_dense` uses this definition to
establish exact identity `(Submodule.span ℝ (range normalizedLegendre)).topologicalClosure=⊤`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
abbrev LegendreSpace := Lp ℝ 2 (volume : Measure LegendreInterval)

/--
Supplies the typeclass structure specified by `IsFiniteMeasure (volume : Measure
LegendreInterval)`. This lets subsequent generic library results apply to this concrete type.

Use: `chebyshev2.SineContinuum.polynomialL2` uses this typeclass instance in the displayed
construction of `polynomialL2`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.sineOperator_domain_eq_range`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
instance legendreInterval_finiteMeasure : IsFiniteMeasure (volume : Measure LegendreInterval) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/--
Defines `polynomialL2` of type `Polynomial ℝ →ₗ[ℝ] LegendreSpace` by `(ContinuousMap.toLp 2
volume ℝ).toLinearMap.comp (Polynomial.toContinuousMapOnAlgHom LegendreInterval).toLinearMap`.

Use: `chebyshev2.SineContinuum.normalizedLegendre` uses this definition in the displayed
construction of `normalizedLegendre`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def polynomialL2 : Polynomial ℝ →ₗ[ℝ] LegendreSpace :=
  (ContinuousMap.toLp 2 volume ℝ).toLinearMap.comp
    (Polynomial.toContinuousMapOnAlgHom LegendreInterval).toLinearMap

/--
Exact identity `polynomialL2 p=ᵐ[volume] (fun x : LegendreInterval => p.eval x)`.

Use: `chebyshev2.SineContinuum.polynomialL2_inner` uses this identity to establish exact
identity `inner ℝ (polynomialL2 p) (polynomialL2 q)=polynomialIntegral (p*q)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem polynomialL2_ae (p : Polynomial ℝ) :
    polynomialL2 p=ᵐ[volume] (fun x : LegendreInterval => p.eval x) :=
  ContinuousMap.coeFn_toLp volume (p.toContinuousMapOn LegendreInterval)

/--
Exact identity `inner ℝ (polynomialL2 p) (polynomialL2 q)=polynomialIntegral (p*q)`.

Use: `chebyshev2.SineContinuum.normalizedLegendre_orthonormal` rewrites with this identity
to establish `Orthonormal ℝ normalizedLegendre`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem polynomialL2_inner (p q : Polynomial ℝ) :
    inner ℝ (polynomialL2 p) (polynomialL2 q)=polynomialIntegral (p*q) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [L2.inner_def]
  have he : (fun x : LegendreInterval => inner ℝ (polynomialL2 p x) (polynomialL2 q x))=ᵐ[volume]
      (fun x : LegendreInterval => p.eval (x:ℝ)*q.eval (x:ℝ)) := by
    filter_upwards [polynomialL2_ae p,polynomialL2_ae q] with x hp hq
    rw [hp,hq]
    change q.eval (x:ℝ)*p.eval (x:ℝ)=p.eval (x:ℝ)*q.eval (x:ℝ)
    ring
  rw [integral_congr_ae he]
  rw [integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc (fun x : ℝ => p.eval x*q.eval x)]
  change (∫ x in Icc (0:ℝ) 1, p.eval (x:ℝ)*q.eval (x:ℝ))=(∫ x in (0:ℝ)..1, (p*q).eval x)
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc]
  simp only [eval_mul]

/--
The precise assertion is `DenseRange polynomialL2`.

Use: `chebyshev2.SineContinuum.normalizedLegendre_span_dense` rewrites with this assertion
to establish the identity `(Submodule.span ℝ (range
normalizedLegendre)).topologicalClosure=⊤`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem polynomialL2_denseRange : DenseRange polynomialL2 := by
  have hp : DenseRange (Polynomial.toContinuousMapOnAlgHom LegendreInterval) := by
    rw [denseRange_iff_closure_range,← polynomialFunctions_coe,
      ← Subalgebra.topologicalClosure_coe,polynomialFunctions.topologicalClosure]
    rfl
  exact (ContinuousMap.toLp_denseRange ℝ volume (p := 2) ℝ (by norm_num)).comp hp
    (ContinuousMap.toLp 2 volume ℝ).continuous

/--
Defines `normalizedLegendre` of type `LegendreSpace` by `√(2*(n:ℝ)+1) • polynomialL2 (shifted
n)`.

Use: `chebyshev2.SineContinuum.normalizedLegendre_orthonormal` rewrites with this
definition to establish `Orthonormal ℝ normalizedLegendre`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def normalizedLegendre (n : ℕ) : LegendreSpace :=
  √(2*(n:ℝ)+1) • polynomialL2 (shifted n)

/--
The precise assertion is `Orthonormal ℝ normalizedLegendre`.

Use: `chebyshev2.SineContinuum.legendreHilbertBasis` uses this assertion in the displayed
construction of `legendreHilbertBasis`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalizedLegendre_orthonormal : Orthonormal ℝ normalizedLegendre := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [orthonormal_iff_ite]
  intro n j
  rw [normalizedLegendre,normalizedLegendre,inner_smul_left,inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  rw [polynomialL2_inner]
  split_ifs with h
  · subst j
    change √(2*(n:ℝ)+1)*(√(2*(n:ℝ)+1)*legendreNorm n)=1
    rw [legendre_norm]
    have hn : 0 < 2*(n:ℝ)+1 := by positivity
    rw [← mul_assoc,Real.mul_self_sqrt hn.le]
    field_simp
  · have hz : polynomialIntegral (shifted n*shifted j)=0 := by
      change (∫ x in (0:ℝ)..1, (shifted n*shifted j).eval x)=0
      simpa only [eval_mul, legendreValue] using legendre_orthogonal h
    rw [hz,mul_zero,mul_zero]

/--
Exact identity `(Submodule.span ℝ (range normalizedLegendre)).topologicalClosure=⊤`.

Use: `chebyshev2.SineContinuum.legendreHilbertBasis` uses this identity in the displayed
construction of `legendreHilbertBasis`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Induct on `hp`; the recursive step uses the previous-stage assertion.
-/
theorem normalizedLegendre_span_dense :
    (Submodule.span ℝ (range normalizedLegendre)).topologicalClosure=⊤ := by
  -- Induct on `hp`; the recursive step uses the previous-stage assertion.
  let S := Submodule.span ℝ (range normalizedLegendre)
  have hm : ∀ n, polynomialL2 (shifted n) ∈ S := by
    intro n
    have hn : √(2*(n:ℝ)+1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have h := S.smul_mem (√(2*(n:ℝ)+1))⁻¹ (Submodule.subset_span (mem_range_self n))
    simpa only [normalizedLegendre,smul_smul,inv_mul_cancel₀ hn,one_smul] using h
  have hs : ∀ p, polynomialL2 p ∈ S := by
    intro p
    have hp : p ∈ Submodule.span ℝ (range shifted) := by rw [shifted_span]; trivial
    induction hp using Submodule.span_induction with
    | mem p hp => obtain ⟨n,rfl⟩ := hp; exact hm n
    | zero => simpa only [map_zero] using S.zero_mem
    | add p q _ _ hp hq => simpa only [map_add] using S.add_mem hp hq
    | smul c p _ hp => simpa only [map_smul] using S.smul_mem c hp
  apply top_unique
  intro v _
  have hv : v ∈ closure (range polynomialL2) := by rw [polynomialL2_denseRange.closure_range]; trivial
  exact closure_mono (range_subset_iff.mpr hs) hv

/--
An actual complete Hilbert basis, with exact normalized polynomial representatives in Lebesgue
L². Endpoints are null and have no effect.

Use: `chebyshev2.SineContinuum.legendreHilbertBasis_apply` uses this definition to
establish exact identity `legendreHilbertBasis n=normalizedLegendre n`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendreHilbertBasis : HilbertBasis ℕ ℝ LegendreSpace :=
  HilbertBasis.mk normalizedLegendre_orthonormal (by rw [normalizedLegendre_span_dense])

/--
Exact identity `legendreHilbertBasis n=normalizedLegendre n`.

Use: `chebyshev2.SineContinuum.sineHilbertBasis_ae` rewrites with this identity to
establish exact identity `sineHilbertBasis n=ᵐ[volume] (fun t : LegendreInterval => upsilon n
t)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem legendreHilbertBasis_apply (n : ℕ) : legendreHilbertBasis n=normalizedLegendre n :=
  congrFun (HilbertBasis.coe_mk _ _) n

end
end chebyshev2.SineContinuum
