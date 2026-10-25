import polyak.Numerics.Polynomial
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: Appendix B, exact isolation of algebraic transition and critical roots.
Use: an interval, two exact endpoint signs and a derivative sign define one actual root.
Proof: the intermediate value theorem gives existence and the proved derivative
bound gives strict monotonicity and uniqueness. No floating-point root finder is trusted.
-/

noncomputable section
open scoped Polynomial
namespace polyak.Numerics
open LeanCert.Core LeanCert.Engine

/-- Article: a designated algebraic root in a rational interval, with proved uniqueness. -/
structure IsolatedRoot (p : ℚ[X]) (I : IntervalRat) where
  /-- Article: the actual real algebraic number. -/
  value : ℝ
  /-- Article: rational root enclosure. -/
  mem : value ∈ I
  /-- Article: its exact defining equation. -/
  root : Polynomial.aeval value p = 0
  /-- Article: the interval isolates exactly one real root. -/
  unique : ∀ x ∈ I, Polynomial.aeval x p = 0 → x=value

/-- Article: exact endpoint signs and derivative positivity isolate a simple real root. -/
theorem exists_isolatedRoot {p : ℚ[X]} (I : IntervalRat)
    (ha : Polynomial.aeval (I.lo : ℝ) p < 0) (hb : 0 < Polynomial.aeval (I.hi : ℝ) p)
    (hd : ∀ x ∈ I, 0 < Polynomial.aeval x p.derivative) :
    Nonempty (IsolatedRoot p I) := by
  have hab : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  have hcont := p.continuous_aeval (A := ℝ)
  obtain ⟨x,hx,hroot⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨ha.le,hb.le⟩
  have hmono : StrictMonoOn (fun x : ℝ => Polynomial.aeval x p) (Set.Icc (I.lo : ℝ) I.hi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont.continuousOn
    intro y hy
    rw [(p.hasDerivAt_aeval y).deriv]
    exact hd y ((interior_subset hy : y ∈ Set.Icc (I.lo : ℝ) I.hi))
  refine ⟨⟨x,hx,hroot,fun y hy hyr => ?_⟩⟩
  exact hmono.injOn hy hx (hyr.trans hroot.symm)

/-- Article: root isolation from a finite exact Bernstein derivative certificate. -/
theorem isolatedRoot_of_bernstein {p : ℚ[X]} (I : IntervalRat)
    (derivativeCode : PolynomialCode p.derivative) (depth : ℕ)
    (ha : Polynomial.aeval (I.lo : ℝ) p < 0) (hb : 0 < Polynomial.aeval (I.hi : ℝ) p)
    (hc : QPoly.bernsteinCheck .strictLower derivativeCode.code 0 I depth = true) :
    Nonempty (IsolatedRoot p I) :=
  exists_isolatedRoot I ha hb (derivativeCode.positive I depth hc)

/-- Article: every isolated root obtained with positive derivative is simple. -/
theorem IsolatedRoot.simple {p : ℚ[X]} {I : IntervalRat} (r : IsolatedRoot p I)
    (hd : ∀ x ∈ I, 0 < Polynomial.aeval x p.derivative) :
    Polynomial.aeval r.value p.derivative ≠ 0 := (hd r.value r.mem).ne'

end polyak.Numerics
