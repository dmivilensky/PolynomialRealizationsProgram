import krylov.Envelope.InvisibleIncrements

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), genuine invisible remainder probes and fresh action.
Use: split the actual finite canonical scenario into its absorbed information fibre and the exactly hidden prefix remainder.
Source: proved source-block invisibility, actual complementary compression and true finite source extension and fresh-defect sums.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual absorbed scenario satisfies the genuine source invisible-block condition.
Use: Every actual absorbed scenario satisfies the genuine source invisible-block condition.
Article: main_krylov, apB:lem:mu(d), genuine invisible remainder probes and fresh action.
Proof: The true complementary output projection is annihilated by the actual old projector. -/
theorem absorbedIncrements_invisible (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    InvisibleIncrements base g (absorbedIncrements base g E) N := by
  intro l _
  apply ContinuousLinearMap.ext
  intro v
  rw [absorbedIncrements_operator]
  change (exploredFlag base g (l+1)).starProjection
    ((exploredFlag base g (l+1))ᗮ.starProjection _)=0
  exact (exploredFlag base g (l+1)).starProjection_apply_eq_zero_iff.mpr
    ((exploredFlag base g (l+1))ᗮ.starProjection_apply_mem _)

/-- The cumulative remainder of a genuine invisible scenario annihilates every actual intermediate CG unit probe.
Use: The cumulative remainder of a genuine invisible scenario annihilates every actual intermediate CG unit probe.
Article: main_krylov, apB:lem:mu(d), genuine invisible remainder probes and fresh action.
Proof: Sum the proved actual zero intermediate actions over the genuine chronological prefix. -/
theorem invisible_remainder_prefix_action (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g) (hInv : InvisibleIncrements base g E N)
    (k : ℕ) (hk : k<N-1) :
    cgOperator (∑ l∈Finset.range k,(E l-absorbedIncrements base g E l)) (canonicalCGUnitStep base g k)=0 := by
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ l∈Finset.range k,(E l-absorbedIncrements base g E l)) _=0
  rw [map_sum,_root_.sum_apply]
  apply Finset.sum_eq_zero
  intro l hl
  exact invisible_remainder_unit_step_zero base hb g E N hcount hInv l k (Finset.mem_range.mp hl) hk

/-- The cumulative increment remainder on the real newest CG unit step equals exactly the genuine printed fresh defect.
Use: The cumulative increment remainder on the real newest CG unit step equals exactly the genuine printed fresh defect.
Article: main_krylov, apB:lem:mu(d), genuine invisible remainder probes and fresh action.
Proof: Sum the actual old projected actions over the true meaningful increments. -/
theorem remainder_last_action_freshDefect (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hN : 0<N) (hcount : N≤referenceAtomCount base hb g) :
    cgOperator (∑ l∈Finset.range (N-1),(E l-absorbedIncrements base g E l))
        (canonicalCGUnitStep base g (N-1))=freshDefect base g E N := by
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ l∈Finset.range (N-1),(E l-absorbedIncrements base g E l)) _=_
  rw [map_sum,_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro l hl
  exact absorbed_remainder_last_unit base hb g E N hN hcount l (Finset.mem_range.mp hl)

/-- Genuine finite source extension preserves actual subtraction.
Use: Genuine finite source extension preserves actual subtraction.
Article: main_krylov, apB:lem:mu(d), genuine invisible remainder probes and fresh action.
Proof: Read the true finite coordinate or use real zero defaults in both arrays. -/
theorem matrixSequenceExtension_sub {p : ℕ}
    (a b : Fin p → Matrix (Fin n) (Fin n) ℝ) :
    matrixSequenceExtension p (a-b)=fun k => matrixSequenceExtension p a k-matrixSequenceExtension p b k := by
  funext k
  by_cases hk : k<p <;> simp only [matrixSequenceExtension,hk,dite_true,dite_false,Pi.sub_apply,sub_self]
end
end krylov.Envelope
