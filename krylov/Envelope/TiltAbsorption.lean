import krylov.Envelope.CanonicalInjectionPairing
import krylov.Envelope.DirectionTiltGeometry
import krylov.Envelope.FlagOrthogonality

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(b) and thm:select, true absorbed invariance of the common tilt.
Use: prove the genuine actual common frozen tilt depends only on the
true complementary canonical increment blocks absorbed by the latest
information model, on every real active prefix including exhaustion.
Source: actual frozen direction impulse sums, genuine canonical injection
pairings and true polynomial-degree old-flag orthogonality.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Polynomial Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine actual common tilt is exactly invariant under true absorbed canonical increment compression.
Use: The genuine actual common tilt is exactly invariant under true absorbed canonical increment compression.
Article: main_krylov, apB:lem:mu(b) and thm:select, true absorbed invariance of the common tilt.
Proof: Unroll each real measured frozen displacement step into actual direction-polynomial injections. The genuine canonical tilt vector and actual later CG step are both orthogonal to every true earlier increment flag, so actual complementary compression preserves each real increment pairing and hence the entire genuine tilt. -/
theorem commonTilt_absorbedIncrements (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    commonTilt base g (canonicalFCPath base (absorbedIncrements base g E)) N=
      commonTilt base g (canonicalFCPath base E) N := by
  -- Reduce each actual tilt coordinate to its genuine frozen direction injections and true canonical increment pairings.
  unfold commonTilt
  apply Finset.sum_congr rfl
  intro i _
  have hpair : inner ℝ (CG.gradient (cgOperator base) g N)
      (frozenDisplacement (cgOperator base) (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g)
        (referenceInjection (cgOperator base) g (canonicalFCPath base (absorbedIncrements base g E))) (i.val+1)-
       frozenDisplacement (cgOperator base) (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g)
        (referenceInjection (cgOperator base) g (canonicalFCPath base (absorbedIncrements base g E))) i.val)=
    inner ℝ (CG.gradient (cgOperator base) g N)
      (frozenDisplacement (cgOperator base) (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g)
        (referenceInjection (cgOperator base) g (canonicalFCPath base E)) (i.val+1)-
       frozenDisplacement (cgOperator base) (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g)
        (referenceInjection (cgOperator base) g (canonicalFCPath base E)) i.val) := by
    rw [frozen_displacement_step,frozen_displacement_step,real_inner_smul_right,real_inner_smul_right]
    apply congrArg (fun x : ℝ => CG.length (cgOperator base) g i.val*x)
    rw [frozen_direction_formula,frozen_direction_formula]
    simp only [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hji := Finset.mem_range.mp hj
    rw [canonical_injection_pairing base hb g (absorbedIncrements base g E),canonical_injection_pairing base hb g E]
    change inner ℝ (directionTiltVector base g N i.val j)
      (cgOperator (∑ l∈Finset.range j,absorbedIncrements base g E l) (canonicalCGStep base g j))=
      inner ℝ (directionTiltVector base g N i.val j)
        (cgOperator (∑ l∈Finset.range j,E l) (canonicalCGStep base g j))
    simp only [cgOperator,map_sum,_root_.sum_apply,inner_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hlj := Finset.mem_range.mp hl
    -- The genuine direction-polynomial degree and actual later CG step make both true test vectors complementary to each real earlier increment flag.
    have hb' := directionTiltVector_orthogonal base hb g N i.val j hcount i.isLt hji
    have hbu : directionTiltVector base g N i.val j∈(exploredFlag base g (l+1))ᗮ :=
      Submodule.orthogonal_le (exploredFlag_mono base g (show l+1≤j+1 by omega)) hb'
    have hcv := canonicalCGStep_later_orthogonal base hb g N (l+1) j hcount (by omega) (hji.trans i.isLt)
    exact absorbedIncrements_pairing base g E l _ _ hbu hcv
  rw [hpair]
end
end krylov.Envelope
