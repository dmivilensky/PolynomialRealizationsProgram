import krylov.Envelope.FlagOrthogonality
import krylov.Envelope.CanonicalPolynomialFlags
import krylov.Envelope.CanonicalResponseFormula

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(b), genuine absorbed invariance of the common unexplored response.
Use: prove actual canonical absorbed compression leaves the true common
unexplored first variation unchanged, by genuine finite polynomial flag
propagation on real active CG prefixes, including exhaustion.
Source: actual complementary-flag compression, true later CG step
orthogonality and genuine measured continuation degree bounds.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Polynomial Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- For a genuine complementary-flag vector, the actual increment action removed by true absorbed compression belongs exactly to the real explored flag.
Use: For a genuine complementary-flag vector, the actual increment action removed by true absorbed compression belongs exactly to the real explored flag.
Article: main_krylov, apB:lem:mu(b), genuine absorbed invariance of the common unexplored response.
Proof: The actual right complementary projector fixes the genuine vector, while the true omitted left complementary projection leaves precisely the real explored projection. -/
theorem absorbedIncrements_action_difference (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v∈(exploredFlag base g (l+1))ᗮ) :
    cgOperator (E l) v-cgOperator (absorbedIncrements base g E l) v∈exploredFlag base g (l+1) := by
  rw [absorbedIncrements_operator]
  let P := exploredFlag base g (l+1)
  have hv' : Pᗮ.starProjection v=v := Submodule.starProjection_eq_self_iff.mpr hv
  change cgOperator (E l) v-Pᗮ.starProjection (cgOperator (E l) (Pᗮ.starProjection v))∈P
  rw [hv',P.starProjection_orthogonal_val,sub_sub_cancel]
  exact P.starProjection_apply_mem _

/-- The true difference between actual canonical frozen responses before and after genuine absorbed compression belongs to the real final explored CG flag.
Use: The true difference between actual canonical frozen responses before and after genuine absorbed compression belongs to the real final explored CG flag.
Article: main_krylov, apB:lem:mu(b), genuine absorbed invariance of the common unexplored response.
Proof: Every actual removed increment on a genuine later CG step belongs to its true earlier flag. Actual continuation polynomial degree bounds propagate all real omitted responses into the genuine final explored flag. -/
theorem canonicalFrozenResponse_absorbed_difference (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g) :
    canonicalFrozenResponse base g (canonicalFCPath base E) N-
      canonicalFrozenResponse base g (canonicalFCPath base (absorbedIncrements base g E)) N∈exploredFlag base g N := by
  -- Every genuine removed increment acts only into an actual earlier flag; true continuation degrees keep its real propagated response explored.
  rw [canonicalFrozenResponse_formula base hb,canonicalFrozenResponse_formula base hb,← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [← map_sub]
  have hsource : cgOperator (∑ l∈Finset.range i,E l) (canonicalCGStep base g i)-
      cgOperator (∑ l∈Finset.range i,absorbedIncrements base g E l) (canonicalCGStep base g i)∈exploredFlag base g i := by
    simp only [cgOperator,map_sum,_root_.sum_apply]
    rw [← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro l hl
    have hl' := Finset.mem_range.mp hl
    have hv := canonicalCGStep_later_orthogonal base hb g N (l+1) i hcount (by omega) hi'
    exact exploredFlag_mono base g (show l+1≤ i by omega) (absorbedIncrements_action_difference base g E l _ hv)
  apply canonical_polynomial_mem_flag base hb g N i hcount _ hsource
  have hd := (continuation_degree (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g) (i+1) (N-(i+1))).1
  omega

/-- The actual common unexplored first variation is exactly invariant under genuine absorbed canonical scenario compression.
Use: The actual common unexplored first variation is exactly invariant under genuine absorbed canonical scenario compression.
Article: main_krylov, apB:lem:mu(b), genuine absorbed invariance of the common unexplored response.
Proof: The true canonical frozen-response difference belongs to the actual explored flag and is therefore removed exactly by the genuine orthogonal complementary projector. -/
theorem commonTransverseResponse_absorbedIncrements (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g) :
    commonTransverseResponse base g (canonicalFCPath base (absorbedIncrements base g E)) N=
      commonTransverseResponse base g (canonicalFCPath base E) N := by
  let P := exploredFlag base g N
  -- The actual difference of genuine frozen responses is fixed by the true explored projector, so their real complementary responses coincide.
  let FE := canonicalFrozenResponse base g (canonicalFCPath base E) N
  let FF := canonicalFrozenResponse base g (canonicalFCPath base (absorbedIncrements base g E)) N
  have hm : FE-FF∈P := canonicalFrozenResponse_absorbed_difference base hb g E N hcount
  have hp : P.starProjection FE-P.starProjection FF=FE-FF := by
    rw [← map_sub]
    exact Submodule.starProjection_eq_self_iff.mpr hm
  change FF-P.starProjection FF=FE-P.starProjection FE
  apply sub_eq_sub_iff_add_eq_add.mpr
  have he := sub_eq_sub_iff_add_eq_add.mp hp
  exact (add_comm _ _).trans he
end
end krylov.Envelope
