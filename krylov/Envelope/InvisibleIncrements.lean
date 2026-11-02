import krylov.Envelope.FreshDefect
import krylov.Envelope.ScenarioAbsorption

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), the genuine invisible-scenario block condition.
Use: express the printed old-projector/increment/intermediate-tail zero block on the actual finite CG flags and derive its true probe actions.
Source: genuine complementary compression, actual orthonormal CG prefixes and standard orthogonal projection splitting.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual source invisibility condition is the vanishing old-increment-intermediate-tail operator block.
Use: The actual source invisibility condition is the vanishing old-increment-intermediate-tail operator block.
Article: main_krylov, apB:lem:mu(d), the genuine invisible-scenario block condition.
Proof: Use the difference of the true predecessor and old projectors for the printed intermediate-tail projector. -/
def InvisibleIncrements (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) : Prop :=
  ∀ l<N-1, (exploredFlag base g (l+1)).starProjection ∘L cgOperator (E l) ∘L
    ((exploredFlag base g (N-1)).starProjection-(exploredFlag base g (l+1)).starProjection)=0

/-- On the genuine old-flag complement the increment remainder is exactly its true old projected action.
Use: On the genuine old-flag complement the increment remainder is exactly its true old projected action.
Article: main_krylov, apB:lem:mu(d), the genuine invisible-scenario block condition.
Proof: Split the actual image into its genuine old and complementary orthogonal projections. -/
theorem absorbed_remainder_complement_action (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v∈(exploredFlag base g (l+1))ᗮ) :
    cgOperator (E l-absorbedIncrements base g E l) v=
      (exploredFlag base g (l+1)).starProjection (cgOperator (E l) v) := by
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (E l-absorbedIncrements base g E l) v=_
  rw [map_sub]
  change cgOperator (E l) v-cgOperator (absorbedIncrements base g E l) v=_
  rw [absorbedIncrements_operator]
  change cgOperator (E l) v-(exploredFlag base g (l+1))ᗮ.starProjection
    (cgOperator (E l) ((exploredFlag base g (l+1))ᗮ.starProjection v))=_
  rw [Submodule.starProjection_eq_self_iff.mpr hv]
  exact sub_eq_iff_eq_add.mpr ((exploredFlag base g (l+1)).starProjection_add_starProjection_orthogonal _).symm

/-- An invisible increment remainder annihilates every actual intermediate CG unit step.
Use: An invisible increment remainder annihilates every actual intermediate CG unit step.
Article: main_krylov, apB:lem:mu(d), the genuine invisible-scenario block condition.
Proof: The intermediate unit step lies in the genuine tail projector and is orthogonal to the real old flag. -/
theorem invisible_remainder_unit_step_zero (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g) (hInv : InvisibleIncrements base g E N)
    (l k : ℕ) (hlk : l<k) (hk : k<N-1) :
    cgOperator (E l-absorbedIncrements base g E l) (canonicalCGUnitStep base g k)=0 := by
  -- The genuine intermediate CG unit step lies in the exact tail block appearing in the source condition.
  have horth : canonicalCGUnitStep base g k∈(exploredFlag base g (l+1))ᗮ := by
    have hs := canonicalCGStep_later_orthogonal base hb g N (l+1) k hcount (by omega) (by omega)
    exact Submodule.smul_mem _ _ hs
  rw [absorbed_remainder_complement_action base g E l _ horth]
  have hv : canonicalCGUnitStep base g k∈exploredFlag base g (N-1) :=
    Submodule.subset_span ⟨(⟨k,hk⟩ : Fin (N-1)),rfl⟩
  have he := congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
    T (canonicalCGUnitStep base g k)) (hInv l (by omega))
  change (exploredFlag base g (l+1)).starProjection (cgOperator (E l)
    ((exploredFlag base g (N-1)).starProjection (canonicalCGUnitStep base g k)-
      (exploredFlag base g (l+1)).starProjection (canonicalCGUnitStep base g k)))=0 at he
  rw [Submodule.starProjection_eq_self_iff.mpr hv,
    (exploredFlag base g (l+1)).starProjection_apply_eq_zero_iff.mpr horth,sub_zero] at he
  exact he

/-- The actual increment remainder on the newest CG unit step is precisely its true old projected fresh defect.
Use: The actual increment remainder on the newest CG unit step is precisely its true old projected fresh defect.
Article: main_krylov, apB:lem:mu(d), the genuine invisible-scenario block condition.
Proof: Use genuine old-flag orthogonality and identify the actual predecessor explored flag with its true old-flag convention. -/
theorem absorbed_remainder_last_unit (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hN : 0<N) (hcount : N≤referenceAtomCount base hb g) (l : ℕ) (hl : l<N-1) :
    cgOperator (E l-absorbedIncrements base g E l) (canonicalCGUnitStep base g (N-1))=
      (oldFlag base g l).starProjection (cgOperator (E l) (canonicalCGUnitStep base g (N-1))) := by
  have horth : canonicalCGUnitStep base g (N-1)∈(exploredFlag base g (l+1))ᗮ := by
    have hs := canonicalCGStep_later_orthogonal base hb g N (l+1) (N-1) hcount (by omega) (by omega)
    exact Submodule.smul_mem _ _ hs
  rw [absorbed_remainder_complement_action base g E l _ horth,exploredFlag_eq_oldFlag base g (show 0<l+1 by omega)]
  simp only [Nat.add_sub_cancel]
end
end krylov.Envelope
