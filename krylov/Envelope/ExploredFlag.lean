import krylov.Variation.ReferenceFlags

/-!
Article: main_krylov, thm:E and apB:lem:mu, genuine finite explored canonical flags.
Use: give the actual finite-horizon CG flag an empty-prefix convention,
identify its true projected coordinate sum, and prove genuine reference-error
orthogonality also before full ambient exhaustion.
Source: the proved actual CG orthonormal prefix and orthogonal projection
uniqueness on its genuine finite span.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Reference krylov.Variation
open scoped InnerProductSpace BigOperators
variable {n m : ℕ}

/-- The genuine canonical span of the first m actual computed CG unit steps.
Use: The genuine canonical span of the first m actual computed CG unit steps.
Article: main_krylov, thm:E and apB:lem:mu, genuine finite explored canonical flags.
Proof: Finite indexing gives the correct empty-prefix convention. -/
def exploredFlag (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range fun i : Fin m => canonicalCGUnitStep base g i.val)

/-- The actual empty explored CG flag is zero.
Use: The actual empty explored CG flag is zero.
Article: main_krylov, thm:E and apB:lem:mu, genuine finite explored canonical flags.
Proof: Its finite family has no actual generators. -/
theorem exploredFlag_zero (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    exploredFlag base g 0=⊥ := by simp [exploredFlag]

/-- At a positive horizon, the genuine explored prefix flag is exactly the source old flag at index m-minus-one.
Use: At a positive horizon, the genuine explored prefix flag is exactly the source old flag at index m-minus-one.
Article: main_krylov, thm:E and apB:lem:mu, genuine finite explored canonical flags.
Proof: The two genuine generating sets have the same true finite indices. -/
theorem exploredFlag_eq_oldFlag (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) : exploredFlag base g m=oldFlag base g (m-1) := by
  -- Match the actual finite prefix indices, including the source predecessor convention.
  unfold exploredFlag oldFlag
  congr 1
  ext v
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.val,by change i.val ≤ m-1;have := i.isLt;omega,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,by change i ≤ m-1 at hi;omega⟩,rfl⟩

/-- Projection onto a true nondegenerate CG prefix is its actual orthonormal coordinate sum.
Use: Projection onto a true nondegenerate CG prefix is its actual orthonormal coordinate sum.
Article: main_krylov, thm:E and apB:lem:mu, genuine finite explored canonical flags.
Proof: The actual CG prefix is orthonormal. Its finite coordinate sum lies in the true flag, and the difference annihilates every actual generator, so genuine projection uniqueness identifies it. -/
theorem exploredFlag_projection (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hm : m ≤ referenceAtomCount base hb g)
    (v : EuclideanSpace ℝ (Fin n)) :
    (exploredFlag base g m).starProjection v=
      ∑ i : Fin m, inner ℝ (canonicalCGUnitStep base g i.val) v • canonicalCGUnitStep base g i.val := by
  -- Obtain the true orthonormal frame from actual CG nonstagnation rather than assuming a chosen reference basis.
  let q := fun i : Fin m => canonicalCGUnitStep base g i.val
  let P := exploredFlag base g m
  have hq : Orthonormal ℝ q := canonicalCGUnitStep_orthonormal base hb g m
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hm))
  have hGram := orthonormal_iff_ite.mp hq
  apply P.eq_starProjection_of_mem_of_inner_eq_zero
  · exact P.sum_mem fun i _ => P.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)
  · have hker : P ≤ (innerSL ℝ (v-∑ i : Fin m, inner ℝ (q i) v • q i)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change inner ℝ (v-∑ j : Fin m, inner ℝ (q j) v • q j) (q i)=0
      simp [inner_sub_left,sum_inner,real_inner_smul_left,hGram,real_inner_comm v (q i)]
    exact fun w hw => hker hw

/-- The genuine current CG canonical error is orthogonal to its complete actual explored prefix, including the empty and exhausted cases.
Use: The genuine current CG canonical error is orthogonal to its complete actual explored prefix, including the empty and exhausted cases.
Article: main_krylov, thm:E and apB:lem:mu, genuine finite explored canonical flags.
Proof: For a positive horizon reuse the already proved actual old-flag tail orthogonality; the empty case has zero explored space. -/
theorem exploredFlag_error_orthogonal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hm : m ≤ referenceAtomCount base hb g) :
    cgCanonicalError base g m∈(exploredFlag base g m)ᗮ := by
  cases m with
  | zero => simp only [exploredFlag_zero,Submodule.bot_orthogonal_eq_top,Submodule.mem_top]
  | succ k =>
    rw [exploredFlag_eq_oldFlag base g (by omega : 0 < k+1)]
    have ht := remainingTail_orthogonal base hb g k (by omega)
    simpa only [remainingTail,Nat.add_sub_cancel,neg_neg] using (oldFlag base g k)ᗮ.neg_mem ht
end
end krylov.Envelope
