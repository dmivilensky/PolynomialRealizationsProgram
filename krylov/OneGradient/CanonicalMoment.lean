import krylov.Completion.StrictJacobiBand
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), free canonical moment and collapsed boundary.
Use: retain the full source canonical parameter on every nondegenerate original
interval, and treat the genuinely possible collapsed physical interval separately.
Source: normalized real interval coordinates; the two-site certificate proves
that the source's unqualified freedom assertion needs a nondegeneracy hypothesis.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.LinearAlgebra krylov.Completion

/-- The actual normalized missing Jacobi pivot on its original endpoint interval.
Use: this is the canonical moment of the source's first missing spectral moment.
Article: main_krylov, s5:moment(b), p=(b-b_minus)/(b_plus-b_minus). -/
def canonicalPivot (lo hi b : ℝ) : ℝ := (b-lo)/(hi-lo)

/-- The canonical moment belongs to the whole unit interval on every true
nondegenerate physical pivot interval.
Use: no division by a vanishing endpoint gap is hidden in the original parameter.
Article: main_krylov, s5:moment(b).
Proof: the actual positive endpoint gap preserves both original endpoint inequalities. -/
theorem canonical_pivot_mem {lo hi b : ℝ} (hgap : lo < hi) (hb : b∈Set.Icc lo hi) :
    canonicalPivot lo hi b∈Set.Icc 0 1 := by
  have hpos : 0 < hi-lo := sub_pos.mpr hgap
  constructor
  · exact div_nonneg (sub_nonneg.mpr hb.1) hpos.le
  · exact (div_le_one hpos).mpr (sub_le_sub_right hb.2 lo)

/-- Every original canonical moment in the unit interval is attained on a
nondegenerate physical pivot interval by its true affine preimage.
Use: the source's canonical moment is genuinely free once its endpoint gap is positive.
Article: main_krylov, s5:moment(b).
Proof: construct the real interval point and cancel only the actual nonzero endpoint gap. -/
theorem canonical_pivot_attainment {lo hi p : ℝ} (hgap : lo < hi) (hp : p∈Set.Icc 0 1) :
    lo+p*(hi-lo)∈Set.Icc lo hi ∧ canonicalPivot lo hi (lo+p*(hi-lo))=p := by
  have hpos : 0 < hi-lo := sub_pos.mpr hgap
  constructor
  · constructor
    · exact le_add_of_nonneg_right (mul_nonneg hp.1 hpos.le)
    · have hm := mul_le_mul_of_nonneg_right hp.2 hpos.le
      nlinarith
  · unfold canonicalPivot
    rw [add_sub_cancel_left,mul_div_cancel_right₀ _ hpos.ne']

/-- The complete canonical parameter image is the unit interval on every
nondegenerate physical missing-pivot interval.
Use: state actual freedom as a set equality with every point attained.
Article: main_krylov, s5:moment(b).
Proof: combine the real interval membership and its explicit actual affine preimages. -/
theorem canonical_pivot_range {lo hi : ℝ} (hgap : lo < hi) :
    canonicalPivot lo hi '' Set.Icc lo hi=Set.Icc 0 1 := by
  ext p
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact canonical_pivot_mem hgap hb
  · intro hp
    obtain ⟨hb,he⟩ := canonical_pivot_attainment hgap hp
    exact ⟨_,hb,he⟩

/-- A collapsed actual information interval has one fixed pivot and one fixed
missing moment; its totalized canonical coordinate has only the value zero.
Use: the source's freedom assertion is restricted to positive interval width.
Article: main_krylov, s5:moment(b), collapsed boundary case.
Proof: the true closed interval is a singleton and the totalized zero-gap quotient is zero. -/
theorem canonical_pivot_collapsed (b : ℝ) :
    canonicalPivot b b '' Set.Icc b b=({0} : Set ℝ) := by
  simp [canonicalPivot]

/-- A genuine irreducible two-site spectral completion family can have a
collapsed admissible interval even with strictly positive leading spectral margins.
Use: certify that the positive-gap hypothesis in canonical freedom is necessary;
the original source's unqualified formulation cannot cover this boundary case.
Article: main_krylov, s5:moment(b), nondegeneracy qualification.
Proof: take the actual fixed leading entry two, coupling one and physical
spectral band [1,3]. Both strict leading shifts equal the identity, and the
proved closed Schur interval is exactly [2,2]. -/
theorem two_site_spectral_interval_collapsed (b : ℝ) :
    let H := scalarCorner 2
    let x : Fin 1 → ℝ := fun _ => 1
    let J := fromBlocks (scalarCorner b) (crossColumn x)ᵀ (crossColumn x) H
    (J-(1 : ℝ) • 1).PosSemidef ∧ ((3 : ℝ) • 1-J).PosSemidef ↔ b=2 := by
  let H := scalarCorner 2
  let x : Fin 1 → ℝ := fun _ => 1
  have hlow : H-(1 : ℝ) • 1=(1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [H,scalarCorner,Matrix.smul_apply]
  have hhigh : (3 : ℝ) • 1-H=(1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [H,scalarCorner,Matrix.smul_apply]
  have hL : (H-(1 : ℝ) • 1).PosDef := by
    rw [hlow]
    exact Matrix.PosDef.one
  have hH : ((3 : ℝ) • 1-H).PosDef := by
    rw [hhigh]
    exact Matrix.PosDef.one
  have he := strict_scalar_band_iff H x b 1 3 hL hH
  have hxx : x ⬝ᵥ x=1 := by norm_num [x,dotProduct,Fin.sum_univ_one]
  simp only [hlow,hhigh] at he
  simp only [inv_one,Matrix.one_mulVec,hxx] at he
  norm_num at he
  constructor
  · intro h
    obtain ⟨hl,hu⟩ := he.mp (by simpa only [one_smul] using h)
    linarith
  · intro hb
    subst b
    simpa only [one_smul] using he.mpr ⟨le_rfl,le_rfl⟩

end
end krylov.OneGradient
