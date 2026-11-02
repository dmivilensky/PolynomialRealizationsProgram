import krylov.Variation.SpectralResponse
import Mathlib.Algebra.BigOperators.Intervals

/-!
Article: main_krylov, thm:A, exact coordinates of the spatial reference response.
Use: identify the differentiated real FC staircase with the already constructed
sharp canonical response operator, using the genuine full CG frame.
Source: orthogonal old flags, true CG tail sums and finite triangular summation.
-/

namespace krylov.Variation
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant
open scoped InnerProductSpace BigOperators
variable {n : ℕ}

/-- Every later true canonical CG unit step is orthogonal to each earlier actual old flag.
Use: spatial reference response coordinates select exactly the earlier increment flags.
Article: main_krylov, thm:A, orthogonal reference flags.
Proof: the genuine CG frame makes every earlier generator orthogonal to the later unit step; this extends to their actual span. -/
theorem unitStep_orthogonal_oldFlag (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    {i l : ℕ} (hi : i < n) (hli : l < i) : canonicalCGUnitStep base g i∈(oldFlag base g l)ᗮ := by
  -- All actual generators have indices strictly earlier than the tested true frame column.
  have hq := canonicalCG_frame_of_full_atoms base hb g hcount
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j,hj,rfl⟩ := hv
    change j≤l at hj
    have he : (⟨j,by omega⟩ : Fin n)≠⟨i,hi⟩ := by
      intro he
      have he' : j=i := congrArg Fin.val he
      omega
    simpa only [Fin.val_mk] using hq.inner_eq_zero he
  | zero => exact inner_zero_left _
  | add v w _ _ hv hw => rw [inner_add_left,hv,hw,add_zero]
  | smul a v _ hv => rw [real_inner_smul_left,hv,mul_zero]

/-- Pairing a true canonical CG step with an old-flag projection keeps exactly the flags containing that step.
Use: turns the spatial sharp response into its actual true-CG-step coordinate equations.
Article: main_krylov, thm:A, P_l coordinate action.
Proof: self-adjointness transfers the genuine orthogonal projection to the
true unit step; membership or actual later-step orthogonality gives the two cases, and scaling restores its physical step length. -/
theorem step_inner_oldFlag (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    {i : ℕ} (hi : i<n) (l : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (canonicalCGStep base g i) ((oldFlag base g l).starProjection v)=
      if i≤l then inner ℝ (canonicalCGStep base g i) v else 0 := by
  -- The scale is retained outside the exact projection identity; no lower step-energy bound enters.
  have hs : canonicalCGStep base g i=‖canonicalCGStep base g i‖ • canonicalCGUnitStep base g i :=
    (NormedSpace.norm_smul_normalize _).symm
  rw [hs,real_inner_smul_left,← Submodule.inner_starProjection_left_eq_right]
  by_cases hil : i≤l
  · rw [(oldFlag base g l).starProjection_eq_self_iff.mpr (unitStep_mem_oldFlag base g hil),ite_eq_left hil,hs,real_inner_smul_left]
  · have hp : (oldFlag base g l).starProjection (canonicalCGUnitStep base g i)=0 := by
      change ((oldFlag base g l).orthogonalProjectionOnto (canonicalCGUnitStep base g i) : EuclideanSpace ℝ (Fin n))=0
      rw [(oldFlag base g l).orthogonalProjectionOnto_eq_zero_iff.mpr
        (unitStep_orthogonal_oldFlag base hb g hcount hi (by omega))]
      rfl
    rw [hp,inner_zero_left,mul_zero,ite_eq_right hil]

/-- The actual canonical CG steps separate all physical vectors on a full active-atom reference.
Use: true response coordinate equations uniquely identify the real terminal derivative.
Article: main_krylov, thm:A, full reference basis.
Proof: normalize the actual nonzero steps, extend zero coordinate pairings to
their full-dimensional genuine orthonormal span, and test the difference against itself. -/
theorem canonical_step_inner_ext (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (v w : EuclideanSpace ℝ (Fin n))
    (he : ∀ i<n, inner ℝ (canonicalCGStep base g i) v=inner ℝ (canonicalCGStep base g i) w) : v=w := by
  -- Full active support supplies the actual full frame, including the empty zero-dimensional case.
  let q := fun i : Fin n => canonicalCGUnitStep base g i.val
  have hq := canonicalCG_frame_of_full_atoms base hb g hcount
  have hspan : Submodule.span ℝ (Set.range q)=⊤ := by
    exact hq.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)
  have hker : Submodule.span ℝ (Set.range q)≤(innerSL ℝ (v-w)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hh := he i.val i.isLt
    have hn : ‖canonicalCGStep base g i.val‖≠0 := by
      apply norm_ne_zero_iff.mpr
      intro hz
      exact hq.ne_zero i (by simp only [canonicalCGUnitStep,hz,NormedSpace.normalize_zero_eq_zero])
    have hzero : inner ℝ (canonicalCGStep base g i.val) (v-w)=0 := by rw [inner_sub_right,hh,sub_self]
    change inner ℝ (v-w) (canonicalCGUnitStep base g i.val)=0
    rw [real_inner_comm]
    have hs := NormedSpace.norm_smul_normalize (canonicalCGStep base g i.val)
    change ‖canonicalCGStep base g i.val‖ • canonicalCGUnitStep base g i.val=canonicalCGStep base g i.val at hs
    rw [← hs,real_inner_smul_left] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hn
  have hz : inner ℝ (v-w) (v-w)=0 := hker (by rw [hspan]; trivial)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

/-- The spatial reference response has exactly the triangular increment coordinates of the true full-CG-step staircase.
Use: this is the algebraic identification needed to transfer the proved sharp response norms to the actual FC derivative.
Article: main_krylov, thm:A, ΣP_lE_lv_l coordinate identity.
Proof: each true old projection selects i≤l; substitute genuine remaining
CG step tails and interchange the two finite triangular sums. -/
theorem fullCycleResponse_coordinates (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) {i : ℕ} (hi : i<n) :
    inner ℝ (canonicalCGStep base g i) (fullCycleResponse base g (range n) E)=
      ∑ j∈Ico (i+1) n, inner ℝ (canonicalCGStep base g i)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (∑ l∈Ico i j, E l) (canonicalCGStep base g j)) := by
  -- The last flag has zero tail, so the full range n has the same response as the printed preterminal range.
  unfold fullCycleResponse
  rw [inner_sum]
  simp_rw [step_inner_oldFlag base hb g hcount hi]
  rw [← sum_filter]
  have hset : (range n).filter (fun l => i≤l)=Ico i n := by ext l; simp only [mem_filter,mem_range,mem_Ico]; tauto
  rw [hset]
  have htail (l : ℕ) (hl : l∈Ico i n) : remainingTail base g l=∑ j∈Ico (l+1) n, canonicalCGStep base g j := by
    simpa only [hcount] using remainingTail_eq_sum base hb g l (by simpa only [hcount] using (mem_Ico.mp hl).2)
  calc
    _ = ∑ l∈Ico i n, ∑ j∈Ico (l+1) n, inner ℝ (canonicalCGStep base g i)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E l) (canonicalCGStep base g j)) := by
      apply sum_congr rfl
      intro l hl
      rw [htail l hl,map_sum,inner_sum]
    _ = ∑ j∈Ico i n, ∑ l∈Ico i j, inner ℝ (canonicalCGStep base g i)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E l) (canonicalCGStep base g j)) := sum_Ico_Ico_comm' i n _
    _ = _ := by
      rw [sum_eq_sum_Ico_succ_bot (by omega : i<n)]
      simp only [Ico_self,sum_empty,zero_add]
      apply sum_congr rfl
      intro j _
      rw [map_sum,_root_.sum_apply,inner_sum]

end
end krylov.Variation
