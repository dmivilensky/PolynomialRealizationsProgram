import krylov.Tensor.HarmonicSlices
import krylov.Tensor.ReferenceTails

/-!
Article: main_krylov, thm:H, the exact genuine harmonic variation budgets.
Use: derive every actual compatible midpoint slice norm and the actual final
correction slice norm from the computed CG frame, retaining n >= 3.
Source: real harmonic slice norms and genuine CG orthogonality.
-/

namespace krylov.Tensor
noncomputable section
open Matrix Finset krylov.Functions krylov.Reference krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual unit CG step pairs with a true adjacent midpoint through
exactly its two computed step lengths. Article: main_krylov, thm:H. -/
theorem reference_midpoint_unit_pair (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : Fin (referenceAtomCount A hA g))
    (l : Fin (referenceAtomCount A hA g - 1)) :
    inner ℝ (canonicalCGUnitStep A g i.val) (referenceMidpointDrift A g l.val) =
      (1/2 : ℝ) * ((if i.val=l.val then ‖canonicalCGStep A g l.val‖ else 0) +
        (if i.val=l.val+1 then ‖canonicalCGStep A g (l.val+1)‖ else 0)) := by
  rw [referenceMidpointDrift, inner_smul_right, inner_add_right]
  have h0 := canonical_step_unit_pair A hA g i ⟨l.val, by have := l.isLt; omega⟩
  have h1 := canonical_step_unit_pair A hA g i ⟨l.val+1, by have := l.isLt; omega⟩
  simpa only [Fin.ext_iff] using congrArg (fun z => (1/2 : ℝ)*z) (congrArg₂ (·+·) h0 h1)

/-- The genuine harmonic tensor on the oldest and newest actual reference directions.
Article: main_krylov, thm:H. -/
def referenceHarmonicTensor (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (a : ℝ) : SymmetricCubic (EuclideanSpace ℝ (Fin n)) :=
  canonicalHarmonicTensor (canonicalCGUnitStep A g 0)
    (canonicalCGUnitStep A g (referenceAtomCount A hA g-1)) a

/-- Only the true first and true last midpoint increments of a full harmonic
reference survive, with their exact printed norms. Article: main_krylov, thm:H. -/
theorem reference_harmonic_increment_norm (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 3 ≤ referenceAtomCount A hA g)
    (a : ℝ) (ha : 0 ≤ a) (l : Fin (referenceAtomCount A hA g-1)) :
    ‖canonicalVariation (referenceHarmonicTensor A hA g a) (referenceMidpointDrift A g l.val)‖ =
      if l.val=0 then a*‖canonicalCGStep A g 0‖ else
        if l.val+2=referenceAtomCount A hA g then
          a*‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖ else 0 := by
  let N := referenceAtomCount A hA g
  have hframe := canonicalCG_frame A hA g
  let i0 : Fin N := ⟨0,by omega⟩
  let il : Fin N := ⟨N-1,by omega⟩
  have he := hframe.norm_eq_one i0
  have hh := hframe.norm_eq_one il
  have heh := hframe.inner_eq_zero (show i0 ≠ il by intro h; have := congrArg Fin.val h; dsimp only [i0,il] at this; omega)
  have h0 := reference_midpoint_unit_pair A hA g i0 l
  have h1 := reference_midpoint_unit_pair A hA g il l
  dsimp only [i0,il] at h0 h1
  have hs := canonicalHarmonic_slice_norm_sq (canonicalCGUnitStep A g 0)
    (canonicalCGUnitStep A g (N-1)) he hh heh a (referenceMidpointDrift A g l.val)
  change ‖canonicalVariation (referenceHarmonicTensor A hA g a) (referenceMidpointDrift A g l.val)‖^2 = _ at hs
  change inner ℝ (canonicalCGUnitStep A g 0) _ = _ at h0
  change inner ℝ (canonicalCGUnitStep A g (N-1)) _ = _ at h1
  rw [h0,h1] at hs
  by_cases hl0 : l.val=0
  · simp [hl0, show N-1 ≠ 0 by omega, show N-1 ≠ 1 by omega] at hs
    rw [ite_eq_left hl0,hl0]
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mp
    nlinarith only [hs]
  · rw [ite_eq_right hl0]
    by_cases hlN : l.val+2=referenceAtomCount A hA g
    · rw [ite_eq_left hlN]
      have heq : l.val+1=N-1 := by omega
      simp only [show ¬(0 : ℕ)=l.val by omega, show ¬(0 : ℕ)=N-1 by omega,
        show ¬N-1=l.val by omega, ite_false, heq, ite_true, zero_add, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hs
      apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mp
      nlinarith only [hs]
    · rw [ite_eq_right hlN]
      simp only [show ¬(0 : ℕ)=l.val by omega, show ¬(0 : ℕ)=l.val+1 by omega,
        show ¬N-1=l.val by have := l.isLt; omega,
        show ¬N-1=l.val+1 by omega, ite_false, add_zero, mul_zero] at hs
      nlinarith only [hs, norm_nonneg (canonicalVariation (referenceHarmonicTensor A hA g a) (referenceMidpointDrift A g l.val))]

set_option maxHeartbeats 800000 in
/-- The true final half-step harmonic correction has its exact printed norm.
Article: main_krylov, thm:H, omega'=a sqrt(c_last). -/
theorem reference_harmonic_correction_norm (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2 ≤ referenceAtomCount A hA g)
    (a : ℝ) (ha : 0 ≤ a) :
    ‖canonicalVariation (referenceHarmonicTensor A hA g a)
      ((1/2 : ℝ) • canonicalCGStep A g (referenceAtomCount A hA g-1))‖ =
      a*‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖ := by
  let N := referenceAtomCount A hA g
  let i0 : Fin N := ⟨0,by omega⟩
  let il : Fin N := ⟨N-1,by omega⟩
  have hframe := canonicalCG_frame A hA g
  let e := canonicalCGUnitStep A g 0
  let h := canonicalCGUnitStep A g (N-1)
  have he := hframe.norm_eq_one i0
  have hh := hframe.norm_eq_one il
  have heh := hframe.inner_eq_zero (show i0 ≠ il by intro hz; have := congrArg Fin.val hz; dsimp only [i0,il] at this; omega)
  have hp0 := canonical_step_unit_pair A hA g i0 il
  have hpL := canonical_step_unit_pair A hA g il il
  have hi0L : i0 ≠ il := by
    intro hz
    have hv := congrArg Fin.val hz
    dsimp only [i0,il] at hv
    omega
  have hx : inner ℝ e ((1/2 : ℝ) • canonicalCGStep A g (N-1))=0 := by
    rw [inner_smul_right]
    change (1/2 : ℝ)*inner ℝ (canonicalCGUnitStep A g 0) (canonicalCGStep A g (N-1))=0
    rw [hp0,ite_eq_right hi0L,mul_zero]
  have hy : inner ℝ h ((1/2 : ℝ) • canonicalCGStep A g (N-1))=
      (1/2 : ℝ)*‖canonicalCGStep A g (N-1)‖ := by
    rw [inner_smul_right]
    change (1/2 : ℝ)*inner ℝ (canonicalCGUnitStep A g (N-1)) (canonicalCGStep A g (N-1))=_
    rw [hpL,ite_eq_left rfl]
  have hs := canonicalHarmonic_slice_norm_sq e h he hh heh a
    ((1/2 : ℝ) • canonicalCGStep A g (N-1))
  rw [hx,hy] at hs
  change ‖canonicalVariation (referenceHarmonicTensor A hA g a)
    ((1/2 : ℝ) • canonicalCGStep A g (referenceAtomCount A hA g-1))‖^2 =
      4*a^2*(0^2+((1/2 : ℝ)*‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖)^2) at hs
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mp
  nlinarith only [hs]

/-- Summing every genuine harmonic midpoint increment gives precisely the
printed W=a(sqrt(c_0)+sqrt(c_last)). Article: main_krylov, thm:H. -/
theorem reference_harmonic_total_budget (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 3 ≤ referenceAtomCount A hA g)
    (a : ℝ) (ha : 0 ≤ a) :
    (∑ l : Fin (referenceAtomCount A hA g-1),
      ‖canonicalVariation (referenceHarmonicTensor A hA g a) (referenceMidpointDrift A g l.val)‖) =
      a*(‖canonicalCGStep A g 0‖+‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖) := by
  let N := referenceAtomCount A hA g
  let i0 : Fin (N-1) := ⟨0,by omega⟩
  let il : Fin (N-1) := ⟨N-2,by omega⟩
  have hne : i0 ≠ il := by intro hz; have := congrArg Fin.val hz; dsimp only [i0,il] at this; omega
  have hterm (l : Fin (N-1)) :
      ‖canonicalVariation (referenceHarmonicTensor A hA g a) (referenceMidpointDrift A g l.val)‖ =
        (if l=i0 then a*‖canonicalCGStep A g 0‖ else 0) +
          (if l=il then a*‖canonicalCGStep A g (N-1)‖ else 0) := by
    rw [reference_harmonic_increment_norm A hA g hN a ha l]
    have hp0 : l.val=0 ↔ l=i0 := by
      constructor
      · intro hz
        apply Fin.ext
        exact hz
      · intro h
        exact congrArg Fin.val h
    have hpL : l.val+2=referenceAtomCount A hA g ↔ l=il := by
      constructor
      · intro hl
        apply Fin.ext
        dsimp only [il]
        omega
      · intro hl
        have := congrArg Fin.val hl
        dsimp only [il] at this
        omega
    simp only [hp0,hpL]
    change (if l=i0 then a*‖canonicalCGStep A g 0‖ else
      if l=il then a*‖canonicalCGStep A g (N-1)‖ else 0) = _
    by_cases h0 : l=i0
    · simp only [h0,hne,ite_true,ite_false,add_zero]
    · simp only [h0,ite_false,zero_add]
  simp_rw [hterm]
  rw [sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,ite_true]
  ring

end
end krylov.Tensor
