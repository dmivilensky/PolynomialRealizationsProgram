import krylov.Cancellation.DeferredTailGeometry
import krylov.Variation.SpectralResponse
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, exact attained original deferred spectral constant.
Use: prove the printed independent symmetric-matrix budget maximum for the
literal original deferred response, with real attaining physical increments.
Source: reused actual orthogonal projection contraction, planar attaining
matrices and true CG tail geometry; no maximizer or budget-duality witness is assumed.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset krylov.Reference krylov.LinearAlgebra krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original deferred spatial response obeys its true independent matrix
budget sum bound, even without symmetry of the input increments.
Use: the exact original coefficient depends on actual deferred tail norms.
Article: main_krylov, thm:DC, sharp coefficient upper bound.
Proof: true old-flag projections are contractive; the real physical operator
norm bounds each queried actual tail, and the finite triangle inequality adds them. -/
theorem deferred_response_le (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (epsilon : ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (omega : ℕ → ℝ)
    (hbudget : ∀ l<k,‖E l‖≤omega l) :
    ‖deferredResponse base g k epsilon E‖≤∑ l∈range k,omega l*‖deferredTail base g k epsilon l‖ := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro l hl
  apply ((oldFlag base g l).norm_starProjection_apply_le _).trans
  have he := (cgOperator (E l)).le_opNorm (deferredTail base g k epsilon l)
  rw [cgOperator,← Matrix.cstar_norm_def] at he
  exact he.trans (mul_le_mul_of_nonneg_right (hbudget l (mem_range.mp hl)) (norm_nonneg _))

/-- A genuine physical symmetric planar increment attains the whole original
deferred-tail projection bound at its own true matrix budget.
Use: actual old-flag orthogonality and nonzero normalizers are derived from CG.
Article: main_krylov, thm:DC, explicit symmetric attaining increments.
Proof: normalize the actual nonzero deferred tail. It is orthogonal to the
real old flag containing the common first CG unit step, so the existing true
planar norm and projected-action identities give the desired physical increment. -/
theorem deferred_cross_increment (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k l : ℕ) (hl : l<k)
    (hcount : k+1≤referenceAtomCount base hb g) (epsilon b : ℝ) (hb0 : 0≤b) :
    let e := canonicalCGUnitStep base g 0
    let v := deferredTail base g k epsilon l
    let M := planarMatrix e (NormedSpace.normalize v) 0 b 0
    M.IsSymm ∧ ‖M‖≤b ∧
      (oldFlag base g l).starProjection (cgOperator M v)=(b*‖v‖) • e := by
  let e := canonicalCGUnitStep base g 0
  let v := deferredTail base g k epsilon l
  let h := NormedSpace.normalize v
  have he : ‖e‖=1 := (firstStep_common base hb g (by omega)).1
  have hv : v≠0 := deferred_tail_ne_zero base hb g k l hcount epsilon
  have hh : ‖h‖=1 := NormedSpace.norm_normalize hv
  have heK : e∈oldFlag base g l := unitStep_mem_oldFlag base g (Nat.zero_le l)
  have hhK : h∈(oldFlag base g l)ᗮ :=
    Submodule.smul_mem _ _ (deferred_tail_orthogonal base hb g k l hl hcount epsilon)
  have heh : inner ℝ e h=0 := ((oldFlag base g l).mem_orthogonal h).mp hhK e heK
  refine ⟨planarMatrix_isSymm _ _ _ _ _,?_,?_⟩
  · have hn := planar_spectral_norm_le e h he hh heh 0 1 (by norm_num)
    have hs : planarMatrix e h 0 b 0=b • planarMatrix e h 0 1 0 := by
      simpa only [mul_zero,mul_one] using planarMatrix_scale e h b 0 1 0
    rw [hs,norm_smul,Real.norm_eq_abs,abs_of_nonneg hb0]
    simpa only [chebyshev1.opNorm,neg_zero,mul_one] using mul_le_mul_of_nonneg_left hn hb0
  · have hp := (projected_planar_actions (oldFlag base g l) e h he hh heh heK hhK 0 b 0 0).1
    have hvh : v=‖v‖ • h := (NormedSpace.norm_smul_normalize v).symm
    change (oldFlag base g l).starProjection (Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix e h 0 b 0) v)=_
    conv_lhs => rw [hvh]
    rw [map_smul,map_smul,hp,smul_smul,mul_comm]

/-- Real symmetric matrix increments attain the complete independent-budget
deferred sum coefficient simultaneously along the genuine first CG unit step.
Use: the original coefficient is an attained maximum on the true matrix budget class.
Article: main_krylov, thm:DC, sharpness with explicit physical increments.
Proof: use the actual planar attaining matrix for each genuine deferred tail.
All true projected actions point along the same real first CG unit step,
so the finite triangle inequality is exactly attained at the original budgets. -/
theorem deferred_response_attained (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g)
    (epsilon : ℝ) (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l) :
    ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
      (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l) ∧
      ‖deferredResponse base g k epsilon E‖=∑ l∈range k,omega l*‖deferredTail base g k epsilon l‖ := by
  let e := canonicalCGUnitStep base g 0
  let E := fun l => planarMatrix e (NormedSpace.normalize (deferredTail base g k epsilon l)) 0 (omega l) 0
  have hp (l : ℕ) (hl : l<k) := deferred_cross_increment base hb g k l hl hcount epsilon (omega l) (homega l hl)
  refine ⟨E,fun _ => planarMatrix_isSymm _ _ _ _ _,fun l hl => (hp l hl).2.1,?_⟩
  have hf : deferredResponse base g k epsilon E=
      (∑ l∈range k,omega l*‖deferredTail base g k epsilon l‖) • e := by
    unfold deferredResponse
    rw [sum_smul]
    exact sum_congr rfl (fun l hl => (hp l (mem_range.mp hl)).2.2)
  rw [hf,norm_smul,Real.norm_eq_abs,(firstStep_common base hb g (by omega)).1,mul_one,
    abs_of_nonneg (sum_nonneg (fun l hl => mul_nonneg (homega l (mem_range.mp hl)) (norm_nonneg _)))]

/-- The original independent symmetric-matrix deferred response problem has
exactly its printed attained sum of square-root energy coefficients.
Use: the source sharp constant is proved over genuine physical matrix increments,
including arbitrary zero budgets and any real reference damping value.
Article: main_krylov, thm:DC, exact sharp matrix maximum.
Proof: the actual deferred tail Pythagorean identity gives every true norm.
The proved physical norm bound and real simultaneous symmetric attaining
family identify the exact greatest response over the original budget class. -/
theorem deferred_response_sharp (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g)
    (epsilon : ℝ) (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l) :
    IsGreatest {z : ℝ | ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
      (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l) ∧ z=‖deferredResponse base g k epsilon E‖}
      (∑ l∈range k,omega l*Real.sqrt (cgEnergy base g k+
        epsilon^2*(‖cgCanonicalError base g (l+1)‖^2-‖cgCanonicalError base g k‖^2))) := by
  have hnorm (l : ℕ) (hl : l<k) : ‖deferredTail base g k epsilon l‖=
      Real.sqrt (cgEnergy base g k+epsilon^2*(‖cgCanonicalError base g (l+1)‖^2-‖cgCanonicalError base g k‖^2)) := by
    rw [← deferred_tail_norm_sq base hb g k l hl hcount epsilon,Real.sqrt_sq (norm_nonneg _)]
  have hsum : (∑ l∈range k,omega l*Real.sqrt (cgEnergy base g k+
      epsilon^2*(‖cgCanonicalError base g (l+1)‖^2-‖cgCanonicalError base g k‖^2)))=
      ∑ l∈range k,omega l*‖deferredTail base g k epsilon l‖ :=
    sum_congr rfl (fun l hl => congrArg (fun t => omega l*t) (hnorm l (mem_range.mp hl)).symm)
  rw [hsum]
  constructor
  · obtain ⟨E,hE,hbudget,hvalue⟩ := deferred_response_attained base hb g k hcount epsilon omega homega
    exact ⟨E,hE,hbudget,hvalue.symm⟩
  · rintro z ⟨E,_,hbudget,rfl⟩
    exact deferred_response_le base g k epsilon E omega hbudget

end
end krylov.Cancellation
