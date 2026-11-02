import krylov.Cancellation.DCSlide
import krylov.Methods.DeferredCoefficients
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(b), genuine one-gradient quadratic reference tools.
Use: derive the actual tilted trial displacement and scaled FC direction
from original native coefficient solves on a true quadratic stored basis.
Source: existing exact deferred coefficient splitting, genuine Galerkin
conjugacy uniqueness and actual CG flag geometry.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real nonzero-estimate tilted trial is exactly its native model correction
plus the same estimate times the original untilted FC direction.
Use: identify the actual one-gradient displacement before any reference argument.
Article: main_krylov, thm:dcs(b).
Proof: split the genuine deferred coefficients into real conjugacy/model
parts, synthesize both actual physical sums, and cancel only the nonzero estimate. -/
theorem tilted_trial_split (s y : ι → E) (g : E) (a : ℝ) (ha : a≠0) :
    a • deferredDirection s y g a=
      combine s (modelCoefficients s (crossGram y s) g)+a • conjugacyDirection s y g := by
  let c := conjugacyCoefficients s y g
  let w := modelCoefficients s (crossGram y s) g
  have hs : combine s (c+a⁻¹ • w)=combine s c+a⁻¹ • combine s w := by
    simp only [combine,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_smul,Finset.sum_add_distrib,Finset.smul_sum,smul_smul]
  rw [deferredDirection,deferredCoefficients_split]
  change a • (-g+combine s (c+a⁻¹ • w))=_
  rw [hs,smul_add,smul_add,smul_smul,mul_inv_cancel₀ ha,one_smul]
  change _=combine s w+a • (-g+combine s c)
  module

/-- On actual quadratic observations, the original tilted trial equals the
genuine virtual Galerkin correction plus its untilted incoming-gradient search.
Use: the one-gradient DC trajectory uses the real native observed solve.
Article: main_krylov, thm:dcs(b).
Proof: true quadratic image symmetry identifies the actual cross-Gram matrix
with the original latest model, so the exact trial split is the native virtual correction. -/
theorem quadratic_tilted_trial (W : List (E × E)) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hy : ∀ i,windowImages W i=Q (windowSteps W i)) (g : E) (a : ℝ) (ha : a≠0) :
    a • deferredDirection (windowSteps W) (windowImages W) g a=
      virtualCorrection W g+a • windowDirection W g := by
  have hY : windowImages W=fun i => Q (windowSteps W i) := funext hy
  have hM : windowModel W=crossGram (windowImages W) (windowSteps W) := by
    rw [windowModel_quadratic W Q hQ hy,← hY]
  rw [tilted_trial_split _ _ _ _ ha,← hM]
  rfl

/-- A true full reference basis sends a scaled current CG residual plus any
old-flag vector to exactly the same scale of the actual CG direction.
Use: derive the original one-gradient DC incoming direction factor from the
actual evaluated gradient, rather than impose a virtual-gradient identity.
Article: main_krylov, thm:dcs(b).
Proof: the real candidate has its required displacement in the actual old
basis span and annihilates every genuine stored quadratic image. Positive
native conjugacy uniqueness identifies the computed direction. -/
theorem windowDirection_scaled_reference (W : List (E × E)) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (k : ℕ) (hpre : ∀ i<k,CG.gradient Q g i≠0)
    (hy : ∀ i,windowImages W i=Q (windowSteps W i)) (hLI : LinearIndependent ℝ (windowSteps W))
    (hspan : pairSpan W=directionFlag Q g k) (rho : ℝ) (v G : E)
    (hv : v∈directionFlag Q g k) (hG : G=rho • CG.gradient Q g k+v) :
    windowDirection W G=rho • CG.direction Q g k := by
  apply conjugacyDirection_unique
  · have hY : windowImages W=fun i => Q (windowSteps W i) := funext hy
    rw [hY]
    exact isUnit_iff_ne_zero.mpr (operatorGram_posDef Q hQ hpos hLI).det_pos.ne'
  · change rho • CG.direction Q g k+G∈pairSpan W
    rw [hspan,hG]
    have he : rho • CG.direction Q g k+(rho • CG.gradient Q g k+v)=
        rho • (CG.direction Q g k+CG.gradient Q g k)+v := by module
    rw [he]
    exact (directionFlag Q g k).add_mem
      ((directionFlag Q g k).smul_mem _ (direction_add_gradient_mem_flag Q g k)) hv
  · ext i
    change inner ℝ (windowImages W i) (rho • CG.direction Q g k)=0
    rw [hy,real_inner_smul_right]
    have hs : windowSteps W i∈directionFlag Q g k := by
      rw [← hspan]
      exact Submodule.subset_span ⟨i,rfl⟩
    have hsym := hQ (windowSteps W i) (CG.direction Q g k)
    change inner ℝ (Q (windowSteps W i)) (CG.direction Q g k)=
      inner ℝ (windowSteps W i) (Q (CG.direction Q g k)) at hsym
    rw [hsym,directionFlag_conjugate Q hQ hpos g k hpre hs,mul_zero]

/-- Every actual current CG gradient belongs to its true next direction flag.
Use: retain the real old-flag component in the one-gradient DC reference induction.
Article: main_krylov, thm:dcs(b).
Proof: its sum with the current direction is in the preceding flag; subtract
that direction inside the true next flag. -/
theorem cg_gradient_mem_next_directionFlag (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    CG.gradient Q g k∈directionFlag Q g (k+1) := by
  have hK : directionFlag Q g k≤directionFlag Q g (k+1) := by rw [directionFlag_succ];exact le_sup_right
  have hd : CG.direction Q g k∈directionFlag Q g (k+1) := Submodule.subset_span ⟨k,Nat.lt_succ_self k,rfl⟩
  have h := (directionFlag Q g (k+1)).sub_mem (hK (direction_add_gradient_mem_flag Q g k)) hd
  simpa only [add_sub_cancel_left] using h

/-- The original one-gradient DC decision on a genuine full quadratic flag
is its true virtual correction plus the actual estimate times the derived
scaled CG direction.
Use: the later execution induction proves the supplied flag and gradient
invariants from original real queried histories.
Article: main_krylov, thm:dcs(b).
Proof: genuine Galerkin uniqueness identifies the actual virtual correction;
true scaled conjugacy uniqueness gives the real untilted direction, and the
native tilted-trial split identifies the original policy's evaluated step. -/
theorem dc_one_gradient_step_from_flag (estimate : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k,CG.gradient Q g i≠0) (H : History E)
    (hbal : H.gradient=g+Q H.displacement)
    (hy : ∀ i,windowImages H.pairs i=Q (windowSteps H.pairs i))
    (hLI : LinearIndependent ℝ (windowSteps H.pairs)) (hspan : pairSpan H.pairs=directionFlag Q g k)
    (rho : ℝ) (v : E) (hv : v∈directionFlag Q g k) (hG : H.gradient=rho • CG.gradient Q g k+v)
    (ha : estimate H≠0) :
    (dcSlideOneGradient fullMemory estimate).step H=CG.displacement Q g k-H.displacement+
      (estimate H*rho) • CG.direction Q g k := by
  have hvirt := virtual_reference_basis H Q hQ hpos g k hpre hbal hy hLI hspan
  have hdir := windowDirection_scaled_reference H.pairs Q hQ hpos g k hpre hy hLI hspan rho v H.gradient hv hG
  change estimate H • deferredDirection (windowSteps (selectedWindow fullMemory H))
    (windowImages (selectedWindow fullMemory H)) H.gradient (estimate H)=_
  rw [selectedWindow_full,quadratic_tilted_trial H.pairs Q hQ hy H.gradient (estimate H) ha,hvirt.1,hdir,smul_smul]

end
end krylov.Cancellation
