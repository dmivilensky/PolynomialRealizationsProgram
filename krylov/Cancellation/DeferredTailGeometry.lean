import krylov.Cancellation.DeferredResponse
import krylov.Reference.EnergyPositive
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, genuine deferred response-tail geometry.
Use: derive the printed energy norm, true old-flag orthogonality and nonzero
normalizers of the original deferred response vectors from actual CG geometry.
Source: proved true canonical CG energy telescoping, real prefix orthogonality
and Pythagoras; no tail norms or response frame are assumed.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Envelope krylov.Variation
open scoped BigOperators
variable {n : ℕ}

/-- Every genuine earlier canonical CG step belongs to its actual explored flag.
Use: prove real partial-tail orthogonality without prescribing a reference basis.
Article: main_krylov, thm:DC.
Proof: the true normalized unit step is an actual flag generator; restore its real norm. -/
theorem canonical_step_mem_exploredFlag (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k j : ℕ) (hj : j<k) :
    canonicalCGStep base g j∈exploredFlag base g k := by
  have h := (exploredFlag base g k).smul_mem ‖canonicalCGStep base g j‖
    (Submodule.subset_span (s := Set.range (fun i : Fin k => canonicalCGUnitStep base g i.val)) ⟨⟨j,hj⟩,rfl⟩)
  simpa only [canonicalCGUnitStep,NormedSpace.norm_smul_normalize] using h

/-- The original deferred tail has exactly the genuine last step energy plus
the squared damping value times the real pre-final remaining error drop.
Use: identify the printed sharp coefficient from actual CG energies.
Article: main_krylov, thm:DC, norm(vtilde_l) squared.
Proof: the actual intermediate tail belongs to the old explored flag, which
both the true current error and last step annihilate. Genuine error telescoping
and two applications of Pythagoras give the original energy formula. -/
theorem deferred_tail_norm_sq (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k l : ℕ) (hl : l<k)
    (hcount : k+1≤referenceAtomCount base hb g) (epsilon : ℝ) :
    ‖deferredTail base g k epsilon l‖^2=cgEnergy base g k+
      epsilon^2*(‖cgCanonicalError base g (l+1)‖^2-‖cgCanonicalError base g k‖^2) := by
  let U := ∑ j∈Ico (l+1) k,canonicalCGStep base g j
  have hU : U∈exploredFlag base g k := by
    exact Submodule.sum_mem _ (fun j hj => canonical_step_mem_exploredFlag base g k j (mem_Ico.mp hj).2)
  have he0 := ((exploredFlag base g k).mem_orthogonal _).mp
    (exploredFlag_error_orthogonal base hb g (show k≤referenceAtomCount base hb g by omega)) _ hU
  have hs0 := ((exploredFlag base g k).mem_orthogonal _).mp
    (canonicalCGStep_later_orthogonal base hb g (k+1) k k hcount le_rfl (by omega)) _ hU
  have he : inner ℝ (cgCanonicalError base g k) U=0 := (real_inner_comm _ _).trans he0
  have hs : inner ℝ U (canonicalCGStep base g k)=0 := hs0
  have htel : cgCanonicalError base g (l+1)=cgCanonicalError base g k-U := by
    dsimp only [U]
    rw [canonicalCGStep_sum base hb g (by omega : l+1≤k)]
    abel
  have hnorm : ‖cgCanonicalError base g (l+1)‖^2=‖cgCanonicalError base g k‖^2+‖U‖^2 := by
    rw [htel,norm_sub_sq_real,he]
    ring
  change ‖epsilon • U+canonicalCGStep base g k‖^2=_
  rw [norm_add_sq_real,real_inner_smul_left,hs,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    ← cgEnergy_eq_norm_sq base hb]
  rw [hnorm]
  ring

/-- Every original deferred response tail lies in the genuine old flag's
orthogonal complement on a true active reference prefix.
Use: construct the actual symmetric planar matrix attaining every sharp budget.
Article: main_krylov, thm:DC.
Proof: every actual tail step is strictly later than the old flag; true
finite-prefix CG orthogonality is preserved by its real sum and scaling. -/
theorem deferred_tail_orthogonal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k l : ℕ) (hl : l<k)
    (hcount : k+1≤referenceAtomCount base hb g) (epsilon : ℝ) :
    deferredTail base g k epsilon l∈(oldFlag base g l)ᗮ := by
  have hflag : exploredFlag base g (l+1)=oldFlag base g l := by
    rw [exploredFlag_eq_oldFlag base g (by omega : 0<l+1),Nat.add_sub_cancel]
  have hstep (j : ℕ) (hlo : l+1≤j) (hhi : j<k+1) :
      canonicalCGStep base g j∈(oldFlag base g l)ᗮ := by
    rw [← hflag]
    exact canonicalCGStep_later_orthogonal base hb g (k+1) (l+1) j hcount hlo hhi
  exact (oldFlag base g l)ᗮ.add_mem
    ((oldFlag base g l)ᗮ.smul_mem epsilon (Submodule.sum_mem _ (fun j hj => hstep j (mem_Ico.mp hj).1 (by have := (mem_Ico.mp hj).2;omega))))
    (hstep k (by omega) (by omega))

/-- Every original deferred tail has a genuine nonzero true last CG component.
Use: sharp attaining matrices normalize actual tails only on a proved domain.
Article: main_krylov, thm:DC.
Proof: its true squared norm contains the positive last step energy; the
remaining contribution is the square of an actual orthogonal partial tail. -/
theorem deferred_tail_ne_zero (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k l : ℕ)
    (hcount : k+1≤referenceAtomCount base hb g) (epsilon : ℝ) :
    deferredTail base g k epsilon l≠0 := by
  have hp := cgEnergy_pos base hb g k (by omega)
  let U := ∑ j∈Ico (l+1) k,canonicalCGStep base g j
  have hU : U∈exploredFlag base g k :=
    Submodule.sum_mem _ (fun j hj => canonical_step_mem_exploredFlag base g k j (mem_Ico.mp hj).2)
  have horth := canonicalCGStep_later_orthogonal base hb g (k+1) k k hcount le_rfl (by omega)
  have hz0 := ((exploredFlag base g k).mem_orthogonal _).mp horth _ hU
  have hz1 : inner ℝ (canonicalCGStep base g k) U=0 := (real_inner_comm _ _).trans hz0
  intro hz
  have he : inner ℝ (canonicalCGStep base g k) (deferredTail base g k epsilon l)=cgEnergy base g k := by
    change inner ℝ (canonicalCGStep base g k) (epsilon • U+canonicalCGStep base g k)=_
    rw [inner_add_right,real_inner_smul_right,hz1,mul_zero,zero_add,real_inner_self_eq_norm_sq,
      ← cgEnergy_eq_norm_sq base hb]
  rw [hz,inner_zero_right] at he
  exact hp.ne' he.symm

end
end krylov.Cancellation
