import nesterov.IQC.StablePowers
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
The full-memory companion operator. Stability is proved from the actual
polynomial, using eigenvectors rather than cancelling numerator factors.
-/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open Polynomial

/-- Companion of an ascending-order recursion, on the complete latent state. -/
def companionLinear (d : ℕ) (a : Fin d→ℂ) : (Fin d→ℂ)→ₗ[ℂ](Fin d→ℂ) where
  toFun x i:=if hi : i.val+1<d then x ⟨i.val+1,hi⟩ else ∑ j,a j*x j
  map_add' x y:=by
    ext i
    by_cases hi : i.val+1<d <;> simp [hi,mul_add,Finset.sum_add_distrib]
  map_smul' r x:=by
    ext i
    by_cases hi : i.val+1<d
    · simp [hi]
    · simp only [hi,↓reduceDIte,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The same genuine transition as a bounded operator. -/
def companion (d : ℕ) (a : Fin d→ℂ) : (Fin d→ℂ)→L[ℂ](Fin d→ℂ) :=
  (companionLinear d a).toContinuousLinearMap

@[simp] theorem companion_apply (d : ℕ) (a : Fin d→ℂ) (x : Fin d→ℂ) (i : Fin d) :
    companion d a x i=if hi : i.val+1<d then x ⟨i.val+1,hi⟩ else ∑ j,a j*x j := rfl

/-- Every eigenvalue satisfies the uncancelled characteristic equation. -/
theorem companion_eigenvalue {d : ℕ} (hd : 0<d) (a : Fin d→ℂ) {z : ℂ}
    (hz : z∈spectrum ℂ (companion d a)) :
    z^d=∑ j : Fin d,a j*z^j.val := by
  rw [ContinuousLinearMap.spectrum_eq] at hz
  obtain ⟨x,hx⟩:= (Module.End.HasEigenvalue.of_mem_spectrum hz).exists_hasEigenvector
  have he : companion d a x=z • x:=hx.apply_eq_smul
  let zeroIndex : Fin d:=⟨0,hd⟩
  have hcoord (j : ℕ) (hj : j<d) : x ⟨j,hj⟩=z^j*x zeroIndex := by
    induction j with
    | zero => simp [zeroIndex]
    | succ j ih =>
      have hj' : j<d:=by omega
      have hh:=congrFun he (⟨j,hj'⟩:Fin d)
      simp only [companion_apply,show j+1<d from hj,↓reduceDIte,Pi.smul_apply,smul_eq_mul] at hh
      rw [hh,ih hj',pow_succ]
      ring
  have hx0 : x zeroIndex≠0 := by
    intro hx0
    apply hx.2
    ext j
    simp [hcoord j.val j.isLt,hx0]
  let lastIndex : Fin d:=⟨d-1,by omega⟩
  have hh:=congrFun he lastIndex
  simp only [companion_apply,lastIndex,show ¬d-1+1<d by omega,↓reduceDIte,
    Pi.smul_apply,smul_eq_mul] at hh
  have hlast : d-1+1=d:=by omega
  have hc : z*x ⟨d-1,by omega⟩=z^d*x zeroIndex := by
    have hp : z^d=z*z^(d-1) := by
      simpa only [hlast] using (pow_succ' z (d-1))
    rw [hcoord,hp]
    ring
  rw [hc] at hh
  have hsum : (∑ j : Fin d,a j*x j)=(∑ j : Fin d,a j*z^j.val)*x zeroIndex := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hcoord j.val j.isLt]
    ring
  rw [hsum] at hh
  exact (mul_right_cancel₀ hx0 hh).symm

/-- Stable roots of a finite recurrence give absolute summability of every
operator coefficient, irrespective of repeated roots and latent common modes. -/
theorem companion_powers_summable {d : ℕ} (hd : 0<d) (a : Fin d→ℂ)
    (hstable : ∀ z : ℂ,z^d=∑ j : Fin d,a j*z^j.val → ‖z‖<1) :
    Summable (fun n : ℕ=>‖companion d a^n‖) := by
  have : Nonempty (Fin d):=⟨⟨0,hd⟩⟩
  apply summable_norm_powers
  intro z hz
  exact hstable z (companion_eigenvalue hd a hz)

end
end nesterov.IQC
