import krylov.Reference.LanczosForms
import krylov.LinearAlgebra.JacobiStrictPrefix
import krylov.LinearAlgebra.StrictSpectralShifts
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine strict Ritz window before exhaustion.
Use: derive strict original Ritz eigenvalue endpoint inequalities from actual physical quadratic bounds and one more genuinely active CG residual.
Source: actual physical Lanczos Gram bounds, genuine extra-site irreducibility and the proved strict positive proper-prefix theorem.
-/

namespace krylov.Reference.CG
noncomputable section
open Matrix krylov.LinearAlgebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual Ritz value of a genuinely nonterminal CG prefix lies strictly between the true physical quadratic bounds.
Use: Every actual Ritz value of a genuinely nonterminal CG prefix lies strictly between the true physical quadratic bounds.
Article: main_krylov, prop:phi(a), genuine strict Ritz window before exhaustion.
Proof: Shift the actual one-site-longer compression, retain its genuine nonzero edges and use strict positivity of both actual proper leading prefixes. -/
theorem lanczosMatrix_strict_window (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m+1,gradient Q g i≠0) (a b : ℝ)
    (hlo : ∀ v : E,a*‖v‖^2≤ inner ℝ v (Q v))
    (hhi : ∀ v : E,inner ℝ v (Q v)≤b*‖v‖^2) :
    ∀ i,a<(lanczosMatrix_posDef Q hQ hpos g m (fun i hi => hpre i (by omega))).1.eigenvalues i ∧
      (lanczosMatrix_posDef Q hQ hpos g m (fun i hi => hpre i (by omega))).1.eigenvalues i<b := by
  -- The genuine additional active residual supplies a real extra Jacobi site and strictly nonzero physical edge.
  let T := lanczosMatrix Q g (m+1)
  have htri := lanczosMatrix_tridiagonal Q hQ hpos g (m+1) hpre
  have hneg := lanczosMatrix_adjacent_neg Q hQ hpos g (m+1) hpre
  have hoff (c : ℝ) (i j : Fin (m+1)) (hij : i≠j) :
      (T-c • 1) i j=T i j ∧ (c • 1-T) i j= -T i j := by
    simp [hij]
  have htlo : ∀ i j : Fin (m+1),i.val+1 < j.val ∨ j.val+1 < i.val → (T-a • 1) i j=0 := by
    intro i j hij
    rw [(hoff a i j (by intro h;subst j;omega)).1]
    exact htri i j hij
  have hthi : ∀ i j : Fin (m+1),i.val+1 < j.val ∨ j.val+1 < i.val → (b • 1-T) i j=0 := by
    intro i j hij
    rw [(hoff b i j (by intro h;subst j;omega)).2]
    exact neg_eq_zero.mpr (htri i j hij)
  -- Both actual endpoint shifts retain the same nonzero true coupling, with opposite signs.
  have hedge (c : ℝ) (i j : Fin (m+1)) (hij : i.val+1=j.val) :
      (T-c • 1) j i≠0 ∧ (c • 1-T) j i≠0 := by
    have hsym := (lanczosMatrix_posDef Q hQ hpos g (m+1) hpre).1
    have he : T j i=T i j := by
      exact congrFun (congrFun hsym i) j
    rw [(hoff c j i (by intro h;subst j;omega)).1,(hoff c j i (by intro h;subst j;omega)).2,he]
    exact ⟨(hneg i j hij).ne,neg_ne_zero.mpr (hneg i j hij).ne⟩
  -- The true proper-prefix positivity theorem makes both original endpoint margins strict.
  have hL := jacobi_strict_prefix (T-a • 1) (lanczosMatrix_shift_posSemidef Q hQ hpos g (m+1) hpre a hlo)
    htlo (fun i j hij => (hedge a i j hij).1)
  have hH := jacobi_strict_prefix (b • 1-T) (lanczosMatrix_upper_shift_posSemidef Q hQ hpos g (m+1) hpre b hhi)
    hthi (fun i j hij => (hedge b i j hij).2)
  have heL : (T-a • 1).submatrix Fin.castSucc Fin.castSucc=lanczosMatrix Q g m-a • 1 := by
    ext i j
    simp [T,lanczosMatrix,Matrix.one_apply]
  have heH : (b • 1-T).submatrix Fin.castSucc Fin.castSucc=b • 1-lanczosMatrix Q g m := by
    ext i j
    simp [T,lanczosMatrix,Matrix.one_apply]
  rw [heL] at hL
  rw [heH] at hH
  have htm := (lanczosMatrix_posDef Q hQ hpos g m (fun i hi => hpre i (by omega))).1
  intro i
  exact ⟨(positive_lower_shift_iff _ htm a).mp hL i,(positive_upper_shift_iff _ htm b).mp hH i⟩
end
end krylov.Reference.CG
