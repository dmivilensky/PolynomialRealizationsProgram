import krylov.XR.Cholesky
import Mathlib.Topology.Instances.Matrix

/-!
Article: main_krylov, lem:xr-local, open actual strict Hermitian tests.
Use: continuity of the true observed Hermitian matrix preserves its strict
positive-definiteness. This derives finite branch stability for the actual
complex test, without putting successful tests into a source structure.
Source: the proved finite Schur/Cholesky criterion and continuity of the
actual inverse precisely on its genuine nonsingular leading-block domain.
-/

namespace krylov.XR
noncomputable section
open Matrix Filter Topology
open scoped ComplexOrder
variable {X : Type*} [TopologicalSpace X]

/-- Genuine continuous Hermitian data preserve strict positive definiteness
near any positive actual reference matrix. The complex order is used only
on the Hermitian diagonal; no open cone in the whole complex plane is
incorrectly asserted. -/
theorem eventually_posDef_of_continuousAt_hermitian {n : ℕ}
    (A : X → Matrix (Fin n) (Fin n) ℂ) (x : X) (hA : ContinuousAt A x)
    (hHerm : ∀ᶠ z in 𝓝 x, (A z).IsHermitian) (hpos : (A x).PosDef) :
    ∀ᶠ z in 𝓝 x, (A z).PosDef := by
  induction n with
  | zero =>
    exact Filter.Eventually.of_forall (fun z => by
      have he : A z = 1 := Subsingleton.elim _ _
      rw [he]
      exact PosDef.one)
  | succ n ih =>
    let L := fun z => choleskyLeading (A z)
    let B := fun z => choleskyColumn (A z)
    let D := fun z => choleskyDiagonal (A z)
    have hentry (i j : Fin (n + 1)) : ContinuousAt (fun z => A z i j) x :=
      (continuous_apply_apply i j).continuousAt.comp hA
    have hL : ContinuousAt L x := by
      apply continuousAt_pi.mpr
      intro i
      apply continuousAt_pi.mpr
      intro j
      exact hentry i.castSucc j.castSucc
    have hB : ContinuousAt B x := by
      apply continuousAt_pi.mpr
      intro i
      apply continuousAt_pi.mpr
      intro _
      exact hentry i.castSucc (Fin.last n)
    have hD : ContinuousAt D x := by
      apply continuousAt_pi.mpr
      intro _
      apply continuousAt_pi.mpr
      intro _
      exact hentry (Fin.last n) (Fin.last n)
    have hLpos : (L x).PosDef := hpos.submatrix (Fin.castSucc_injective n)
    have hLherm : ∀ᶠ z in 𝓝 x, (L z).IsHermitian :=
      hHerm.mono (fun _ hz => hz.submatrix Fin.castSucc)
    have hevent := ih L hL hLherm hLpos
    have hdet : (L x).det ≠ 0 := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp hLpos.isUnit)
    have hInv : ContinuousAt (fun z => (L z)⁻¹) x := by
      have hscalar : ContinuousAt Ring.inverse (L x).det := by
        simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
      exact (continuousAt_matrix_inv (L x) hscalar).comp hL
    have hpivot : ContinuousAt (fun z => schurPivot (L z) (B z) (D z)) x := by
      unfold schurPivot
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      have hb (i : Fin n) (j : Fin 1) : ContinuousAt (fun z => B z i j) x :=
        (continuous_apply_apply i j).continuousAt.comp hB
      have hd : ContinuousAt (fun z => D z 0 0) x :=
        (continuous_apply_apply 0 0).continuousAt.comp hD
      have hi (i j : Fin n) : ContinuousAt (fun z => (L z)⁻¹ i j) x :=
        (continuous_apply_apply i j).continuousAt.comp hInv
      exact hd.sub (tendsto_finsetSum _ (fun j _ =>
        (tendsto_finsetSum _ (fun i _ => (hb i 0).star.mul (hi i j))).mul (hb j 0)))
    have hre : 0 < (schurPivot (L x) (B x) (D x)).re :=
      (Complex.lt_def.mp ((cholesky_last_iff (A x) hpos.1 hLpos).mp hpos)).1
    have hp := (Complex.continuous_re.continuousAt.comp hpivot).eventually (lt_mem_nhds hre)
    filter_upwards [hevent, hHerm, hp] with z hz hherm hpositive
    apply (cholesky_last_iff (A z) hherm hz).mpr
    apply Complex.lt_def.mpr
    refine ⟨hpositive, ?_⟩
    have hDh : (D z).IsHermitian := by
      change (A z).submatrix (fun _ : Fin 1 => Fin.last n) (fun _ : Fin 1 => Fin.last n) |>.IsHermitian
      exact hherm.submatrix _
    have hs : (D z - (B z)ᴴ * (L z)⁻¹ * B z).IsHermitian :=
      hDh.sub (isHermitian_conjTranspose_mul_mul _ hz.1.inv)
    have hh := congrArg Complex.im (hs.apply 0 0)
    change -(schurPivot (L z) (B z) (D z)).im = (schurPivot (L z) (B z) (D z)).im at hh
    change (0 : ℝ) = (schurPivot (L z) (B z) (D z)).im
    linarith

end
end krylov.XR
