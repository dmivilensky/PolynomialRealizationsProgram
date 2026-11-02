import krylov.Convergence.SS1LocalConvergence
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Article: main_krylov, lem:ss1-local.
Use: the original lower bound on the normalized physical determinant gives
a genuine uniform inverse bound. A compactness proof suffices for the local
existence theorem and does not introduce a smaller least-gain hypothesis.
Source: finite-dimensional compactness, the exact determinant inverse
domain, and continuity of inversion on the unit group.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Metric Set Topology krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- The actual spectral norm of a unit-column square window is uniformly
bounded. The loose dimension bound is enough for the compact domain. -/
theorem unit_column_matrix_norm (V : Matrix (Fin n) (Fin n) ℝ)
    (hV : ∀ j,‖WithLp.toLp 2 (fun i=>V i j)‖=1) : ‖V‖≤n := by
  have he (i j : Fin n) : |V i j|≤(1:ℝ) := by
    have hh := PiLp.norm_apply_le (WithLp.toLp 2 (fun a=>V a j)) i
    simpa only [Real.norm_eq_abs,hV] using hh
  have hh := (spectral_le_hsNorm V).trans (hsNorm_le_dimension V (by norm_num : (0:ℝ)≤1) he)
  simpa only [mul_one] using hh

/-- A determinant-separated bounded family of genuine matrices has a common
inverse bound. This is the precise compactness step needed by the source's
determinant criterion; no bound on inverses is assumed. -/
theorem bounded_determinant_inverse {R σ : ℝ} (hσ : 0<σ) :
    ∃ C : ℝ,0<C ∧∀ V : Matrix (Fin n) (Fin n) ℝ,
      ‖V‖≤R → σ≤|V.det| → IsUnit V.det ∧‖V⁻¹‖≤C := by
  let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    closedBall 0 R∩{V|σ≤|V.det|}
  have hc : IsClosed {V : Matrix (Fin n) (Fin n) ℝ|σ≤|V.det|} :=
    isClosed_le continuous_const continuous_id.matrix_det.abs
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right hc
  have hunit (V : Matrix (Fin n) (Fin n) ℝ) (hV : V∈K) : IsUnit V.det := by
    rw [isUnit_iff_ne_zero]
    exact (abs_pos.mp (hσ.trans_le hV.2))
  have hi : ContinuousOn (fun V : Matrix (Fin n) (Fin n) ℝ=>V⁻¹) K := by
    intro V hV
    have hh := (NormedRing.inverse_continuousAt ((Matrix.isUnit_iff_isUnit_det _).mpr (hunit V hV)).unit)
    simpa only [IsUnit.unit_spec,Matrix.nonsing_inv_eq_ringInverse] using hh.continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hi
  refine ⟨max M 1,lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _),?_⟩
  intro V hV hd
  have hm : V∈K := ⟨by simpa only [mem_closedBall,dist_zero_right] using hV,hd⟩
  exact ⟨hunit V hm,(hM V hm).trans (le_max_left _ _)⟩

/-- The original normalized determinant condition yields a uniform inverse
constant for every actual unit-column window. -/
theorem unit_window_determinant_inverse {σ : ℝ} (hσ : 0<σ) :
    ∃ C : ℝ,0<C ∧∀ s : Fin n → EuclideanSpace ℝ (Fin n),
      (∀ i,‖s i‖=1) → σ≤|(windowMatrix s).det| →
      IsUnit (windowMatrix s).det ∧‖(windowMatrix s)⁻¹‖≤C := by
  obtain ⟨C,hC,hbound⟩ := bounded_determinant_inverse (n:=n) (R:=(n:ℝ)) hσ
  refine ⟨C,hC,?_⟩
  intro s hs hd
  apply hbound _ (unit_column_matrix_norm _ ?_) hd
  intro i
  simpa only [windowMatrix,WithLp.toLp_ofLp] using hs i

end
end krylov.Convergence
