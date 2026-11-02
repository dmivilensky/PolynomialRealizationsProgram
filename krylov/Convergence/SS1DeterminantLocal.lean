import krylov.Convergence.WindowDeterminant
import krylov.Convergence.SS1Rate

/-!
Article: main_krylov, lem:ss1-local, actual normalized-determinant criterion.
Use: obtain a common starting radius for the genuine recursive SS1 method
from exactly the source's determinant separation, rather than assuming a
least-gain or inverse bound. Convergence and the characteristic R-order are
conclusions of the actual execution theorem.
Source: the Appendix G invariant ball, finite-dimensional compactness of
determinant-separated unit-column windows, and the proved scalar R-order API.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Metric Filter Set Topology Asymptotics krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The genuine local SS1 theorem under the original normalized determinant
condition, in canonical coordinates. The same radius works for every
initial finite history satisfying that original window condition. -/
theorem ss1_local_determinant_convergence
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    {R σ₀ : ℝ} (hR : 0<R) (hσ₀ : 0<σ₀)
    (hball : closedBall (0:EuclideanSpace ℝ (Fin (n+1))) R⊆S) :
    ∃ r : ℝ,0<r ∧r≤R ∧∀ seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
      (∀ i,‖seed i‖≤r) →
      (∀ k,σ₀≤|(windowMatrix (unitWindow
        (windowStep (n:=n+1) (ss1Sequence G seed) k))).det|) →
      Tendsto (ss1Sequence G seed) atTop (𝓝 0) ∧
      ((fun k=>ss1Sequence G seed (k+1)) =o[atTop] (fun k=>‖ss1Sequence G seed k‖)) ∧
      HasROrder (fun k=>‖ss1Sequence G seed k‖) (oneGradientRoot (n+2)) := by
  obtain ⟨C,hC,hbound⟩ := unit_window_determinant_inverse (n:=n+1) hσ₀
  let B := 1+((n+1:ℕ):ℝ)*C^2
  have hB : 0<B := by dsimp only [B]; positivity
  let r := min R (8*((L:ℝ)+1)*B)⁻¹
  have hr : 0<r := lt_min hR (inv_pos.mpr (by positivity))
  have hrR : r≤R := min_le_left _ _
  have hden : 0<8*((L:ℝ)+1)*B := by positivity
  have hrad : r*(8*((L:ℝ)+1)*B)≤1 := by
    have hh := min_le_right R (8*((L:ℝ)+1)*B)⁻¹
    exact (le_div_iff₀ hden).mp (by simpa only [one_div] using hh)
  have hsmall : 2*(L:ℝ)*r*(1+(n+1)*C^2)≤1/2 := by
    have hp : 0≤r*B := mul_nonneg hr.le hB.le
    have hh : 2*(L:ℝ)*r*B≤1/2 := by nlinarith only [hrad,hp]
    simpa only [B,Nat.cast_add,Nat.cast_one] using hh
  refine ⟨r,hr,hrR,?_⟩
  intro seed hseed hdet
  have hi (k : ℕ) :
      IsUnit (windowMatrix (unitWindow (windowStep (n:=n+1) (ss1Sequence G seed) k))).det ∧
      ‖(windowMatrix (unitWindow (windowStep (n:=n+1) (ss1Sequence G seed) k)))⁻¹‖≤C := by
    let s := windowStep (n:=n+1) (ss1Sequence G seed) k
    have hu : IsUnit (windowMatrix (unitWindow s)).det :=
      isUnit_iff_ne_zero.mpr (abs_pos.mp (hσ₀.trans_le (hdet k)))
    have hs (i : Fin (n+1)) : s i≠0 := by
      intro hz
      have hh := windowMatrix_step_ne_zero (unitWindow s) hu i
      apply hh
      simp only [unitWindow,krylov.Methods.rescaleWindow,hz,smul_zero]
    exact hbound (unitWindow s) (unitWindow_norm s hs) (hdet k)
  have hc := ss1Sequence_local_convergence G H S hS hH hH₀ hG hG₀ seed hr hC.le
    (fun z hz=>hball (closedBall_subset_closedBall hrR hz)) hseed hi hsmall
  have h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S := hball (by simpa using hR.le)
  have hnbhd : S∈𝓝 (0:EuclideanSpace ℝ (Fin (n+1))) :=
    Metric.mem_nhds_iff.mpr ⟨R,hR,ball_subset_closedBall.trans hball⟩
  have hgain : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k))).det ∧
      C⁻¹≤leastGain (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k))) := by
    apply Filter.Eventually.of_forall
    intro k
    exact ⟨(hi k).1,inv_anti₀ (inverse_norm_pos _ (hi k).1) (hi k).2⟩
  exact ⟨hc.2.2,ss1Sequence_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀ seed hc.2.2
    (inv_pos.mpr hC) hgain,ss1Sequence_rorder G H S hS h₀ hnbhd hH hH₀ hG hG₀ seed hc.2.2
    (inv_pos.mpr hC) hgain⟩

end
end krylov.Convergence
