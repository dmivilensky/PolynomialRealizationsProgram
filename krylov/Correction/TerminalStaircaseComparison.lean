import krylov.Correction.ObliqueStaircase
import krylov.Correction.TerminalObliqueResponse

/-!
Article: main_krylov, thm:UCq, weighted terminal staircase comparison.
Use: Retain the true last reference line as a weight until the two genuine
staircase actions have been compared, allowing arbitrarily small last energies.
Source: the proved oblique fresh-response and weighted staircase estimates;
only genuine finite spectral operator products enter the comparison.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Appending a genuine zero increment does not change the actual oblique staircase.
Use: Match the full model factorization with the original old-increment source.
Article: main_krylov, thm:UCq.
Proof: The last finite-sum summand is exactly the compressed zero matrix.
-/
theorem obliqueStaircase_succ_of_zero (T : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (N : ℕ) (hE : E N=0) : obliqueStaircase T E F (N+1)=obliqueStaircase T E F N := by
  simp only [obliqueStaircase,sum_range_succ,hE,Matrix.mul_zero,Matrix.zero_mul,add_zero]

/-- Actual terminal staircase actions have an explicit uniform difference controlled by the true line error and reference-line-weighted old-flag errors.
Use: Replace the genuine moving RFC geometry by the original CG coefficient with a cubic cost.
Article: main_krylov, thm:UCq.
Proof: Split the two real operator actions into the fresh-vector change and the staircase change. Keep the true reference line norm on the latter until applying the weighted staircase bound; bound the first using the actual oblique fresh-response comparison and total increment norms.
-/
theorem terminal_staircase_response_difference (T Q : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (v w : EuclideanSpace ℝ (Fin n))
    {ε η : ℝ} (hε : 0≤ε) (hη : 0≤η)
    (hT : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) (hQ : ‖Qᵀ*Q-1‖≤(1/2 : ℝ))
    (hline : ‖v-w‖≤ε)
    (hflag : ∀ l<n-1, ‖w‖*‖transportedFlag T l-transportedFlag Q l‖≤η) :
    let W := ∑ l ∈ range n, ‖E l‖
    let V := ∑ l ∈ range (n-1), ‖E l‖
    let fT := obliqueResponse T E (terminalLineSequence n v)
    let fQ := obliqueResponse Q E (terminalLineSequence n w)
    ‖cgOperator (obliqueStaircase T E F (n-1)) fT-
      cgOperator (obliqueStaircase Q E F (n-1)) fQ‖≤
      (4*V+‖F‖)*(W*(2*(n : ℝ)*ε+η))+8*V*W*η := by
  dsimp only
  let W := ∑ l ∈ range n, ‖E l‖
  let V := ∑ l ∈ range (n-1), ‖E l‖
  let LT := cgOperator (obliqueStaircase T E F (n-1))
  let LQ := cgOperator (obliqueStaircase Q E F (n-1))
  let fT := obliqueResponse T E (terminalLineSequence n v)
  let fQ := obliqueResponse Q E (terminalLineSequence n w)
  have hW : 0≤W := sum_nonneg fun _ _ => norm_nonneg _
  have hV : 0≤V := sum_nonneg fun _ _ => norm_nonneg _
  have hLT : ‖LT‖≤4*V+‖F‖ := by
    simpa only [LT,cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using obliqueStaircase_norm T E F (n-1) hT
  have hdf : ‖fT-fQ‖≤W*(2*(n : ℝ)*ε+η) :=
    terminal_oblique_response_difference T Q E v w hε hη hT hline hflag
  have hfQ : ‖fQ‖≤2*W*‖w‖ := terminal_oblique_response_norm Q E w hQ
  have hdiff : ‖w‖*‖LT-LQ‖≤4*V*η := by
    simpa only [LT,LQ,cgOperator,← map_sub,Matrix.l2_opNorm_toEuclideanCLM] using
      obliqueStaircase_weighted_difference T Q E F (n-1) hT hQ (norm_nonneg w) hflag
  have hfirst : ‖LT (fT-fQ)‖≤(4*V+‖F‖)*(W*(2*(n : ℝ)*ε+η)) :=
    (LT.le_opNorm _).trans (mul_le_mul hLT hdf (norm_nonneg _) (by positivity))
  have hsecond : ‖(LT-LQ) fQ‖≤8*V*W*η := by
    calc
      _ ≤ ‖LT-LQ‖*‖fQ‖ := (LT-LQ).le_opNorm _
      _ ≤ ‖LT-LQ‖*(2*W*‖w‖) := mul_le_mul_of_nonneg_left hfQ (norm_nonneg _)
      _ = (2*W)*(‖w‖*‖LT-LQ‖) := by ring
      _ ≤ (2*W)*(4*V*η) := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = _ := by ring
  have hsplit : LT fT-LQ fQ=LT (fT-fQ)+(LT-LQ) fQ := by
    simp only [map_sub,_root_.sub_apply]
    abel
  change ‖LT fT-LQ fQ‖≤_
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

end
end krylov.Correction
