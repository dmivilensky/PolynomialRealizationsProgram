import krylov.Correction.TerminalObliqueResponse
import krylov.Correction.FullReconstruction
import krylov.Correction.UniformBasisInverse
import krylov.Correction.ProbedConjugacy
import krylov.Methods.ProjectedSearch

/-!
Article: main_krylov, thm:UCq, uniform incoming terminal fresh response.
Use: Bound the actual post-search gradient by its genuine oblique fresh
response using measured old secants, without dividing by the last line length.
Source: the proved exact search-pair identity and oblique response coordinates;
mathlib's finite telescoping sum and Euclidean coordinate norm inequalities.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The single-last-line oblique response has exactly the true accumulated-increment pairing at every old column and zero last coordinate.
Use: Identify the actual incoming terminal response before taking a uniform bound.
Article: main_krylov, thm:UCq.
Proof: Specialize the proved genuine oblique response coordinates. The finite conditional sum selects only the supplied actual last searched line.
-/
theorem terminal_oblique_response_coordinates (T : Matrix (Fin n) (Fin n) ℝ)
    (hT : IsUnit T.det) (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    inner ℝ (WithLp.toLp 2 (fun a => T a i)) (obliqueResponse T E (terminalLineSequence n v))=
      if i.val<n-1 then inner ℝ (WithLp.toLp 2 (fun a => T a i))
        (cgOperator (∑ l ∈ Ico i.val (n-1), E l) v) else 0 := by
  rw [obliqueResponse_coordinates T hT]
  have hiff : i.val+1≤n-1 ∧ n-1<n ↔ i.val<n-1 := by omega
  simp only [terminalLineSequence,apply_ite,map_zero,inner_zero_right,
    sum_ite_eq',mem_Ico,hiff,cgOperator]
  by_cases h : i.val<n-1 <;> simp only [h,ite_true,ite_false]

/-- The true finite operator increments telescope to their actual endpoint difference.
Use: Identify the terminal drift in the original chronological source variables.
Article: main_krylov, thm:UCq.
Proof: Replace every true increment by its consecutive difference and reuse Finset.sum_Ico_sub.
-/
theorem terminal_increment_sum (A E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hInc : ∀ j<n-1, A (j+1)-A j=E j) {i : ℕ} (hi : i≤n-1) :
    (∑ l ∈ Ico i (n-1), E l)=A (n-1)-A i := by
  calc
    _ = ∑ l ∈ Ico i (n-1), (A (l+1)-A l) := by
      apply sum_congr rfl
      intro l hl
      exact (hInc l (mem_Ico.mp hl).2).symm
    _ = _ := sum_Ico_sub A hi

/-- The true post-search gradient differs from its genuine oblique fresh response by a uniform old-residual plus measured-contamination bound.
Use: Supply the second-order incoming-vector estimate for the actual uniform RFC response, including a zero final searched line.
Article: main_krylov, thm:UCq.
Proof: The exact observed-pair search identity leaves only the old projected gradient and the actual measured-pair discrepancy in each old coordinate. Exact current search kills the last coordinate. Bound those real coordinates and reconstruct with the derived half-Gram inverse transpose. No individual step length or reference energy is inverted.
-/
theorem terminal_incoming_fresh_bound {k : ℕ}
    (t : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1)))
    (A E : ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hA : ∀ j, (A j).IsSymm) (hInc : ∀ j<k, A (j+1)-A j=E j)
    (G line : EuclideanSpace ℝ (Fin (k+1)))
    (y : Fin k → EuclideanSpace ℝ (Fin (k+1)))
    {R η : ℝ} (hη : 0≤η)
    (hGram : ‖(fullBasisMatrix t)ᵀ*fullBasisMatrix t-1‖≤(1/2 : ℝ))
    (hR : ‖projectedResidual (fun i : Fin k => t i.castSucc) G‖≤R)
    (hy : ∀ i : Fin k, ‖y i-cgOperator (A i.val) (t i.castSucc)‖≤η)
    (hconj : ∀ i : Fin k, inner ℝ (y i) line=0)
    (hcurrent : inner ℝ (t (Fin.last k)) (G+cgOperator (A k) line)=0) :
    ‖G+cgOperator (A k) line-obliqueResponse (fullBasisMatrix t) E
      (terminalLineSequence (k+1) line)‖≤2*Real.sqrt (k+1)*(R+η*‖line‖) := by
  let T := fullBasisMatrix t
  let f := obliqueResponse T E (terminalLineSequence (k+1) line)
  let u := G+cgOperator (A k) line-f
  obtain ⟨hu,_hT,hTi,_herr⟩ := full_column_inverse_transpose_bounds T hGram
  have hR0 : 0≤R := (norm_nonneg _).trans hR
  have hC : 0≤R+η*‖line‖ := add_nonneg hR0 (mul_nonneg hη (norm_nonneg _))
  have hcoord (i : Fin (k+1)) : |inner ℝ (t i) u|≤R+η*‖line‖ := by
    have hf := terminal_oblique_response_coordinates T hu E line i
    change inner ℝ (t i) f=_ at hf
    by_cases hi : i.val<k
    · let j : Fin k := ⟨i.val,hi⟩
      have hij : j.castSucc=i := Fin.ext rfl
      have hs := search_pair_identity (cgOperator (A i.val)) (cgOperator (A k))
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (hA i.val)))
        (t i) (y j) (y j-cgOperator (A i.val) (t i)) line G (by abel) (hconj j)
      have hsum : (∑ l ∈ Ico i.val k, E l)=A k-A i.val := by
        simpa only [Nat.add_sub_cancel] using
          terminal_increment_sum A E (by simpa only [Nat.add_sub_cancel] using hInc) hi.le
      rw [show k+1-1=k by omega,ite_eq_left hi,hsum] at hf
      change inner ℝ (t i) f=inner ℝ (t i) (cgOperator (A k-A i.val) line) at hf
      have hident : inner ℝ (t i) u=inner ℝ (t i) G-
          inner ℝ (y j-cgOperator (A i.val) (t i)) line := by
        dsimp only [u]
        rw [inner_sub_right,hs,hf]
        simp only [cgOperator,map_sub,_root_.sub_apply]
        ring
      have hp := PiLp.norm_apply_le (projectedResidual (fun j : Fin k => t j.castSucc) G) j
      change ‖inner ℝ (t j.castSucc) G‖≤_ at hp
      rw [hij,Real.norm_eq_abs] at hp
      have hxi := norm_inner_le_norm (𝕜 := ℝ) (y j-cgOperator (A i.val) (t i)) line
      rw [Real.norm_eq_abs] at hxi
      have hxi' : ‖y j-cgOperator (A i.val) (t i)‖≤η := by simpa only [hij] using hy j
      rw [hident]
      have htri (a b : ℝ) : |a-b|≤|a|+|b| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le a b
      exact (htri _ _).trans (add_le_add (hp.trans hR)
        (hxi.trans (mul_le_mul_of_nonneg_right hxi' (norm_nonneg _))))
    · have hilast : i=Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
      have hv : ¬i.val<k+1-1 := by omega
      rw [ite_eq_right hv] at hf
      dsimp only [u]
      rw [inner_sub_right,hf,hilast,hcurrent,sub_self,abs_zero]
      exact hC
  have hp : ‖projectedResidual t u‖≤Real.sqrt (k+1)*(R+η*‖line‖) := by
    change ‖WithLp.toLp 2 (fun i => inner ℝ (t i) u)‖≤Real.sqrt (k+1)*(R+η*‖line‖)
    simpa only [Nat.cast_add,Nat.cast_one] using
      coordinate_norm_le_sqrt_card (fun i => inner ℝ (t i) u) hC hcoord
  have hcancel : cgOperator Tᵀ⁻¹ (projectedResidual t u)=u := by
    rw [projectedResidual_fullBasisMatrix]
    change cgOperator Tᵀ⁻¹ (cgOperator Tᵀ u)=u
    simp only [cgOperator]
    rw [← mul_apply_eq_comp,← map_mul,
      Matrix.nonsing_inv_mul _ (by simpa only [Matrix.det_transpose] using hu),map_one,one_apply_eq_self]
  calc
    ‖u‖ = ‖cgOperator Tᵀ⁻¹ (projectedResidual t u)‖ := congrArg norm hcancel.symm
    _ ≤ ‖cgOperator Tᵀ⁻¹‖*‖projectedResidual t u‖ := (cgOperator Tᵀ⁻¹).le_opNorm _
    _ ≤ 2*(Real.sqrt (k+1)*(R+η*‖line‖)) := by
      apply mul_le_mul _ hp (norm_nonneg _) (by norm_num)
      simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hTi
    _ = _ := by ring

end
end krylov.Correction
