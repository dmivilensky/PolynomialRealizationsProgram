import krylov.Convergence.SlidingFCSharpTerms

/-!
Article: main_krylov, thm:G, source-level exceptional FC pair.
Use: isolate the genuine oldest/next pair with the exact endpoint weight
one half; the remaining terms retain their actual individual masses.
Source: Hessian FTC, scalar Schwarz symmetry, and observed FC conjugacy.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions chebyshev1.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- Splitting a genuine finite staircase at its unique exceptional pair. -/
theorem fcPathMass_sum
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2))) (x : ℕ → EuclideanSpace ℝ (Fin (n+2))) (k : ℕ) :
    (∑ i : Fin (n+2),∑ j : Fin (n+2),fcPathPairMass (n:=n) H x k (i,j))=
      fcPathPairMass (n:=n) H x k (0,1)+fcPathNewerMass (n:=n) H x k := by
  rw [←Fintype.sum_prod_type]
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ ((0,1):Fin (n+2)×Fin (n+2)))).symm

/-- The terminal genuine gradient is reconstructed from the true observed
FC staircase, with the exact oldest-pair endpoint coefficient. -/
theorem source_fc_sharp_path_residual
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} {L : ℝ≥0} (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,
      HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z)
    (x : ℕ → EuclideanSpace ℝ (Fin (n+2))) (k : ℕ)
    (hmem : ∀ j≤n+2,‖x (k+j)‖<r)
    (hline : ∀ j<n+2,inner ℝ (x (k+j+1)-x (k+j)) (G (x (k+j+1)))=0)
    (hconj : ∀ i j,i<j → j<n+2 →
      inner ℝ (G (x (k+i+1))-G (x (k+i))) (x (k+j+1)-x (k+j))=0)
    (hu : IsUnit (windowMatrix (unitWindow (windowStep (n:=n+2) x k))).det) :
    ‖G (x (k+n+2))‖≤‖(windowMatrix (unitWindow (windowStep (n:=n+2) x k)))⁻¹‖*
      ((L:ℝ)/2*(‖x (k+1)-x k‖+‖x (k+2)-x (k+1)‖)*‖x (k+2)-x (k+1)‖+
        fcPathNewerMass (n:=n) H x k) := by
  let A := fcPathSegment H x k
  have hm j (hj : j≤n+2) : x (k+j)∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (hmem j hj).le
  have hy j (hj : j<n+2) : G (x (k+j+1))-G (x (k+j))=A j (x (k+j+1)-x (k+j)) := by
    have hp t (ht : t∈Icc (0:ℝ) 1) : x (k+j)+t • (x (k+j+1)-x (k+j))∈Metric.closedBall 0 r :=
      (convex_closedBall _ _).add_smul_mem (hm j (by omega))
        (by simpa only [add_sub_cancel,Nat.add_assoc] using hm (j+1) (by omega)) ht
    have he := averagedDerivative_apply G H (x (k+j)) (x (k+j+1)-x (k+j))
      (hH.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp)
      (fun t ht=>hG _ (hp t ht))
    simpa only [A,fcPathSegment,add_sub_cancel] using he.symm
  have hsym j (hj : j<n+2) : (A j).toLinearMap.IsSymmetric :=
    source_segment_symmetric f G H hH hf hG _ _ (hmem j (by omega))
      (by simpa only [Nat.add_assoc] using hmem (j+1) (by omega))
  have hsrc := conjugate_staircase_weighted_frame (fun j=>G (x (k+j)))
    (fun j=>x (k+j+1)-x (k+j)) A (by simpa only [Nat.add_assoc] using hy)
    hsym (by simpa only [Nat.add_assoc] using hline)
    (by simpa only [Nat.add_assoc] using hconj) (by
      exact hu)
  have hsum : (∑ i : Fin (n+2),∑ j : Fin (n+2),
      if i<j then ‖A j.val-A i.val‖*‖x (k+j.val+1)-x (k+j.val)‖ else 0)=
      fcPathPairMass (n:=n) H x k (0,1)+fcPathNewerMass (n:=n) H x k := fcPathMass_sum H x k
  have hpair : fcPathPairMass (n:=n) H x k ((0,1):Fin (n+2)×Fin (n+2))≤
      (L:ℝ)/2*(‖x (k+1)-x k‖+‖x (k+2)-x (k+1)‖)*‖x (k+2)-x (k+1)‖ := by
    have hh := source_segment_comparison H (Metric.closedBall 0 r) (convex_closedBall _ _) hH
      (x (k+1)) (x (k+2)) (x k) (x (k+1))
      (hm 1 (by omega)) (hm 2 (by omega)) (by simpa only [Nat.add_zero] using hm 0 (by omega))
      (hm 1 (by omega))
    have hi : (0:Fin (n+2))<1 := by simp only [Fin.lt_def,Fin.val_zero,Fin.val_one];omega
    simpa only [fcPathPairMass,ite_eq_left hi,fcPathSegment,Fin.val_zero,Fin.val_one,
      Nat.add_zero,show k+1+1=k+2 by omega] using mul_le_mul_of_nonneg_right hh
        (norm_nonneg (x (k+2)-x (k+1)))
  apply hsrc.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [hsum]
  exact add_le_add hpair le_rfl

end
end krylov.Convergence
