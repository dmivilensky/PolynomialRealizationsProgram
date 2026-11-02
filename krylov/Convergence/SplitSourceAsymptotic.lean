import krylov.Convergence.SplitAdmissibility
import krylov.Convergence.SecantWindowSource
import krylov.Convergence.SlidingMetricProbe

/-!
Article: main_krylov, condition (S) preceding thm:ss1F.
Use: prove the actual observed model-metric split has Cw→1 on genuine
convergent source windows, and the physical Euclidean split has the exact
sqrt(kappa) metric allowance. Source: endpoint Hessian FTC and orthogonal
projection, with actual primal/dual positive-root norm bounds.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {p : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
set_option maxHeartbeats 900000

/-- The genuine observed covector split satisfies (S) with one actual
factor tending to one, without assuming split admissibility or a lambda
bound. The anchor is arbitrary, including the true current iterate. -/
theorem covector_split_source_asymptotic (G : E → E) (H : E → E →L[ℝ] E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S) (hn : S∈𝓝 (0:E))
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (a b : ℕ → Fin p → E) (x : ℕ → E)
    (ha : ∀ i,Tendsto (fun k=>a k i) atTop (𝓝 0))
    (hb : ∀ i,Tendsto (fun k=>b k i) atTop (𝓝 0))
    (hs : ∀ᶠ k in atTop,∀ i,b k i-a k i≠0) :
    ∃ C : ℕ → ℝ,Tendsto C atTop (𝓝 1) ∧∀ᶠ k in atTop,∀ i,
      0< inner ℝ (G (b k i)-G (a k i)) (b k i-a k i) ∧
      ‖splitRemainder (a k i) (b k i-a k i) (x k)
        (covectorSplit (innerSL ℝ (G (b k i)-G (a k i))) (a k i) (b k i-a k i) (x k))‖≤
        C k*‖x k-b k i‖ := by
  let ε:=fun k=>(L:ℝ)/2*sourceWindowRadius (a k) (b k)
  have hε (k) : 0≤ε k:=mul_nonneg (by positivity) (sourceWindowRadius_nonneg _ _)
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have ht:=tendsto_finsetSum Finset.univ (fun i _=>(ha i).norm.add (hb i).norm)
    have hr : Tendsto (fun k=>sourceWindowRadius (a k) (b k)) atTop (𝓝 0) := by
      simpa only [sourceWindowRadius,norm_zero,add_zero,Finset.sum_const_zero] using ht
    simpa only [ε,mul_zero] using hr.const_mul ((L:ℝ)/2)
  let C:=fun k=>(1+ε k)/(1-ε k)
  have hCt : Tendsto C atTop (𝓝 1) := by
    have ht:=((tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1)).add hεt).div
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1)).sub hεt) (by norm_num)
    convert! ht using 1
    norm_num
  have hm : ∀ᶠ k in atTop,(∀ i,a k i∈S) ∧(∀ i,b k i∈S) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hn).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hn)
  refine ⟨C,hCt,?_⟩
  filter_upwards [hm,hs,hεt.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with k hk hsk hek i
  have he:=secant_image_endpoint_bound G H S hS h₀ hH hG _ _ (hk.1 i) (hk.2 i)
  rw [hH₀,ContinuousLinearMap.id_apply] at he
  have hy : ‖G (b k i)-G (a k i)-(b k i-a k i)‖≤ε k*‖b k i-a k i‖ := by
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.single_le_sum (fun j _=>add_nonneg (norm_nonneg (a k j)) (norm_nonneg (b k j))) (Finset.mem_univ i)
  have hh:=covectorSplit_near_identity_admissible (a k i) (b k i-a k i) (x k)
    (G (b k i)-G (a k i)) (hsk i) (hε k) hek hy
  simpa only [C,add_sub_cancel] using hh

/- The physical Euclidean split obeys (S) in the true metric with the
exact sqrt(upper/mu) allowance, hence the printed sqrt(kappa)(1+o(1)). -/
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem euclidean_split_metric_admissible {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    {mu upper : ℝ} (hmu : 0<mu) (hu : 0<upper)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hupper : ∀ v,inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (a s x : EuclideanSpace ℝ (Fin n)) (hs : s≠0) :
    ‖metricCoordinates base hb (splitRemainder a s x (innerSplit a s x))‖≤
      Real.sqrt (upper/mu)*‖metricCoordinates base hb (x-(a+s))‖ := by
  let T:=metricCoordinates base hb
  have hupperW:=metricCoordinates_norm_upper base hb hu hupper (splitRemainder a s x (innerSplit a s x))
  have hsplit:=innerSplit_admissible a s x hs
  have hinv:=(T.symm.toContinuousLinearMap).le_opNorm (T (x-(a+s)))
  change ‖T.symm (T (x-(a+s)))‖≤‖T.symm.toContinuousLinearMap‖*‖T (x-(a+s))‖ at hinv
  rw [T.symm_apply_apply] at hinv
  have hl : ‖x-(a+s)‖≤(Real.sqrt mu)⁻¹*‖T (x-(a+s))‖:=hinv.trans
    (mul_le_mul_of_nonneg_right (metricCoordinates_inverse_norm_bound base hb hmu hlower) (norm_nonneg _))
  have hh:=hupperW.trans ((mul_le_mul_of_nonneg_left hsplit (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg _)))
  apply hh.trans_eq
  rw [Real.sqrt_div hu.le]
  ring

end
end krylov.Convergence
