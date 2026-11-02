import jacobi.Jacobi.NodeGap
import jacobi.Jacobi.ModelGap

/-!
Article: jacobi, Proposition B.1.
A common positive constant and a single original degree threshold give
both endpoint-distance bounds, every consecutive angular gap, and the
exact pairwise quadratic separation of both the genuine nodes and the
literal corrected trigonometric model. All original-function estimates
and source-parameter hypotheses are discharged.
Use: supplies all source endpoint and separation estimates to the later interpolation and finite-chain proofs.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter
open scoped Topology

/-- The full geometric part of the article's uniform two-edge zero proposition, with one common positive constant and one degree threshold.
Use: supplies all source endpoint and separation estimates to the later interpolation and finite-chain proofs.
Article: jacobi, Proposition B.1.
Proof: combine the proved genuine two-edge distance theorem, the true
Sturm angular-gap theorem, and the actual and explicit-model pair-gap
theorems. Take the minimum of their positive lower constants and combine
their eventual degree thresholds. The ordered pair form is equivalent
to the arbitrary-pair statement by symmetry of absolute difference. -/
theorem zeros_geometry {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∃ n0 : ℕ,∀ n≥n0,0<frequency a b n ∧
      (∀ i : Fin n,c*(edgeIndex n i.val:ℝ)/frequency a b n≤min (angle a b ha hb i) (Real.pi-angle a b ha hb i) ∧
        min (angle a b ha hb i) (Real.pi-angle a b ha hb i)≤C*(edgeIndex n i.val:ℝ)/frequency a b n) ∧
      (∀ k : ℕ,∀ hk : k+1<n,c/frequency a b n≤
        angle a b ha hb (⟨k+1,hk⟩ : Fin n)-angle a b ha hb (⟨k,by omega⟩ : Fin n)) ∧
      (∀ i j : Fin n,i≤j → c*((j.val-i.val:ℕ):ℝ)*(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2≤
        |(nodes a b ha hb n).value i-(nodes a b ha hb n).value j|) ∧
      (∀ i j : Fin n,i≤j → c*((j.val-i.val:ℕ):ℝ)*(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2≤
        |modelNode a b n i.val-modelNode a b n j.val|) := by
  -- All four component estimates are unconditional statements about the original source families; this step only unifies their constants and finite thresholds.
  obtain ⟨ce,C,hce,hC,hends⟩ := angle_endpoint_bounds ha hb
  obtain ⟨cg,hcg,hgaps⟩ := angle_gap_bound ha hb
  obtain ⟨cn,hcn,hnodes⟩ := node_gap_bound ha hb
  let c := min ce (min cg (min cn (1/16:ℝ)))
  have hc : 0<c := lt_min hce (lt_min hcg (lt_min hcn (by norm_num)))
  have hce' : c≤ce := min_le_left _ _
  have hcg' : c≤cg := (min_le_right _ _).trans (min_le_left _ _)
  have hcn' : c≤cn := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcm' : c≤(1/16:ℝ) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c,C,hc,hC,?_⟩
  apply eventually_atTop.mp
  filter_upwards [hends,hgaps,hnodes,model_gap_bound ha hb] with n he hg hz hm
  have hN := he.1
  refine ⟨hN,?_,?_,?_,?_⟩
  · intro i
    refine ⟨?_,(he.2 i).2⟩
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hce' (Nat.cast_nonneg _)) hN.le).trans (he.2 i).1
  · intro k hk
    exact (div_le_div_of_nonneg_right hcg' hN.le).trans (hg.2 k hk)
  · intro i j hij
    calc
      _ ≤ cn*((j.val-i.val:ℕ):ℝ)*(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2 := by gcongr
      _ ≤ _ := hz.2 i j hij
  · intro i j hij
    calc
      _ ≤ (1/16:ℝ)*((j.val-i.val:ℕ):ℝ)*(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2 := by gcongr
      _ ≤ _ := hm.2 i j hij

end
end jacobi.Jacobi
