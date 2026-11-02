import krylov.Convergence.OldestWindowSource
import krylov.Convergence.SecantMovingModel

/-!
Article: main_krylov, thm:Ip, oldest error for a genuine moving frame.
Use: isolate the actual oldest observed diagonal while allowing the last
column to be the real current RFC probe. All model and inverse limits are
derived from genuine derivatives and the stated frame/age assumptions.
Source: sharp endpoint FTC, actual oldest-dual geometry and continuity of
inversion at the identity.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Secant krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- The exact oldest-distance leading bound for actual moving full secant
queries. Only the newer source endpoints enter the little-o remainder. -/
theorem moving_source_oldest_asymptotic
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (a b : ℕ → Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (x : ℕ → EuclideanSpace ℝ (Fin (n+1))) (q : ℕ → ℝ)
    (ha : ∀ i,Tendsto (fun k=>a k i) atTop (𝓝 0))
    (hb : ∀ i,Tendsto (fun k=>b k i) atTop (𝓝 0)) (hx : Tendsto x atTop (𝓝 0))
    {C : ℝ} (hC : 0≤C)
    (hframe : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (fun i=>b k i-a k i))).det ∧
      ‖(windowMatrix (unitWindow (fun i=>b k i-a k i)))⁻¹‖≤C)
    (hnew : (fun k=>newerWindowRadius (a k) (b k))=o[atTop] q)
    (hcurrent : (fun k=>‖x k‖)=o[atTop] q) :
    ∃ m r : ℕ → ℝ,Tendsto m atTop (𝓝 1) ∧r=o[atTop] q ∧∀ᶠ k in atTop,
      let s := fun i=>b k i-a k i
      let y := fun i=>G (b k i)-G (a k i)
      let V := windowMatrix (unitWindow s)
      ‖ss1Point s y (G (x k)) (x k)‖≤m k*
        (((L:ℝ)/2*(‖a k 0‖+‖b k 0‖)) /
          (Metric.infDist (euclideanColumn V 0) (newerColumnSpan V:Set _))^2+r k)*‖x k‖ := by
  let s := fun k i=>b k i-a k i
  let y := fun k i=>G (b k i)-G (a k i)
  let V := fun k=>windowMatrix (unitWindow (s k))
  let M := fun k=>inverseCongruence (V k) (ss1Model (unitWindow (s k)) (unitWindowImages (s k) (y k)))
  let m := fun k=>‖(M k)⁻¹‖
  let r := fun k=>((n+1:ℕ):ℝ)*((L:ℝ)/2)*C^2*newerWindowRadius (a k) (b k)+(L:ℝ)/2*‖x k‖
  have hm : ∀ᶠ k in atTop,(∀ i,a k i∈S) ∧(∀ i,b k i∈S) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)
  have hmodel := source_moving_model_tendsto G H S hS h₀ hH hH₀ hG a b ha hb hm hC hframe
  have hmt : Tendsto m atTop (𝓝 1) := by
    simpa only [m,M,V,s,y,norm_one] using hmodel.2.1.norm
  have hru : r=o[atTop] q := by
    simpa only [r] using (hnew.const_mul_left (((n+1:ℕ):ℝ)*((L:ℝ)/2)*C^2)).add
      (hcurrent.const_mul_left ((L:ℝ)/2))
  refine ⟨m,r,hmt,hru,?_⟩
  have hMd : ∀ᶠ k in atTop,IsUnit (M k).det :=
    (hmodel.1.eventually (Units.isOpen.mem_nhds isUnit_one)).mono
      fun _ h=>(Matrix.isUnit_iff_isUnit_det _).mp h
  filter_upwards [hm,hframe,hMd,hx.eventually hnbhd] with k hk hf hMk hxk
  have hh := ss1_oldest_source_step_bound G H S hS h₀ hH hH₀ hG hG₀ (a k) (b k) (x k)
    hk.1 hk.2 hxk hf.1 hMk
  apply hh.trans
  have hrest : (((n+1:ℕ):ℝ)*((L:ℝ)/2*newerWindowRadius (a k) (b k)))/(leastGain (V k))^2+
      (L:ℝ)/2*‖x k‖≤r k := by
    dsimp only [r,leastGain]
    rw [inv_pow,div_inv_eq_mul]
    have hp := pow_le_pow_left₀ (norm_nonneg _) hf.2 2
    have hn := mul_le_mul_of_nonneg_left hp (show 0≤((n+1:ℕ):ℝ)*((L:ℝ)/2*newerWindowRadius (a k) (b k)) by
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (newerWindowRadius_nonneg _ _)))
    nlinarith only [hn]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (by simpa only [add_assoc] using add_le_add le_rfl hrest) (norm_nonneg _)) (norm_nonneg _)

end
end krylov.Convergence
