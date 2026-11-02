import krylov.Convergence.SS1PhysicalRate
import krylov.Convergence.WindowTranslation

/-!
Article: main_krylov, thm:Ip and thm:grow, arbitrary physical limit.
Use: center genuine physical executors at their actual critical point and
obtain the literal Hessian-norm R-order with the original physical gain.
Source: exact observed-rule translation and actual positive-root transport.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Centering preserves the exact physical source and every actual secant,
so the SS1 characteristic order holds at an arbitrary actual limit. -/
theorem ss1Sequence_centered_physical_rorder
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (center : EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : center∈S) (hnbhd : S∈𝓝 center)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H center=cgOperator base)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G center=0)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 center))
    {mu upper σ : ℝ} (hmu : 0<mu) (hu : 0<upper) (hσ : 0<σ)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hupper : ∀ v,inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep (ss1Sequence G seed) k)) c‖^2) :
    HasROrder (fun k=>‖(metricCoordinates base hb) (ss1Sequence G seed k-center)‖)
      (oneGradientRoot (n+2)) := by
  let Gc := fun z=>G (center+z)
  let Hc := fun z=>H (center+z)
  let sc := fun i=>seed i-center
  let Sc := (fun z=>center+z) ⁻¹' S
  have he (k : ℕ) : ss1Sequence G seed k-center=ss1Sequence Gc sc k :=
    ss1Sequence_translate G center seed k
  have hSc : Convex ℝ Sc := hS.affine_preimage (AffineMap.const ℝ _ center+AffineMap.id ℝ _)
  have hzc : (0:EuclideanSpace ℝ (Fin (n+1)))∈Sc := by simpa only [Sc,Set.mem_preimage,add_zero] using h₀
  have hnc : Sc∈𝓝 (0:EuclideanSpace ℝ (Fin (n+1))) := by
    exact (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa only [Pi.add_apply,id_eq,add_zero] using hnbhd)
  have hHc : LipschitzOnWith L Hc Sc := by
    rw [lipschitzOnWith_iff_norm_sub_le] at hH ⊢
    intro z hz w hw
    have hh := hH hz hw
    have heq : center+z-(center+w)=z-w := by abel
    simpa only [Hc,heq] using hh
  have hGc (z) (hz : z∈Sc) : HasFDerivAt Gc (Hc z) z := by
    have hh := (hG _ hz).comp z ((hasFDerivAt_id z).const_add center)
    convert! hh using 1
  have hcc : Tendsto (ss1Sequence Gc sc) atTop (𝓝 0) := by
    have hh := hconv.sub_const center
    simpa only [sub_self,Function.comp_def,he] using hh
  have hgc : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep (ss1Sequence Gc sc) k)) c‖^2 := by
    have hs (k : ℕ) : windowStep (n:=n+1) (ss1Sequence Gc sc) k=windowStep (ss1Sequence G seed) k := by
      funext i
      dsimp only [windowStep]
      rw [←he,←he]
      abel
    simpa only [hs] using hgain
  have hh := ss1Sequence_physical_rorder base hb Gc Hc Sc hSc hzc hnc hHc
    (by simpa only [Hc,add_zero] using hH₀) hGc
    (by simpa only [Gc,add_zero] using hG₀) sc hcc hmu hu hσ hlower hupper hgc
  simpa only [he] using hh

/-- A literal R-order on an actual tail is the same order on the entire
trajectory; its finite prefix changes only the multiplicative constant. -/
theorem HasROrder.of_tail {e : ℕ → ℝ} {τ : ℝ} (hτ : 0<τ) (K : ℕ)
    (h : HasROrder (fun j=>e (K+j)) τ) : HasROrder e τ := by
  obtain ⟨C,q,hC,hq,hq₁,hbound⟩ := h
  apply hasROrder_of_tail_exp e τ hτ K hC (neg_pos.mpr (Real.log_neg hq hq₁))
  intro j
  have hh := hbound j
  rw [Real.rpow_def_of_pos hq] at hh
  simpa only [neg_neg] using hh

end
end krylov.Convergence
