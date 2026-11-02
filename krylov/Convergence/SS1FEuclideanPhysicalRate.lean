import krylov.Convergence.WindowArbitrarySplitCoordinates
import krylov.Convergence.SS1FPhysicalRate
import krylov.Convergence.SplitSourceAsymptotic

/-!
Article: main_krylov, cor:xrF, physical Euclidean-split SS1-F rate.
Use: prove the genuine physical sequence's improved rate while explicitly
pulling back its actual Euclidean split. The original physical independence
implies canonical independence; the Euclidean projection gives (S) with
sqrt(upper/mu), without any supplied split or model estimate.
Source: exact affine full-query coordinates and the actual SS1-F recurrence.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1200000

/-- The actual Euclidean midpoint split, computed only from observed
window points, independent of any unknown minimizer or Hessian. -/
def ss1FEuclideanSplit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (q : Fin (n+2) → E) (i : Fin (n+1)) : ℝ :=
  innerSplit (q i.castSucc) (q i.succ-q i.castSucc) (q (Fin.last (n+1)))

/-- Genuine physical SS1-F with its Euclidean split has R-order tau_1(n)
under the original source regularity, convergence and physical G2 only. -/
theorem ss1FEuclideanSequence_centered_physical_rorder
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (center : EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center∈S) (hn : S∈𝓝 center) {L L₃ : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hbase : H center=cgOperator base)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G center=0)
    (T₃ : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (hT : ∀ z∈centeredMetricDomain (metricCoordinates base hb) center S,
      HasFDerivAt (gradientHessian (centeredMetricHessian (metricCoordinates base hb) center H)) (T₃ z).form z)
    (hLip : ∀ z∈centeredMetricDomain (metricCoordinates base hb) center S,
      ∀ w∈centeredMetricDomain (metricCoordinates base hb) center S,∀ h,‖h‖=1 →
      |(T₃ z).form h h h-(T₃ w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1FSequence f G ss1FEuclideanSplit seed) atTop (𝓝 center))
    {mu upper σ : ℝ} (hmu : 0<mu) (hu : 0<upper) (hσ : 0<σ)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hupper : ∀ v,inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep
        (ss1FSequence f G ss1FEuclideanSplit seed) k)) c‖^2) :
    HasROrder (fun k=>‖(metricCoordinates base hb)
      (ss1FSequence f G ss1FEuclideanSplit seed k-center)‖) (oneGradientRoot (n+1)) := by
  let J := metricCoordinates base hb
  let fh := centeredMetricObjective J center f
  let Gh := centeredMetricGradient J center G
  let Hh := centeredMetricHessian J center H
  let Sh := centeredMetricDomain J center S
  let sh := fun i=>J (seed i-center)
  let x := ss1FSequence f G ss1FEuclideanSplit seed
  let xh := ss1FSequence fh Gh (centeredSplit J center ss1FEuclideanSplit) sh
  have he (k : ℕ) : J (x k-center)=xh k :=
    ss1FSequence_centered_coordinate J (metricCoordinates_inverse_symmetric base hb) center f G ss1FEuclideanSplit seed k
  have hSc : Convex ℝ Sh := centeredMetricDomain_convex J center hS
  have h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈Sh := by
    simpa only [Sh,centeredMetricDomain,Set.mem_preimage,map_zero,add_zero] using hc
  have hnh : Sh∈𝓝 (0:EuclideanSpace ℝ (Fin (n+1))) := centeredMetricDomain_mem_nhds J center hn
  have hHh := centeredMetricHessian_lipschitz base hb center H hH hmu hlower
  have hH₀ : Hh 0=ContinuousLinearMap.id ℝ _ :=
    coordinateDerivative_metric_zero base hb (fun z=>H (center+z)) (by simpa only [add_zero] using hbase)
  have hfh (z) (hz : z∈Sh) : HasFDerivAt fh (innerSL ℝ (Gh z)) z :=
    centeredMetricObjective_hasFDerivAt J (metricCoordinates_inverse_symmetric base hb) center f G z (hf _ hz)
  have hGh (z) (hz : z∈Sh) : HasFDerivAt Gh (Hh z) z :=
    centeredMetricGradient_hasFDerivAt J center G H z (hG _ hz)
  have hGz : Gh 0=0 := by simp only [Gh,centeredMetricGradient,coordinateGradient,map_zero,add_zero,hG₀]
  have hch : Tendsto xh atTop (𝓝 0) := by
    have hh := J.continuous.continuousAt.tendsto.comp (hconv.sub_const center)
    change Tendsto (fun k=>J (x k-center)) atTop (𝓝 (J (center-center))) at hh
    simpa only [sub_self,map_zero,he] using hh
  have hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (n:=n+1) xh k))).det ∧
        σ*Real.sqrt (mu/upper)≤leastGain (windowMatrix (unitWindow (windowStep (n:=n+1) xh k))) := by
    filter_upwards [hgain] with k hk
    have hh := metric_full_window_leastGain base hb (windowStep x k) hmu hu hσ hlower hupper hk
    have hw : (fun i : Fin (n+1)=>J (windowStep x k i))=windowStep xh k := by
      funext i
      have hdiff : windowStep x k i=(x (k+i.val+1)-center)-(x (k+i.val)-center) := by
        dsimp only [windowStep]
        abel_nf
      rw [hdiff,map_sub,he,he]
      rfl
    rwa [hw] at hh
  have hs : ∀ᶠ k in atTop,∀ i : Fin (n+1),windowStep xh k i≠0 := by
    filter_upwards [hind] with k hk i
    intro hz
    apply windowMatrix_step_ne_zero (unitWindow (windowStep xh k)) hk.1 i
    simp only [unitWindow,rescaleWindow,hz,smul_zero]
  have hphysical (j : ℕ) : center+J.symm (xh j)=x j := by
    rw [←he,J.symm_apply_apply]
    abel
  have hwindow (k : ℕ) (i : Fin (n+1)) : J (windowStep x k i)=windowStep xh k i := by
    dsimp only [windowStep]
    rw [show x (k+i.val+1)-x (k+i.val)=(x (k+i.val+1)-center)-(x (k+i.val)-center) by abel,
      map_sub,he,he]
  have hw : ∀ᶠ k in atTop,∀ i : Fin (n+1),
      ‖splitRemainder (xh (k+i.val)) (windowStep xh k i) (xh (k+n+1))
        (centeredSplit J center ss1FEuclideanSplit (fun j=>xh (k+j.val)) i)‖≤
      Real.sqrt (upper/mu)*‖xh (k+n+1)-xh (k+i.val+1)‖ := by
    filter_upwards [hs] with k hk i
    have hsp : windowStep x k i≠0 := by
      intro hz
      have hh:=hwindow k i
      rw [hz,map_zero] at hh
      exact hk i hh.symm
    have hp:=euclidean_split_metric_admissible base hb hmu hu hlower hupper
      (x (k+i.val)) (windowStep x k i) (x (k+n+1)) hsp
    have hl : centeredSplit J center ss1FEuclideanSplit (fun j=>xh (k+j.val)) i=
        innerSplit (x (k+i.val)) (windowStep x k i) (x (k+n+1)) := by
      simp only [centeredSplit,ss1FEuclideanSplit,hphysical,Fin.val_castSucc,Fin.val_succ,Fin.val_last,windowStep,Nat.add_assoc]
    rw [splitRemainder_centered_coordinate J center,he,hwindow,he] at hp
    have heq : x (k+i.val)+windowStep x k i=x (k+i.val+1) := by
      dsimp only [windowStep]
      abel
    rw [heq,show x (k+n+1)-x (k+i.val+1)=(x (k+n+1)-center)-(x (k+i.val+1)-center) by abel,
      map_sub,he,he] at hp
    rw [hl]
    exact hp
  have hr := (ss1FSequence_improved_rorder fh Gh Hh T₃ Sh hSc h₀ hnh hHh hH₀ hfh hGh hGz hT hLip
    (norm_nonneg (canonicalVariation (T₃ 0))) (canonicalVariation_unit_diagonal_bound (T₃ 0))
    (centeredSplit J center ss1FEuclideanSplit) sh hch (Real.sqrt_nonneg (upper/mu))
    (mul_pos hσ (Real.sqrt_pos.mpr (div_pos hmu hu))) hw hind).2
  change HasROrder (fun k=>‖J (x k-center)‖) _
  simpa only [he] using hr

end
end krylov.Convergence
