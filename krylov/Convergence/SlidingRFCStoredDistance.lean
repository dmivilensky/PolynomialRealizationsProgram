import krylov.Convergence.SlidingRFCOldest
import krylov.Convergence.OldestProbeDistance

/-!
Article: main_krylov, thm:Ip, the original RFC stored-only Delta.
Use: remove the actually evaluated current probe from the leading oldest
conditioning constant. Source: real secants, observed conjugacy, original
stored independence and the exact orthogonal distance augmentation formula.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- The article's original oldest-column distance uses only retained
stored steps, with no current probe in its newer span. -/
def slidingRFCStoredOldestDistance
    (x : ℕ → EuclideanSpace ℝ (Fin (n+2))) (k : ℕ) : ℝ :=
  let s := unitWindow (windowStep (n:=n+1) x k)
  Metric.infDist (s 0) (Submodule.span ℝ (Set.range (fun i : Fin n=>s i.succ)):Set _)

/-- The exact full observed model uses this genuinely augmented distance. -/
def slidingRFCAugmentedOldestDistance
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (probe : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) → EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin (n+2))) (k : ℕ) : ℝ :=
  let V := windowMatrix (unitWindow (Fin.snoc (windowStep (n:=n+1) x k) (slidingRFCProbe G probe x k)))
  Metric.infDist (euclideanColumn V 0) (newerColumnSpan V:Set _)

/-- The actual full-model amplification is bounded by the original
stored-only Delta amplification times a genuine factor tending to one. -/
theorem slidingRFCSequence_stored_distance_comparison
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (S : Set (EuclideanSpace ℝ (Fin (n+2)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (_hG₀ : G 0=0)
    (probe : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) → EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    {γ : ℝ} (_hγ : 0<γ) (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)))
    (hconv : Tendsto (slidingRFCSequence G probe γ seed) atTop (𝓝 0))
    (hsolve : ∀ᶠ k in atTop,
      IsUnit (slidingRFCSolveMatrix (n:=n) G (slidingRFCSequence G probe γ seed) k).det)
    {cP : ℝ} (hprobe : ∀ᶠ k in atTop,
      slidingRFCProbe G probe (slidingRFCSequence G probe γ seed) k≠0 ∧
      ‖slidingRFCProbe G probe (slidingRFCSequence G probe γ seed) k‖≤
        cP*‖slidingRFCSequence G probe γ seed (k+n+1)‖)
    {σ : ℝ} (hσ : 0<σ) (_hσ₁ : σ≤1)
    (hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤
        ‖combine (unitWindow (windowStep (n:=n+1) (slidingRFCSequence G probe γ seed) k)) c‖^2) :
    let x := slidingRFCSequence G probe γ seed
    (∀ᶠ k in atTop,σ≤slidingRFCStoredOldestDistance x k) ∧
    ∃ F : ℕ → ℝ,Tendsto F atTop (𝓝 1) ∧∀ᶠ k in atTop,
      0<F k ∧((slidingRFCAugmentedOldestDistance G probe x k)^2)⁻¹≤
        F k*((slidingRFCStoredOldestDistance x k)^2)⁻¹ := by
  dsimp only
  let x := slidingRFCSequence G probe γ seed
  let v := slidingRFCProbe G probe x
  let s := fun k=>unitWindow (windowStep (n:=n+1) x k)
  let d := fun k=>(‖v k‖⁻¹:ℝ) • v k
  let a := fun k (i : Fin (n+1))=>x (k+i.val)
  let b := fun k (i : Fin (n+1))=>x (k+i.val+1)
  let ε := fun k=>(L:ℝ)/2*sourceWindowRadius (a k) (b k)
  have ha (i : Fin (n+1)) : Tendsto (fun k=>a k i) atTop (𝓝 0) := hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+1)) : Tendsto (fun k=>b k i) atTop (𝓝 0) := by
    simpa only [b,Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hm : ∀ᶠ k in atTop,(∀ i,a k i∈S) ∧(∀ i,b k i∈S) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)
  have hε (k) : 0≤ε k := mul_nonneg (by positivity) (sourceWindowRadius_nonneg _ _)
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have ht := tendsto_finsetSum Finset.univ (fun i _=>(ha i).norm.add (hb i).norm)
    have hr : Tendsto (fun k=>sourceWindowRadius (a k) (b k)) atTop (𝓝 0) := by
      simpa only [sourceWindowRadius,norm_zero,add_zero,Finset.sum_const_zero] using ht
    simpa only [ε,mul_zero] using hr.const_mul ((L:ℝ)/2)
  have hs : ∀ᶠ k in atTop,∀ i : Fin (n+1),windowStep x k i≠0 := by
    filter_upwards [hsolve] with k hk i
    exact observed_solve_step_ne_zero _ _ hk i
  have hp : ∀ᶠ k in atTop,∀ i : Fin (n+1),|inner ℝ (s k i) (d k)|≤ε k := by
    filter_upwards [hm,hs,hsolve,hprobe] with k hk hsk hsol hpr i
    have he := secant_image_endpoint_bound G H S hS h₀ hH hG _ _ (hk.1 i) (hk.2 i)
    rw [hH₀,ContinuousLinearMap.id_apply] at he
    have herror : ‖windowImage G x k i-windowStep x k i‖≤ε k*‖windowStep x k i‖ := by
      apply he.trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.single_le_sum (fun j _=>add_nonneg (norm_nonneg (a k j)) (norm_nonneg (b k j))) (Finset.mem_univ i)
    exact observed_conjugacy_unit_pairing _ _ _ (hsk i) hpr.1 herror (slidingRFCProbe_conjugate G probe x k hsol i)
  have hsn : ∀ᶠ k in atTop,‖s k 0‖=1 := hs.mono fun k hk=>unitWindow_norm _ hk 0
  have hdn : ∀ᶠ k in atTop,‖d k‖=1 := hprobe.mono fun k hk=>norm_smul_inv_norm hk.1
  have hgeom := oldest_probe_distance_asymptotic s d ε hσ hε hεt hgain hp hsn hdn
  dsimp only at hgeom
  let theta := fun k=>inner ℝ
    (s k 0-(Submodule.span ℝ (Set.range (fun i : Fin n=>s k i.succ))).starProjection (s k 0))
    ((‖d k-(Submodule.span ℝ (Set.range (fun i : Fin n=>s k i.succ))).starProjection (d k)‖⁻¹:ℝ) •
      (d k-(Submodule.span ℝ (Set.range (fun i : Fin n=>s k i.succ))).starProjection (d k)))
  have hlow : ∀ᶠ k in atTop,σ≤slidingRFCStoredOldestDistance x k :=
    hgain.mono fun k hk=>oldest_distance_ge_gain (s k) hσ.le hk
  refine ⟨hlow,?_⟩
  apply distance_inverse_sq_comparison (slidingRFCStoredOldestDistance x)
    (slidingRFCAugmentedOldestDistance G probe x) theta hσ hlow hgeom.1
  filter_upwards [hgeom.2] with k hk
  have he : unitWindow (Fin.snoc (windowStep (n:=n+1) x k) (v k))=Fin.snoc (s k) (d k) := unitWindow_snoc _ _
  have hzero : euclideanColumn (windowMatrix (Fin.snoc (s k) (d k))) 0=s k 0 := by
    change (Fin.snoc (s k) (d k) : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) (Fin.castSucc (0:Fin (n+1)))=_
    rw [Fin.snoc_castSucc]
  simpa only [slidingRFCAugmentedOldestDistance,slidingRFCStoredOldestDistance,he,hzero,
    newerColumnSpan_snoc_window,s,d,v,theta] using hk

end
end krylov.Convergence
