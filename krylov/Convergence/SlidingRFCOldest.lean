import krylov.Convergence.SlidingRFCWindows
import krylov.Convergence.OldestMovingSource
import krylov.Convergence.WindowSuperlinear

/-!
Article: main_krylov, thm:Ip, genuine RFC oldest-pair asymptotics.
Use: isolate the oldest actual stored diagonal on the real bounded-probe
executor, retaining the exact augmented-span distance before the geometric
comparison with the original stored-only distance. Source: actual current
probe observations, source-derived superlinearity and sharp moving secants.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- The real RFC execution has the exact oldest-diagonal coefficient;
all newer stored observations and its actual current probe are lower order. -/
theorem slidingRFCSequence_augmented_oldest_asymptotic
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (S : Set (EuclideanSpace ℝ (Fin (n+2)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (probe : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) → EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    {γ : ℝ} (hγ : 0<γ) (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)))
    (hconv : Tendsto (slidingRFCSequence G probe γ seed) atTop (𝓝 0))
    (hsolve : ∀ᶠ k in atTop,
      IsUnit (slidingRFCSolveMatrix (n:=n) G (slidingRFCSequence G probe γ seed) k).det)
    {cP : ℝ} (hprobe : ∀ᶠ k in atTop,
      slidingRFCProbe G probe (slidingRFCSequence G probe γ seed) k≠0 ∧
      ‖slidingRFCProbe G probe (slidingRFCSequence G probe γ seed) k‖≤
        cP*‖slidingRFCSequence G probe γ seed (k+n+1)‖)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1)
    (hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤
        ‖combine (unitWindow (windowStep (n:=n+1) (slidingRFCSequence G probe γ seed) k)) c‖^2) :
    let x := slidingRFCSequence G probe γ seed
    let v := slidingRFCProbe G probe x
    let V := fun k=>windowMatrix (unitWindow (Fin.snoc (windowStep (n:=n+1) x k) (v k)))
    ∃ m r : ℕ → ℝ,Tendsto m atTop (𝓝 1) ∧r=o[atTop](fun k=>‖x k‖) ∧∀ᶠ k in atTop,
      ‖x (k+n+2)‖≤m k*
        (((L:ℝ)/2*(‖x k‖+‖x (k+1)‖)) /
          (Metric.infDist (euclideanColumn (V k) 0) (newerColumnSpan (V k):Set _))^2+r k)*‖x (k+n+1)‖ := by
  dsimp only
  let x := slidingRFCSequence G probe γ seed
  let v := slidingRFCProbe G probe x
  let a : ℕ → Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) :=
    fun k=>Fin.snoc (fun i : Fin (n+1)=>x (k+i.val)) (x (k+n+1))
  let b : ℕ → Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) :=
    fun k=>Fin.snoc (fun i : Fin (n+1)=>x (k+i.val+1)) (x (k+n+1)+v k)
  have hsup := (slidingRFCSequence_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀
    probe hγ seed hconv hsolve hprobe hσ hσ₁ hgain).2
  have hcurrent : (fun k=>‖x (k+n+1)‖)=o[atTop](fun k=>‖x k‖) := superlinear_window_tail x hsup n
  have hvo : v=O[atTop](fun k=>‖x (k+n+1)‖) := by
    apply IsBigO.of_bound |cP|
    filter_upwards [hprobe] with k hk
    simpa only [norm_norm] using hk.2.trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hvl : v=o[atTop](fun k=>‖x k‖) := hvo.trans_isLittleO hcurrent
  have hplus : (fun k=>‖x (k+n+1)+v k‖)=o[atTop](fun k=>‖x k‖) := by
    have hh := hcurrent.add hvl.norm_left
    apply IsLittleO.of_bound
    intro ε hε
    filter_upwards [hh.def hε] with k hk
    simp only [norm_norm]
    exact (norm_add_le _ _).trans (by simpa only [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),norm_norm] using hk)
  have hc : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hv : Tendsto v atTop (𝓝 0) := hvl.trans_tendsto (by simpa only [norm_zero] using hconv.norm)
  have hp : Tendsto (fun k=>x (k+n+1)+v k) atTop (𝓝 0) := by simpa only [add_zero] using hc.add hv
  have ha (i : Fin (n+2)) : Tendsto (fun k=>a k i) atTop (𝓝 0) := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [a,Fin.snoc_last] using hc
    · simpa only [a,Fin.snoc_castSucc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat j.val)
  have hb (i : Fin (n+2)) : Tendsto (fun k=>b k i) atTop (𝓝 0) := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [b,Fin.snoc_last] using hp
    · simpa only [b,Fin.snoc_castSucc,Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (j.val+1))
  have hage (j : Fin (n+2)) : j≠0 →
      (fun k=>‖a k j‖+‖b k j‖)=o[atTop](fun k=>‖x k‖) := by
    refine Fin.lastCases ?_ (fun i=>?_) j
    · intro _
      simpa only [a,b,Fin.snoc_last] using hcurrent.add hplus
    · intro hi
      have hip : 0 < i.val := by
        by_contra! hz
        apply hi
        exact Fin.ext (by simp only [Fin.val_castSucc,Fin.val_zero]; omega)
      have hai : (fun k=>‖x (k+i.val)‖)=o[atTop](fun k=>‖x k‖) := by
        simpa only [show i.val-1+1=i.val by omega,Nat.add_assoc] using superlinear_window_tail x hsup (i.val-1)
      simpa only [a,b,Fin.snoc_castSucc] using hai.add (superlinear_window_tail x hsup i.val)
  have hnew : (fun k=>newerWindowRadius (a k) (b k))=o[atTop](fun k=>‖x k‖) := by
    have hh := IsLittleO.sum (s:=Finset.univ) (fun i _=>hage i.succ (Fin.succ_ne_zero i))
    apply hh.congr_left
    intro k
    simp only [newerWindowRadius,Finset.sum_apply]
  have hs (k : ℕ) : (fun i=>b k i-a k i)=Fin.snoc (windowStep (n:=n+1) x k) (v k) := by
    funext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [a,b,Fin.snoc_last,add_sub_cancel_left]
    · simp only [a,b,Fin.snoc_castSucc,windowStep]
  have hy (k : ℕ) : (fun i=>G (b k i)-G (a k i))=Fin.snoc (windowImage G x k)
      (G (x (k+n+1)+v k)-G (x (k+n+1))) := by
    funext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [a,b,Fin.snoc_last]
    · simp only [a,b,Fin.snoc_castSucc,windowImage]
  have hw := slidingRFCSequence_window_domains G H S hS h₀ hnbhd hH hH₀ hG hG₀
    probe hγ seed hconv hsolve hprobe hσ hσ₁ hgain
  have hframe : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (fun i=>b k i-a k i))).det ∧
      ‖(windowMatrix (unitWindow (fun i=>b k i-a k i)))⁻¹‖≤(σ^2/2)⁻¹+1 := by
    filter_upwards [hw] with k hk
    simpa only [hs] using ⟨hk.1,hk.2.1⟩
  obtain ⟨m,r,hm,hr,hbound⟩ := moving_source_oldest_asymptotic G H S hS h₀ hnbhd hH hH₀ hG hG₀
    a b (fun k=>x (k+n+1)) (fun k=>‖x k‖) ha hb hc (by positivity : 0≤(σ^2/2)⁻¹+1) hframe hnew hcurrent
  refine ⟨m,r,hm,hr,?_⟩
  filter_upwards [hbound,hw] with k hk hdom
  dsimp only at hk
  rw [hs,hy,←hdom.2.2.2] at hk
  have ha0 : a k 0=x k := by
    change a k (Fin.castSucc (0:Fin (n+1)))=x k
    simp only [a,Fin.snoc_castSucc,Fin.val_zero,Nat.add_zero]
  have hb0 : b k 0=x (k+1) := by
    change b k (Fin.castSucc (0:Fin (n+1)))=x (k+1)
    simp only [b,Fin.snoc_castSucc,Fin.val_zero,Nat.add_zero]
  simpa only [ha0,hb0] using hk

end
end krylov.Convergence
