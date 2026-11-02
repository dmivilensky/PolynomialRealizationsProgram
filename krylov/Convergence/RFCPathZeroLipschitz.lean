import krylov.Convergence.SlidingRFCZeroLipschitz
import krylov.Convergence.RFCPathStoredDistance

/-!
Article: main_krylov, thm:Ip, invariant actual observed RFC path.
Use: transport the original physical execution through genuine metric
coordinates. Inputs here are exact observed execution identities; physical
wrappers derive them from the literal rule. No recurrence, gate success,
model estimate or output rate is an input. Source: the existing source
FTC, actual full-model inverse and oldest-pair geometric arguments.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- The genuine bounded-probe RFC executor reaches the true stationary
point exactly in its eventual full-model phase when LH=0. -/
theorem rfcPath_zero_lipschitz
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (S : Set (EuclideanSpace ℝ (Fin (n+2)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈S) (hnbhd : S∈𝓝 0)
    (hH : LipschitzOnWith 0 H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (x v : ℕ → EuclideanSpace ℝ (Fin (n+2)))
    {γ : ℝ} (hγ : 0<γ)
    (hquery : ∀ k,x (k+n+2)=evaluatedRFCPoint G (windowStep (n:=n+1) x k)
      (windowImage G x k) (x (k+n+1)) (v k) γ)
    (hconv : Tendsto x atTop (𝓝 0))
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingRFCSolveMatrix (n:=n) G x k).det)
    (hconj : ∀ᶠ k in atTop,∀ i : Fin (n+1),inner ℝ (windowImage G x k i) (v k)=0)
    {cP : ℝ} (hprobe : ∀ᶠ k in atTop,
      v k≠0 ∧
      ‖v k‖≤
        cP*‖x (k+n+1)‖)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1)
    (hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤
        ‖combine (unitWindow (windowStep (n:=n+1) (x) k)) c‖^2) :
    ∀ᶠ k in atTop,x (k+n+2)=0 := by
  let a : ℕ → Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) :=
    fun k=>Fin.snoc (fun i : Fin (n+1)=>x (k+i.val)) (x (k+n+1))
  let b : ℕ → Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) :=
    fun k=>Fin.snoc (fun i : Fin (n+1)=>x (k+i.val+1)) (x (k+n+1)+v k)
  have hc : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hv : Tendsto v atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun k=>cP*‖x (k+n+1)‖) (hprobe.mono fun _ h=>h.2)
    simpa only [norm_zero,mul_zero] using hc.norm.const_mul cP
  have hp : Tendsto (fun k=>x (k+n+1)+v k) atTop (𝓝 0) := by simpa only [add_zero] using hc.add hv
  have ha (i : Fin (n+2)) : Tendsto (fun k=>a k i) atTop (𝓝 0) := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [a,Fin.snoc_last] using hc
    · simpa only [a,Fin.snoc_castSucc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat j.val)
  have hb (i : Fin (n+2)) : Tendsto (fun k=>b k i) atTop (𝓝 0) := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [b,Fin.snoc_last] using hp
    · simpa only [b,Fin.snoc_castSucc,Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (j.val+1))
  have hm : ∀ᶠ k in atTop,(∀ i,a k i∈S) ∧(∀ i,b k i∈S) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)
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
  have hw := rfcPath_window_domains G H S hS h₀ hnbhd hH hH₀ hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain
  filter_upwards [hm,hw,hc.eventually hnbhd] with k hmk hwk hck
  have hh := ss1Point_eq_zero_of_zero_lipschitz G H S hS h₀ hH hH₀ hG hG₀ (a k) (b k)
    (x (k+n+1)) hmk.1 hmk.2 hck (by simpa only [hs] using hwk.1)
  rw [hs,hy,←hwk.2.2.2] at hh
  exact hh

end
end krylov.Convergence
