import krylov.Convergence.SlidingRFCRate
import krylov.Convergence.RFCPathSharpOldest

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
open Set Filter Topology Matrix Asymptotics krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- The actual convergent bounded-probe sliding RFC executor satisfies its
one-shorter-lag delayed error product, derived from the original source. -/
theorem rfcPath_product_recurrence
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (S : Set (EuclideanSpace ℝ (Fin (n+2)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
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
    ∃ K : ℝ,0<K ∧∀ᶠ k in atTop,
      ‖x (k+1)‖≤
        K*‖x (k-(n+1))‖*‖x k‖ := by
  let C := (σ^2/2)⁻¹+1
  let R := 1+|cP|
  have hC : 0≤C := by dsimp only [C]; positivity
  have hR : 1≤R := by dsimp only [R]; linarith [abs_nonneg cP]
  have hRpos : 0<R := by linarith
  have hsuper := (rfcPath_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain).2
  have hmono : ∀ᶠ k in atTop,‖x (k+1)‖≤‖x k‖ := by
    simpa only [one_mul,norm_norm] using hsuper.def (by norm_num : (0:ℝ)<1)
  have hW := rfcPath_window_domains G H S hS h₀ hnbhd hH hH₀ hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain
  have hv : Tendsto v atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun k=>cP*‖x (k+n+1)‖) (hprobe.mono fun _ h=>h.2)
    have hh : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
      simpa only [Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (n+1))
    simpa only [norm_zero,mul_zero] using hh.norm.const_mul cP
  have hp : ∀ᶠ k in atTop,x (k+n+1)+v k∈S := by
    have hh : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
      simpa only [Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (n+1))
    have ht : Tendsto (fun k=>x (k+n+1)+v k) atTop (𝓝 0) := by
      simpa only [add_zero] using hh.add hv
    exact ht.eventually hnbhd
  have hsmall : ∀ᶠ k in atTop,C^2*(((n+2:ℕ):ℝ)*((L:ℝ)*(R*‖x k‖)))≤1/2 := by
    have hh : Tendsto (fun k=>C^2*(((n+2:ℕ):ℝ)*((L:ℝ)*(R*‖x k‖)))) atTop (𝓝 0) := by
      simpa only [norm_zero,mul_zero] using
        (((hconv.norm.const_mul R).const_mul (L:ℝ)).const_mul ((n+2:ℕ):ℝ)).const_mul (C^2)
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).mono fun _ h=>h.le
  have hmem : ∀ᶠ k in atTop,x k∈S := hconv.eventually hnbhd
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hmono.and hmem)
  have htail (o : ℕ) (ho : N≤o) (j : ℕ) : ‖x (o+j)‖≤‖x o‖ := by
    induction j with
    | zero => simp only [Nat.add_zero]; exact le_rfl
    | succ j ih => exact ((hN (o+j) (by omega)).1).trans ih
  let K := 2*(L:ℝ)*R*(1+((n+2:ℕ):ℝ)*C^2)+1
  refine ⟨K,by dsimp only [K]; positivity,?_⟩
  have hraw : ∀ᶠ o in atTop,‖x (o+n+2)‖≤K*‖x o‖*‖x (o+n+1)‖ := by
    filter_upwards [eventually_ge_atTop N,hW,hprobe,hp,hsmall] with o ho hw hpr hpm hs
    let a : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) :=
      Fin.snoc (fun i : Fin (n+1)=>x (o+i.val)) (x (o+n+1))
    let b : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) :=
      Fin.snoc (fun i : Fin (n+1)=>x (o+i.val+1)) (x (o+n+1)+v o)
    have ha (i : Fin (n+2)) : a i∈S := by
      refine Fin.lastCases ?_ (fun j=>?_) i
      · simpa only [a,Fin.snoc_last] using (hN (o+n+1) (by omega)).2
      · simpa only [a,Fin.snoc_castSucc] using (hN (o+j.val) (by omega)).2
    have hb (i : Fin (n+2)) : b i∈S := by
      refine Fin.lastCases ?_ (fun j=>?_) i
      · simpa only [b,Fin.snoc_last] using hpm
      · simpa only [b,Fin.snoc_castSucc] using (hN (o+j.val+1) (by omega)).2
    have har (i : Fin (n+2)) : ‖a i‖≤R*‖x o‖ := by
      refine Fin.lastCases ?_ (fun j=>?_) i
      · simpa only [a,Fin.snoc_last,Nat.add_assoc] using
          (htail o ho (n+1)).trans (le_mul_of_one_le_left (norm_nonneg _) hR)
      · simpa only [a,Fin.snoc_castSucc] using
          (htail o ho j.val).trans (le_mul_of_one_le_left (norm_nonneg _) hR)
    have hbr (i : Fin (n+2)) : ‖b i‖≤R*‖x o‖ := by
      refine Fin.lastCases ?_ (fun j=>?_) i
      · simp only [b,Fin.snoc_last]
        have hvb : ‖v o‖≤|cP| * ‖x (o+n+1)‖ :=
          hpr.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
        have hh := (norm_add_le (x (o+n+1)) (v o)).trans (add_le_add le_rfl hvb)
        have ht := mul_le_mul_of_nonneg_left (htail o ho (n+1)) hRpos.le
        dsimp only [R] at ht
        simp only [←Nat.add_assoc] at ht
        change ‖x (o+n+1)+v o‖≤(1+|cP|)*‖x o‖
        nlinarith only [hh,ht]
      · simpa only [b,Fin.snoc_castSucc,Nat.add_assoc] using
          (htail o ho (j.val+1)).trans (le_mul_of_one_le_left (norm_nonneg _) hR)
    have hsteps : (fun i=>b i-a i)=Fin.snoc (windowStep (n:=n+1) x o) (v o) := by
      funext i
      refine Fin.lastCases ?_ (fun j=>?_) i
      · simp only [a,b,Fin.snoc_last,add_sub_cancel_left]
      · simp only [a,b,Fin.snoc_castSucc,windowStep]
    have himages : (fun i=>G (b i)-G (a i))=Fin.snoc (windowImage G x o)
        (G (x (o+n+1)+v o)-G (x (o+n+1))) := by
      funext i
      refine Fin.lastCases ?_ (fun j=>?_) i
      · simp only [a,b,Fin.snoc_last]
      · simp only [a,b,Fin.snoc_castSucc,windowImage]
    have hh := ss1_local_step_bound G H S hS h₀ hH hH₀ hG hG₀ a b (x (o+n+1))
      ha hb (hN (o+n+1) (by omega)).2 (mul_nonneg hRpos.le (norm_nonneg _)) hC
      har hbr ((htail o ho (n+1)).trans (le_mul_of_one_le_left (norm_nonneg _) hR))
      (by simpa only [hsteps] using hw.1) (by simpa only [hsteps] using hw.2.1) hs
    rw [hsteps,himages,←hw.2.2.2] at hh
    apply hh.trans
    have hcoef : 2*(L:ℝ)*R*(1+((n+2:ℕ):ℝ)*C^2)≤K := by dsimp only [K]; linarith
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (norm_nonneg (x o)))
      (norm_nonneg (x (o+n+1)))
    convert ht using 1
    ring
  obtain ⟨M,hM⟩ := eventually_atTop.mp hraw
  filter_upwards [eventually_ge_atTop (M+n+1)] with k hk
  let o := k-(n+1)
  have ho : M≤o := by dsimp only [o]; omega
  have hh := hM o ho
  simpa only [show o+n+1=k by dsimp only [o]; omega,show o+n+2=k+1 by dsimp only [o]; omega] using hh

/-- The literal sliding RFC iteration has R-order τ1(dimension), derived
from its actual bounded-probe function queries and old-window independence. -/
theorem rfcPath_rorder
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (S : Set (EuclideanSpace ℝ (Fin (n+2)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
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
    HasROrder (fun k=>‖x k‖) (oneGradientRoot (n+2)) := by
  have hrec := rfcPath_product_recurrence G H S hS h₀ hnbhd hH hH₀ hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain
  have hh := rorder_product_recurrence (fun k=>‖x k‖)
    (fun _=>norm_nonneg _) (by simpa only [norm_zero] using hconv.norm)
    (n+1) 0 (by omega) (by simpa only [Nat.sub_zero] using hrec)
  simpa only [oneGradientRoot,show n+2-1=n+1 by omega] using hh

end
end krylov.Convergence
