import krylov.Convergence.SlidingRFCRefinedAngle
import krylov.Convergence.RFCPathSourceAngle

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
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1200000

/-- The actual correction-to-accepted-step ratio in the article. -/
def rfcPathCorrectionRatio
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (x v : ℕ → EuclideanSpace ℝ (Fin (n+2))) (r : ℝ) (k : ℕ) : ℝ :=
  ‖rfcPathSearchCorrection f x v r k‖/‖x (k+n+2)-x (k+n+1)‖

/-- The complete original RFC correction-angle estimate is derived from
the actual function, actual probe and actual full observed model solve. -/
theorem rfcPath_refined_angle_bound
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r)) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
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
        ‖combine (unitWindow (windowStep (n:=n+1) (x) k)) c‖^2)
    (hne : ∀ᶠ k in atTop,x k≠0) :
      ∃ K : ℝ,0<K ∧∀ᶠ k in atTop,‖x (k+n+2)‖≤K*‖x (k+n+1)‖*
      ((rfcPathCorrectionRatio f x v r k+‖x k‖)*‖x k‖+‖x (k+1)‖+‖x (k+n+1)‖) := by
  let a := rfcFrameAnchor (n:=n) x
  let b := rfcFrameEndpoint (n:=n) x v
  let C := (σ^2/2)⁻¹+1
  have hC : 0≤C := by dsimp only [C];positivity
  let R := 1+|cP|
  have hR : 0≤R := by dsimp only [R];positivity
  let M := fun k=>inverseCongruence (windowMatrix (unitWindow (fun i=>b k i-a k i)))
    (ss1Model (unitWindow (fun i=>b k i-a k i))
      (unitWindowImages (fun i=>b k i-a k i) (fun i=>G (b k i)-G (a k i))))
  have h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈Metric.closedBall 0 r := by simpa using hr.le
  have hn : Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r∈𝓝 0 := Metric.closedBall_mem_nhds 0 hr
  have hsuper := (rfcPath_superlinear G H (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hn
    hH hH₀ hG hG₀ x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain).2
  have hc : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hv : Tendsto v atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun k=>cP*‖x (k+n+1)‖) (hprobe.mono fun _ h=>h.2)
    simpa only [norm_zero,mul_zero] using hc.norm.const_mul cP
  have hp : Tendsto (fun k=>x (k+n+1)+v k) atTop (𝓝 0) := by simpa only [add_zero] using hc.add hv
  have ha (i : Fin (n+2)) : Tendsto (fun k=>a k i) atTop (𝓝 0) := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [a,rfcFrameAnchor,Fin.snoc_last] using hc
    · simpa only [a,rfcFrameAnchor,Fin.snoc_castSucc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat j.val)
  have hb (i : Fin (n+2)) : Tendsto (fun k=>b k i) atTop (𝓝 0) := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [b,rfcFrameEndpoint,Fin.snoc_last] using hp
    · simpa only [b,rfcFrameEndpoint,Fin.snoc_castSucc,Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (j.val+1))
  have hm : ∀ᶠ k in atTop,(∀ i,a k i∈Metric.closedBall 0 r) ∧(∀ i,b k i∈Metric.closedBall 0 r) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hn).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hn)
  have hw := rfcPath_window_domains G H (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hn
    hH hH₀ hG hG₀ x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain
  have hframe : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (fun i=>b k i-a k i))).det ∧
      ‖(windowMatrix (unitWindow (fun i=>b k i-a k i)))⁻¹‖≤C := by
    filter_upwards [hw] with k hk
    simpa only [a,b,rfcFrame_steps] using ⟨hk.1,hk.2.1⟩
  have hmodel := source_moving_model_tendsto G H (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hH hH₀ hG
    a b ha hb hm hC hframe
  have hMd : ∀ᶠ k in atTop,IsUnit (M k).det :=
    (hmodel.1.eventually (Units.isOpen.mem_nhds isUnit_one)).mono fun _ h=>(Matrix.isUnit_iff_isUnit_det _).mp h
  have hMi : ∀ᶠ k in atTop,‖(M k)⁻¹‖≤2 := by
    have ht : Tendsto (fun k=>‖(M k)⁻¹‖) atTop (𝓝 1) := by simpa only [M,norm_one] using hmodel.2.1.norm
    exact (ht.eventually (gt_mem_nhds (by norm_num : (1:ℝ)<2))).mono fun _ h=>h.le
  have hage := superlinear_rfc_newer_radius x v hsuper (hprobe.mono fun _ h=>h.2)
  have hmono : ∀ᶠ k in atTop,‖x (k+1)‖≤‖x k‖ := by
    simpa only [norm_norm,one_mul] using hsuper.def (by norm_num : (0:ℝ)<1)
  have hcurage : ∀ᶠ k in atTop,‖x (k+n+1)‖≤‖x (k+1)‖ := by
    by_cases hnzero : n=0
    · subst n
      exact Filter.Eventually.of_forall fun _=>le_rfl
    · have hh := (superlinear_window_tail x hsuper (n-1)).def (by norm_num : (0:ℝ)<1)
      have hh' := (tendsto_add_atTop_nat 1).eventually hh
      simpa only [norm_norm,one_mul,show ∀ k : ℕ,k+1+(n-1)+1=k+n+1 from fun _=>by omega] using hh'
  have hhalf := (tendsto_add_atTop_nat (n+1)).eventually (hsuper.def (by norm_num : (0:ℝ)<1/2))
  have hnecur := (tendsto_add_atTop_nat (n+1)).eventually hne
  have hvec := rfcPath_correction_perpendicular f G H hr hLr hH hH₀ hf hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain
  obtain ⟨A,hA,hAvec⟩ := hvec.exists_pos
  let B := C^2*((n+2:ℕ):ℝ)*(L:ℝ)*((n+1:ℕ):ℝ)*R+(L:ℝ)/2
  have hB : 0≤B := by dsimp only [B];positivity
  let K := 4*(L:ℝ)*C^2+2*(L:ℝ)*C^2*A+2*B+1
  have hK : 0<K := by dsimp only [K];positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [hm,hw,hframe,hMd,hMi,hage,hmono,hcurage,hhalf,hnecur,hAvec.bound,hc.eventually hn]
    with k hmk hwk hfk hMdk hMik hagek hmonk hcagek hhalfk hnecurk hveck hcurmem
  let e := ‖x (k+n+1)‖
  let q := ‖x k‖
  let q₁ := ‖x (k+1)‖
  let rho := rfcPathCorrectionRatio f x v r k
  have he : 0<e := norm_pos_iff.mpr hnecurk
  have hrho : 0≤rho := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hnext : ‖x (k+n+2)‖≤e/2 := by
    simpa only [e,norm_norm,Nat.add_assoc,Nat.reduceAdd,one_div,div_eq_mul_inv,mul_comm,one_mul] using hhalfk
  have hstep : ‖x (k+n+2)-x (k+n+1)‖≤2*e := by
    apply (norm_sub_le _ _).trans
    change ‖x (k+n+2)‖+e≤2*e
    linarith only [hnext,he]
  have hstepne : ‖x (k+n+2)-x (k+n+1)‖≠0 := by
    intro hz
    have heq := sub_eq_zero.mp (norm_eq_zero.mp hz)
    rw [heq] at hnext
    change e≤e/2 at hnext
    linarith only [he,hnext]
  have hcsize : ‖rfcPathSearchCorrection f x v r k‖≤2*rho*e := by
    have hh := mul_le_mul_of_nonneg_left hstep hrho
    dsimp only [rho,rfcPathCorrectionRatio] at hh
    rw [div_mul_cancel₀ _ hstepne] at hh
    simpa only [rho,rfcPathCorrectionRatio,mul_assoc,mul_comm,mul_left_comm] using hh
  have hqs : ‖quadraticSearchPoint (x (k+n+1)) (v k)‖≤(2*rho+A*q)*e := by
    have ht := norm_sub_le
      (rfcPathSearchCorrection f x v r k+quadraticSearchPoint (x (k+n+1)) (v k))
      (rfcPathSearchCorrection f x v r k)
    rw [add_sub_cancel_left] at ht
    have hveck' : ‖rfcPathSearchCorrection f x v r k+quadraticSearchPoint (x (k+n+1)) (v k)‖≤A*q*e := by
      simpa only [q,e,norm_mul,norm_norm,mul_assoc] using hveck
    nlinarith only [ht,hveck',hcsize]
  have hsbound := ss1_oldest_perpendicular_source_bound G H (Metric.closedBall 0 r) (convex_closedBall _ _)
    h₀ hH hH₀ hG hG₀ (a k) (b k) (x (k+n+1)) hmk.1 hmk.2 hcurmem hC hfk.1 hfk.2 hMdk
  have hsteps := rfcFrame_steps (n:=n) x v k
  have himages := rfcFrame_images (n:=n) G x v k
  change (fun i=>b k i-a k i)=_ at hsteps
  change (fun i=>G (b k i)-G (a k i))=_ at himages
  dsimp only at hsbound
  rw [hsteps,himages,←hwk.2.2.2] at hsbound
  have hprobeStep : b k (Fin.last (n+1))-a k (Fin.last (n+1))=v k := by
    simp only [a,b,rfcFrameAnchor,rfcFrameEndpoint,Fin.snoc_last,add_sub_cancel_left]
  rw [hprobeStep] at hsbound
  have hfirst : ‖a k 0‖+‖b k 0‖≤2*q := by
    rw [show a k 0=x k from rfcFrame_anchor_zero x k,show b k 0=x (k+1) from rfcFrame_endpoint_zero x v k]
    change q+q₁≤2*q
    linarith only [hmonk]
  have hbudget : (L:ℝ)/2*(‖a k 0‖+‖b k 0‖)*C^2*‖quadraticSearchPoint (x (k+n+1)) (v k)‖+
      (C^2*((n+2:ℕ):ℝ)*((L:ℝ)/2)*newerWindowRadius (a k) (b k)+(L:ℝ)/2*e)*e≤
      (L:ℝ)*q*C^2*((2*rho+A*q)*e)+B*q₁*e := by
    have h₁ := mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfirst (show 0≤(L:ℝ)/2 by positivity)) (sq_nonneg C)) hqs
      (norm_nonneg _) (by positivity : 0≤(L:ℝ)/2*(2*q)*C^2)
    have h₂ := mul_le_mul_of_nonneg_left hagek (show 0≤C^2*((n+2:ℕ):ℝ)*((L:ℝ)/2) by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hcagek (show 0≤(L:ℝ)/2 by positivity)
    have hsum := mul_le_mul_of_nonneg_right (add_le_add h₂ h₃) he.le
    dsimp only [B,R,q₁] at hsum ⊢
    nlinarith only [h₁,hsum]
  have hsbound' : ‖x (k+n+2)‖≤2*((L:ℝ)*q*C^2*((2*rho+A*q)*e)+B*q₁*e) := by
    apply hsbound.trans
    have hi := hMik
    dsimp only [M] at hi
    rw [hsteps,himages] at hi
    exact (mul_le_mul_of_nonneg_left hbudget (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hi (by positivity))
  have hcoef₁ : 4*(L:ℝ)*C^2≤K := by
    dsimp only [K]
    linarith [show 0≤2*(L:ℝ)*C^2*A by positivity,hB]
  have hcoef₂ : 2*(L:ℝ)*C^2*A≤K := by
    dsimp only [K]
    linarith [show 0≤4*(L:ℝ)*C^2 by positivity,hB]
  have hcoef₃ : 2*B≤K := by
    dsimp only [K]
    linarith [show 0≤4*(L:ℝ)*C^2 by positivity,show 0≤2*(L:ℝ)*C^2*A by positivity]
  have h₁ := mul_le_mul_of_nonneg_right hcoef₁ (show 0≤rho*q*e by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hcoef₂ (show 0≤q^2*e by positivity)
  have h₃ := mul_le_mul_of_nonneg_right hcoef₃ (show 0≤q₁*e by positivity)
  have h₄ : 0≤K*e^2 := mul_nonneg hK.le (sq_nonneg _)
  apply hsbound'.trans
  change 2*((L:ℝ)*q*C^2*((2*rho+A*q)*e)+B*q₁*e)≤K*e*((rho+q)*q+q₁+e)
  nlinarith only [h₁,h₂,h₃,h₄]

end
end krylov.Convergence
