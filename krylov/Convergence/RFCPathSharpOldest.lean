import krylov.Convergence.SlidingRFCSharpOldest
import krylov.Convergence.RFCPathZeroLipschitz

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
open Matrix Set Filter Topology Asymptotics krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- The actual RFC oldest-diagonal coefficient uses precisely the original
stored-only Delta; every newer and current-probe error is little-o of its
actual oldest error, with a genuine remaining factor tending to one. -/
theorem rfcPath_stored_oldest_asymptotic
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
      ∃ m r : ℕ → ℝ,Tendsto m atTop (𝓝 1) ∧r=o[atTop](fun k=>‖x k‖) ∧∀ᶠ k in atTop,
      ‖x (k+n+2)‖≤m k*
        (((L:ℝ)/2*(‖x k‖+‖x (k+1)‖))/(slidingRFCStoredOldestDistance x k)^2+r k)*‖x (k+n+1)‖ := by
  obtain ⟨m,r,hm,hr,hb⟩ := rfcPath_augmented_oldest_asymptotic G H S hS h₀ hnbhd hH hH₀ hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain
  obtain ⟨F,hF,hFb⟩ := (rfcPath_stored_distance_comparison G H S hS h₀ hnbhd hH hH₀ hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain).2
  have hFinv : (fun k=>(F k)⁻¹)=O[atTop](fun _=>(1:ℝ)) :=
    (hF.inv₀ one_ne_zero).isBigO_one ℝ
  have hrr : (fun k=>r k*(F k)⁻¹)=o[atTop](fun k=>‖x k‖) := by
    simpa only [mul_one] using hr.mul_isBigO hFinv
  refine ⟨fun k=>m k*F k,fun k=>r k*(F k)⁻¹,by simpa only [mul_one] using hm.mul hF,hrr,?_⟩
  filter_upwards [hb,hFb,hm.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1))] with k hk hFk hmk
  have hlead := mul_le_mul_of_nonneg_left hFk.2
    (show 0≤(L:ℝ)/2*(‖x k‖+‖x (k+1)‖) by positivity)
  have hlead' : ((L:ℝ)/2*(‖x k‖+‖x (k+1)‖))/(rfcPathAugmentedOldestDistance x v k)^2≤
      F k*(((L:ℝ)/2*(‖x k‖+‖x (k+1)‖))/(slidingRFCStoredOldestDistance x k)^2) := by
    simpa only [div_eq_mul_inv,mul_left_comm] using hlead
  have hh := hk.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (add_le_add hlead' le_rfl) hmk.le) (norm_nonneg (x (k+n+1))))
  convert hh using 1
  field_simp [hFk.1.ne']

/-- The article's literal multiplicative oldest-distance bound for the
actual bounded-probe RFC executor, with every newer observation absorbed
into one genuine factor tending to one. -/
theorem rfcPath_printed_oldest_bound_of_pos
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
        ‖combine (unitWindow (windowStep (n:=n+1) (x) k)) c‖^2)
    (hL : 0<(L:ℝ)) :
      ∃ theta : ℕ → ℝ,Tendsto theta atTop (𝓝 0) ∧∀ᶠ k in atTop,
      ‖x (k+n+2)‖≤(1+theta k)*((L:ℝ)/(2*(slidingRFCStoredOldestDistance x k)^2))*
        ‖x (k+n+1)‖*‖x k‖ := by
  obtain ⟨m,r,hm,hr,hb⟩ := rfcPath_stored_oldest_asymptotic G H S hS h₀ hnbhd hH hH₀ hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain
  have hlow := (rfcPath_stored_distance_comparison G H S hS h₀ hnbhd hH hH₀ hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain).1
  have hupp := slidingRFC_stored_distance_le_one G x hsolve
  have hsup := (rfcPath_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain).2
  obtain ⟨theta,htheta,he⟩ := oldest_multiplicative_factor (fun k=>‖x k‖) (fun k=>‖x (k+1)‖)
    (slidingRFCStoredOldestDistance x) m r hσ hL (fun _=>norm_nonneg _) (hlow.and hupp) hm hsup.norm_left hr
  refine ⟨theta,htheta,?_⟩
  filter_upwards [hb,he] with k hk hek
  rw [hek] at hk
  convert hk using 1
  ring

/-- The literal printed RFC oldest-distance coefficient, including the
exact zero-Lipschitz quadratic branch and intermittent zero errors. -/
theorem rfcPath_printed_oldest_bound
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
      ∃ theta : ℕ → ℝ,Tendsto theta atTop (𝓝 0) ∧∀ᶠ k in atTop,
      ‖x (k+n+2)‖≤(1+theta k)*((L:ℝ)/(2*(slidingRFCStoredOldestDistance x k)^2))*
        ‖x (k+n+1)‖*‖x k‖ := by
  by_cases hL : L=0
  · subst L
    have hz := rfcPath_zero_lipschitz G H S hS h₀ hnbhd hH hH₀ hG hG₀
      x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain
    refine ⟨fun _=>0,tendsto_const_nhds,?_⟩
    filter_upwards [hz] with k hk
    simp only [hk,norm_zero,NNReal.coe_zero,zero_div,mul_zero,zero_mul,le_refl]
  · exact rfcPath_printed_oldest_bound_of_pos G H S hS h₀ hnbhd hH hH₀ hG hG₀
      x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hL))

end
end krylov.Convergence
