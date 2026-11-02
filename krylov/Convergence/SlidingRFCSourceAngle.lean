import krylov.Convergence.SlidingRFCAngle
import krylov.Convergence.WindowSuperlinear

/-!
Article: main_krylov, thm:Ip, actual RFC correction-angle leading vector.
Use: combine the genuinely derived corrected endpoint recurrence with an
actual scalar-objective search. Source: real local exact searches and the
bounded-probe RFC source; no angular or output estimate is assumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Actual RFC searched correction after its real scalar chord search. -/
def slidingRFCSearchCorrection
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (probe : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) → EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (r γ : ℝ) (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) (k : ℕ) : EuclideanSpace ℝ (Fin (n+2)) :=
  let x := slidingRFCSequence G probe γ seed
  x (k+n+2)-localExactPoint f (x (k+n+1)) (slidingRFCProbe G probe x k) r

/-- The real correction is the negative perpendicular error plus the
printed O(e_oldest*e_current), on the actual function execution. -/
theorem slidingRFCSequence_correction_perpendicular
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r)) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
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
    (fun k=>slidingRFCSearchCorrection f G probe r γ seed k+
      quadraticSearchPoint (x (k+n+1)) (slidingRFCProbe G probe x k))=O[atTop]
      (fun k=>‖x k‖*‖x (k+n+1)‖) := by
  dsimp only
  let x := slidingRFCSequence G probe γ seed
  let v := slidingRFCProbe G probe x
  have h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈Metric.closedBall 0 r := by simpa using hr.le
  have hn : Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r∈𝓝 0 := Metric.closedBall_mem_nhds 0 hr
  obtain ⟨K,hK,hrec⟩ := slidingRFCSequence_product_recurrence G H (Metric.closedBall 0 r)
    (convex_closedBall _ _) h₀ hn hH hH₀ hG hG₀ probe hγ seed hconv hsolve hprobe hσ hσ₁ hgain
  have hraw : ∀ᶠ k in atTop,‖x (k+n+2)‖≤K*‖x k‖*‖x (k+n+1)‖ := by
    have hh := (tendsto_add_atTop_nat (n+1)).eventually hrec
    simpa only [show ∀ k : ℕ,k+(n+1)-(n+1)=k from fun _=>Nat.add_sub_cancel _ _,Nat.add_assoc] using hh
  have hsuper := (slidingRFCSequence_superlinear G H (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hn
    hH hH₀ hG hG₀ probe hγ seed hconv hsolve hprobe hσ hσ₁ hgain).2
  have hage := (superlinear_window_tail x hsuper n).def (by norm_num : (0:ℝ)<1)
  have hcurrent : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hsmall : ∀ᶠ k in atTop,‖x (k+n+1)‖<r/2 := by
    have hh : Tendsto (fun k=>‖x (k+n+1)‖) atTop (𝓝 0) := by simpa only [norm_zero] using hcurrent.norm
    exact hh.eventually (gt_mem_nhds (half_pos hr))
  apply IsBigO.of_bound (K+3*(L:ℝ)/2)
  filter_upwards [hraw,hage,hsmall] with k hk ha hs
  have hm : x (k+n+1)∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (hs.le.trans (by linarith : r/2≤r))
  have hsearch := localExactPoint_spec f (x (k+n+1)) (v k) r
    (existsUnique_local_chord_minimum f G H hr hH₀ hLr hH hf hG _ _ hm)
  have hy := local_exact_search_quadratic_error f G H hr hG₀ hH₀ hLr hH hf hG _ _ _ hs hsearch
  have ha' : ‖x (k+n+1)‖≤‖x k‖ := by simpa only [norm_norm,one_mul] using ha
  have hy' : ‖localExactPoint f (x (k+n+1)) (v k) r-quadraticSearchPoint (x (k+n+1)) (v k)‖≤
      (3*(L:ℝ)/2)*‖x k‖*‖x (k+n+1)‖ := by
    apply hy.trans
    have hh := mul_le_mul_of_nonneg_right ha' (show 0≤3*(L:ℝ)/2*‖x (k+n+1)‖ by positivity)
    nlinarith only [hh]
  have hh := correction_perpendicular_error _ _ _ _ hk hy'
  simpa only [slidingRFCSearchCorrection,norm_mul,norm_norm,x,v,mul_assoc] using hh

/-- The literal actual correction-to-step ratio is the ordinary sine
angle plus O(e_oldest), with no angular regularity hypothesis. -/
theorem slidingRFCSequence_correction_angle
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r)) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
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
        ‖combine (unitWindow (windowStep (n:=n+1) (slidingRFCSequence G probe γ seed) k)) c‖^2)
    (hne : ∀ᶠ k in atTop,slidingRFCSequence G probe γ seed k≠0) :
    let x := slidingRFCSequence G probe γ seed
    (fun k=>‖slidingRFCSearchCorrection f G probe r γ seed k‖/‖x (k+n+2)-x (k+n+1)‖-
      Real.sin (InnerProductGeometry.angle (x (k+n+1)) (slidingRFCProbe G probe x k)))=O[atTop](fun k=>‖x k‖) := by
  dsimp only
  let x := slidingRFCSequence G probe γ seed
  let v := slidingRFCProbe G probe x
  let c := slidingRFCSearchCorrection f G probe r γ seed
  have hvect := slidingRFCSequence_correction_perpendicular f G H hr hLr hH hH₀ hf hG hG₀
    probe hγ seed hconv hsolve hprobe hσ hσ₁ hgain
  obtain ⟨C,hC,hCv⟩ := hvect.exists_pos
  have h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈Metric.closedBall 0 r := by simpa using hr.le
  have hn : Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r∈𝓝 0 := Metric.closedBall_mem_nhds 0 hr
  obtain ⟨K,hK,hrec⟩ := slidingRFCSequence_product_recurrence G H (Metric.closedBall 0 r)
    (convex_closedBall _ _) h₀ hn hH hH₀ hG hG₀ probe hγ seed hconv hsolve hprobe hσ hσ₁ hgain
  have hraw : ∀ᶠ k in atTop,‖x (k+n+2)‖≤K*‖x k‖*‖x (k+n+1)‖ := by
    have hh := (tendsto_add_atTop_nat (n+1)).eventually hrec
    simpa only [show ∀ k : ℕ,k+(n+1)-(n+1)=k from fun _=>Nat.add_sub_cancel _ _,Nat.add_assoc] using hh
  have hsmall : ∀ᶠ k in atTop,K*‖x k‖≤1/2 := by
    have hh : Tendsto (fun k=>K*‖x k‖) atTop (𝓝 0) := by simpa only [norm_zero,mul_zero] using hconv.norm.const_mul K
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).mono fun _ h=>h.le
  have hcurrentne := (tendsto_add_atTop_nat (n+1)).eventually hne
  apply IsBigO.of_bound (2*(C+K))
  filter_upwards [hCv.bound,hraw,hsmall,hcurrentne,hprobe] with k hcv hk hs hnk hpk
  have hX : 0<‖x (k+n+1)‖ := norm_pos_iff.mpr hnk
  have hstep : |‖x (k+n+2)-x (k+n+1)‖-‖x (k+n+1)‖|≤K*‖x k‖*‖x (k+n+1)‖ := by
    have hh := abs_norm_sub_norm_le (x (k+n+2)-x (k+n+1)) (-x (k+n+1))
    have hh' : |‖x (k+n+2)-x (k+n+1)‖-‖x (k+n+1)‖|≤‖x (k+n+2)‖ := by
      simpa only [norm_neg,sub_neg_eq_add,sub_add_cancel] using hh
    exact hh'.trans hk
  have hlen : ‖x (k+n+1)‖/2≤‖x (k+n+2)-x (k+n+1)‖ := by
    have hh := mul_le_mul_of_nonneg_right hs hX.le
    have hb := (abs_le.mp hstep).1
    nlinarith only [hh,hb]
  have hnorm : |‖c k‖-‖quadraticSearchPoint (x (k+n+1)) (v k)‖|≤C*‖x k‖*‖x (k+n+1)‖ := by
    have hh := abs_norm_sub_norm_le (c k) (-quadraticSearchPoint (x (k+n+1)) (v k))
    have hcv' : ‖c k+quadraticSearchPoint (x (k+n+1)) (v k)‖≤C*‖x k‖*‖x (k+n+1)‖ := by
      simpa only [c,norm_mul,norm_norm,mul_assoc] using hcv
    have hh' : |‖c k‖-‖quadraticSearchPoint (x (k+n+1)) (v k)‖|≤
        ‖c k+quadraticSearchPoint (x (k+n+1)) (v k)‖ := by
      simpa only [norm_neg,sub_neg_eq_add] using hh
    exact hh'.trans hcv'
  have hh := correction_ratio_error hX (norm_nonneg _) (quadraticSearchPoint_norm_le _ _) hC.le hK.le
    (norm_nonneg (x k)) hlen hnorm hstep
  have hsine := quadraticSearchPoint_norm_div_eq_sin (x (k+n+1)) (v k)
    (by simpa only [x,Nat.add_assoc] using hnk) hpk.1
  rw [hsine] at hh
  simpa only [Real.norm_eq_abs,abs_norm,c] using hh

/-- The actual searched correction in the angular theorem is precisely
the original observed full-model correction using its real line scalar
and the predicted endpoint gradient from the genuine evaluated probe. -/
theorem slidingRFCSequence_observed_search_correction
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r)) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
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
    ∀ᶠ k in atTop,∃ alpha : ℝ,
      localExactPoint f (x (k+n+1)) (v k) r=x (k+n+1)+alpha • v k ∧
      slidingRFCSearchCorrection f G probe r γ seed k=
        combine (Fin.snoc (windowStep (n:=n+1) x k) (v k))
          (modelCoefficients (Fin.snoc (windowStep (n:=n+1) x k) (v k))
            (ss1Model (Fin.snoc (windowStep (n:=n+1) x k) (v k))
              (Fin.snoc (windowImage G x k) (G (x (k+n+1)+v k)-G (x (k+n+1)))))
            (G (x (k+n+1))+alpha • (G (x (k+n+1)+v k)-G (x (k+n+1))))) := by
  dsimp only
  let x := slidingRFCSequence G probe γ seed
  let v := slidingRFCProbe G probe x
  have h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈Metric.closedBall 0 r := by simpa using hr.le
  have hn : Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r∈𝓝 0 := Metric.closedBall_mem_nhds 0 hr
  have hc : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hw := slidingRFCSequence_window_domains G H (Metric.closedBall 0 r) (convex_closedBall _ _) h₀ hn
    hH hH₀ hG hG₀ probe hγ seed hconv hsolve hprobe hσ hσ₁ hgain
  filter_upwards [hw,hc.eventually hn] with k hk hck
  have hs := localExactPoint_spec f (x (k+n+1)) (v k) r
    (existsUnique_local_chord_minimum f G H hr hH₀ hLr hH hf hG _ _ hck)
  obtain ⟨alpha,ha⟩ := hs.2.1
  refine ⟨alpha,ha,?_⟩
  have he := rfc_model_line_anchor (windowStep (n:=n+1) x k) (windowImage G x k) (v k)
    (G (x (k+n+1)+v k)-G (x (k+n+1))) (G (x (k+n+1))) (x (k+n+1)) hk.2.2.1 alpha
  rw [←hk.2.2.2] at he
  change _=x (k+n+2) at he
  change x (k+n+2)-localExactPoint f (x (k+n+1)) (v k) r=_
  rw [ha,←he]
  dsimp only [x,v]
  abel_nf

end
end krylov.Convergence
