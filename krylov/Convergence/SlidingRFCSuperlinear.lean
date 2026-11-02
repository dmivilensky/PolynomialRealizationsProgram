import krylov.Convergence.SlidingRFCSource

/-!
Article: main_krylov, thm:Ip, literal sliding RFC superlinearity.
Use: connect the actual recursive observed solver and bounded evaluated
probes to the source theorem. Measured conjugacy, actual nonzero stored
pairs, defect gates and full augmented-model domains are derived.
Source: genuine observed solve cancellation and the original (A1)--(A4).
-/

namespace krylov.Convergence
noncomputable section
open Set Filter Topology Matrix Asymptotics krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual recursively executed sliding RFC has vanishing defects,
eventually accepts the original positive gate, and is superlinear under
the independence of only its old stored normalized steps. -/
theorem slidingRFCSequence_superlinear
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
    (∀ᶠ k in atTop,‖pairDefect (windowStep (n:=n+1) (slidingRFCSequence G probe γ seed) k)
      (windowImage G (slidingRFCSequence G probe γ seed) k)‖<γ) ∧
    ((fun k=>slidingRFCSequence G probe γ seed (k+1))=o[atTop]
      (fun k=>‖slidingRFCSequence G probe γ seed k‖)) := by
  let x := slidingRFCSequence G probe γ seed
  let q := slidingRFCProbe G probe x
  have ha (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val)) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val+1)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hx : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hn : ∀ᶠ k in atTop,(∀ i : Fin (n+1),x (k+i.val+1)-x (k+i.val)≠0) ∧q k≠0 := by
    filter_upwards [hsolve,hprobe] with k hk hp
    refine ⟨?_,hp.1⟩
    intro i
    exact observed_solve_step_ne_zero (windowStep (n:=n+1) x k) (windowImage G x k) hk i
  have hc : ∀ᶠ k in atTop,∀ i : Fin (n+1),
      inner ℝ (G (x (k+i.val+1))-G (x (k+i.val))) (q k)=0 := by
    filter_upwards [hsolve] with k hk i
    let Q : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) := fun j=>x (k+j.val)
    have hsolve' : IsUnit (crossGram
        (fun i : Fin (n+1)=>G (Q i.succ)-G (Q i.castSucc))
        (fun i : Fin (n+1)=>Q i.succ-Q i.castSucc)).det := by
      have hsQ : (fun i : Fin (n+1)=>Q i.succ-Q i.castSucc)=windowStep x k := by
        funext i
        simp only [Q,windowStep,Fin.val_succ,Fin.val_castSucc,Nat.add_assoc]
      have hyQ : (fun i : Fin (n+1)=>G (Q i.succ)-G (Q i.castSucc))=windowImage G x k := by
        funext i
        simp only [Q,windowImage,Fin.val_succ,Fin.val_castSucc,Nat.add_assoc]
      rw [hsQ,hyQ]
      exact hk
    have hh := congrFun (conjugacyDirection_conjugate
      (fun i : Fin (n+1)=>Q i.succ-Q i.castSucc)
      (fun i=>G (Q i.succ)-G (Q i.castSucc)) (G (Q (Fin.last (n+1)))) hsolve') i
    have hpair : inner ℝ (G (Q i.succ)-G (Q i.castSucc))
        (slidingRFCWindowDirection G Q)=0 := hh
    change inner ℝ (G (x (k+i.val+1))-G (x (k+i.val)))
      (probe Q (slidingRFCWindowDirection G Q) • slidingRFCWindowDirection G Q)=0
    have hpair' : inner ℝ (G (x (k+i.val+1))-G (x (k+i.val)))
        (slidingRFCWindowDirection G Q)=0 := by
      simpa only [Q,Fin.val_succ,Fin.val_castSucc,Nat.add_assoc] using hpair
    rw [real_inner_smul_right,hpair',mul_zero]
  have hs := evaluatedRFC_source_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀
    (fun k i=>x (k+i.val)) (fun k i=>x (k+i.val+1)) (fun k=>x (k+n+1)) q
    ha hb hx (hprobe.mono fun _ h=>h.2) hn hc hσ hσ₁ hgain hγ
  refine ⟨hs.1,?_⟩
  have hquery k : evaluatedRFCPoint G (windowStep (n:=n+1) x k) (windowImage G x k)
      (x (k+n+1)) (q k) γ=x (k+n+2) := by
    change evaluatedRFCPoint G (fun i : Fin (n+1)=>x (k+i.val+1)-x (k+i.val))
      (fun i=>G (x (k+i.val+1))-G (x (k+i.val))) (x (k+n+1)) (q k) γ=x (k+n+2)
    simpa [slidingRFCWindowRule,slidingRFCProbe,windowStep,windowImage,x,q,Nat.add_assoc] using
      (slidingRFCSequence_step G probe γ seed k).symm
  have hsl : (fun k=>x (k+n+2))=o[atTop](fun k=>‖x (k+n+1)‖) :=
    hs.2.2.congr_left hquery
  have hmap : ((fun k=>x (k+1)) ∘ (fun k=>k+(n+1)))=o[atTop]
      ((fun k=>‖x k‖) ∘ (fun k=>k+(n+1))) := by
    simpa only [Function.comp_def,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hsl
  have hout := Asymptotics.isLittleO_map.mpr hmap
  simpa only [Filter.map_add_atTop_eq_nat] using hout

end
end krylov.Convergence
