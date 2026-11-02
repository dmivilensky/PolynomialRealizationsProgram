import krylov.Convergence.SlidingRFCSuperlinear

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

/-- The actual recursively executed sliding RFC has vanishing defects,
eventually accepts the original positive gate, and is superlinear under
the independence of only its old stored normalized steps. -/
theorem rfcPath_superlinear
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
    (∀ᶠ k in atTop,‖pairDefect (windowStep (n:=n+1) (x) k)
      (windowImage G (x) k)‖<γ) ∧
    ((fun k=>x (k+1))=o[atTop]
      (fun k=>‖x k‖)) := by
  let q := v
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
      inner ℝ (G (x (k+i.val+1))-G (x (k+i.val))) (q k)=0 := hconj
  have hs := evaluatedRFC_source_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀
    (fun k i=>x (k+i.val)) (fun k i=>x (k+i.val+1)) (fun k=>x (k+n+1)) q
    ha hb hx (hprobe.mono fun _ h=>h.2) hn hc hσ hσ₁ hgain hγ
  refine ⟨hs.1,?_⟩
  have hsl : (fun k=>x (k+n+2))=o[atTop](fun k=>‖x (k+n+1)‖) :=
    hs.2.2.congr_left (fun k=>(hquery k).symm)
  have hmap : ((fun k=>x (k+1)) ∘ (fun k=>k+(n+1)))=o[atTop]
      ((fun k=>‖x k‖) ∘ (fun k=>k+(n+1))) := by
    simpa only [Function.comp_def,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hsl
  have hout := Asymptotics.isLittleO_map.mpr hmap
  simpa only [Filter.map_add_atTop_eq_nat] using hout

end
end krylov.Convergence
