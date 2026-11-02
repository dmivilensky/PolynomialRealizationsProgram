import krylov.Convergence.SlidingRFCWindows
import krylov.Convergence.RFCPathSuperlinear

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

/-- Every late actual RFC iteration has its derived full-frame domain and
uniform inverse bound and takes exactly its genuine anchored model step. -/
theorem rfcPath_window_domains
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
        let U : ℕ → Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) :=
      fun k=>Fin.snoc (windowStep (n:=n+1) x k) (v k)
    let Z : ℕ → Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) :=
      fun k=>Fin.snoc (windowImage G x k) (G (x (k+n+1)+v k)-G (x (k+n+1)))
    ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (U k))).det ∧
      ‖(windowMatrix (unitWindow (U k)))⁻¹‖≤(σ^2/2)⁻¹+1 ∧
      IsUnit (ss1Model (U k) (Z k)).det ∧
      x (k+n+2)=ss1Point (U k) (Z k) (G (x (k+n+1))) (x (k+n+1)) := by
  have ha (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val)) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val+1)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hx : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hm : ∀ᶠ k in atTop,(∀ i : Fin (n+1),x (k+i.val)∈S) ∧
      (∀ i : Fin (n+1),x (k+i.val+1)∈S) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)
  have hn : ∀ᶠ k in atTop,(∀ i : Fin (n+1),x (k+i.val+1)-x (k+i.val)≠0) ∧v k≠0 := by
    filter_upwards [hsolve,hprobe] with k hk hp
    exact ⟨fun i=>observed_solve_step_ne_zero (windowStep (n:=n+1) x k) (windowImage G x k) hk i,hp.1⟩
  have hc : ∀ᶠ k in atTop,∀ i : Fin (n+1),
      inner ℝ (G (x (k+i.val+1))-G (x (k+i.val))) (v k)=0 := hconj
  have hf := source_probe_frame_conditioning G H S hS h₀ hH hH₀ hG
    (fun k i=>x (k+i.val)) (fun k i=>x (k+i.val+1)) v ha hb hm hn hc hσ hσ₁ hgain
  have hs := evaluatedRFC_source_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀
    (fun k i=>x (k+i.val)) (fun k i=>x (k+i.val+1)) (fun k=>x (k+n+1)) v
    ha hb hx (hprobe.mono fun _ h=>h.2) hn hc hσ hσ₁ hgain hγ
  filter_upwards [hf,hs.1,hs.2.1] with k hk hgate hM
  refine ⟨hk.1,hk.2,hM,?_⟩
  rw [hquery]
  exact evaluatedRFCPoint_eq_ss1Point G _ _ _ _ γ hgate hM

end
end krylov.Convergence
