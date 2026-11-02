import krylov.Convergence.SlidingRFCExecution
import krylov.Convergence.WindowProbeConditioning
import krylov.Convergence.SecantMovingModel

/-!
Article: main_krylov, thm:Ip, source-to-query RFC superlinearity.
Use: derive actual gate acceptance, true full-model inverse domains and
the anchored Newton-model query from the original local derivatives and
independence of only the stored steps. Source: bounded real probes,
observed conjugacy, the sharp augmented Gram bound and the actual secant
FTC model estimate. No model convergence or desired recurrence is assumed.
-/

namespace krylov.Convergence
noncomputable section
open Set Filter Topology Matrix Asymptotics krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ} {α : Type*} {l : Filter α}

/-- Evaluated RFC on genuine moving source windows has automatic actual
gates and full model domains, its actual anchored query identity, and
superlinear error. Only the old stored steps carry an independence premise. -/
theorem evaluatedRFC_source_superlinear
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (S : Set (EuclideanSpace ℝ (Fin (n+2)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (a b : α → Fin (n+1) → EuclideanSpace ℝ (Fin (n+2)))
    (x q : α → EuclideanSpace ℝ (Fin (n+2)))
    (ha : ∀ i,Tendsto (fun z=>a z i) l (𝓝 0))
    (hb : ∀ i,Tendsto (fun z=>b z i) l (𝓝 0)) (hx : Tendsto x l (𝓝 0))
    {cP : ℝ} (hprobe : ∀ᶠ z in l,‖q z‖≤cP*‖x z‖)
    (hne : ∀ᶠ z in l,(∀ i,b z i-a z i≠0) ∧q z≠0)
    (hconj : ∀ᶠ z in l,∀ i,inner ℝ (G (b z i)-G (a z i)) (q z)=0)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1)
    (hgain : ∀ᶠ z in l,∀ c : Fin (n+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (fun i=>b z i-a z i)) c‖^2)
    {γ : ℝ} (hγ : 0<γ) :
    (∀ᶠ z in l,‖pairDefect (fun i=>b z i-a z i) (fun i=>G (b z i)-G (a z i))‖<γ) ∧
    (∀ᶠ z in l,
      IsUnit (ss1Model (Fin.snoc (fun i=>b z i-a z i) (q z))
        (Fin.snoc (fun i=>G (b z i)-G (a z i)) (G (x z+q z)-G (x z)))).det) ∧
    ((fun z=>evaluatedRFCPoint G (fun i=>b z i-a z i)
      (fun i=>G (b z i)-G (a z i)) (x z) (q z) γ)=o[l](fun z=>‖x z‖)) := by
  have hq : Tendsto q l (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun z=>cP*‖x z‖) hprobe
    simpa only [norm_zero,mul_zero] using hx.norm.const_mul cP
  have hplus : Tendsto (fun z=>x z+q z) l (𝓝 0) := by simpa only [add_zero] using hx.add hq
  let A : α → Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) := fun z=>Fin.snoc (a z) (x z)
  let B : α → Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)) := fun z=>Fin.snoc (b z) (x z+q z)
  have hA (i : Fin (n+2)) : Tendsto (fun z=>A z i) l (𝓝 0) := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [A,Fin.snoc_last] using hx
    · simpa only [A,Fin.snoc_castSucc] using ha j
  have hB (i : Fin (n+2)) : Tendsto (fun z=>B z i) l (𝓝 0) := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [B,Fin.snoc_last] using hplus
    · simpa only [B,Fin.snoc_castSucc] using hb j
  have hm : ∀ᶠ z in l,(∀ i,a z i∈S) ∧(∀ i,b z i∈S) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)
  have hM : ∀ᶠ z in l,(∀ i,A z i∈S) ∧(∀ i,B z i∈S) :=
    (Filter.eventually_all.mpr fun i=>(hA i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hB i).eventually hnbhd)
  have hsteps z : (fun i=>B z i-A z i)=Fin.snoc (fun i=>b z i-a z i) (q z) := by
    funext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [A,B,Fin.snoc_last,add_sub_cancel_left]
    · simp only [A,B,Fin.snoc_castSucc]
  have himages z : (fun i=>G (B z i)-G (A z i))=
      Fin.snoc (fun i=>G (b z i)-G (a z i)) (G (x z+q z)-G (x z)) := by
    funext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [A,B,Fin.snoc_last]
    · simp only [A,B,Fin.snoc_castSucc]
  have hframe := source_probe_frame_conditioning G H S hS h₀ hH hH₀ hG a b q ha hb hm
    hne hconj hσ hσ₁ hgain
  have hframe' : ∀ᶠ z in l,
      IsUnit (windowMatrix (unitWindow (fun i=>B z i-A z i))).det ∧
      ‖(windowMatrix (unitWindow (fun i=>B z i-A z i)))⁻¹‖≤(σ^2/2)⁻¹+1 := by
    simpa only [hsteps] using hframe
  have hdomain := (source_moving_model_tendsto G H S hS h₀ hH hH₀ hG A B hA hB hM
    (by positivity : 0≤(σ^2/2)⁻¹+1) hframe').2.2
  have hgate := source_window_eventually_defect_gate G H S hS h₀ hH hH₀ hG a b ha hb hm
    (hne.mono fun _ h=>h.1) hγ
  have hlim := ss1_source_superlinear G H S hS h₀ hH hH₀ hG hG₀ A B x hA hB hx
    (hM.and (hx.eventually hnbhd) |>.mono fun _ h=>⟨h.1.1,h.1.2,h.2⟩)
    (by positivity : 0≤(σ^2/2)⁻¹+1) hframe'
  refine ⟨hgate,?_,?_⟩
  · simpa only [hsteps,himages] using hdomain
  · apply hlim.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [hgate,hdomain] with z hg hd
    rw [hsteps,himages] at hd ⊢
    exact (evaluatedRFCPoint_eq_ss1Point G _ _ _ _ γ hg hd).symm

end
end krylov.Convergence
