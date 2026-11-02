import krylov.Functions.NativeRFCFOperators

/-!
Article: main_krylov, prop:Fcycle, genuine terminal observed domains.
Use: derive the actual accepted RFC-F gate and the inverse current-line
coordinate scale from genuine compact nonstagnating quadratic references.
Source: actual finite chronological pair coordinates, strict gate continuity,
real positive CG curvature and the compact analytic reference tube.
-/
namespace krylov.Functions
noncomputable section
open Matrix Set Filter Asymptotics Topology krylov.Reference krylov.Methods krylov.Stability
  krylov.Correction krylov.Envelope krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual full-history RFC gate is exactly its genuine finite old-pair gate.
Article: main_krylov, prop:Fcycle, observed gate dictionary. -/
theorem rfcFunctionGate_operator_iff (A B : ℕ → E →L[ℝ] E) (g : E)
    (k : ℕ) (hk : 0<k) :
    rfcFunctionGate fullMemory (methodRun (rfcMethod fullMemory 1) A B g k) ↔
      ‖pairDefect (fun i : Fin k=>probedStep (rfcMethod fullMemory 1) A B g (k-1-i.val))
        (fun i : Fin k=>probedSecant (rfcMethod fullMemory 1) A B g (k-1-i.val))‖<1 := by
  let s := probedStep (rfcMethod fullMemory 1) A B g
  let y := probedSecant (rfcMethod fullMemory 1) A B g
  let W := (executedPairs s y k).take k
  have hlen : W.length=k := by simp only [W,List.length_take,executedPairs_length,min_self]
  have hcoord := retainedWindow_coordinates s y k k
  have hs : windowSteps W=(fun i : Fin k=>s (k-1-i.val)) ∘ finCongr hlen := hcoord.1
  have hy : windowImages W=(fun i : Fin k=>y (k-1-i.val)) ∘ finCongr hlen := hcoord.2
  have hne : W≠[] := by
    intro hz
    have he : W.length=0 := by rw [hz]; rfl
    omega
  unfold rfcFunctionGate
  rw [selectedWindow_methodRun]
  change W≠[] ∧ ‖windowDefect W‖<1 ↔ _
  rw [windowDefect_norm_of_coordinates W hlen _ _ hs hy]
  exact and_iff_right hne

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

set_option maxHeartbeats 800000 in
/-- Every true analytic ordinary-RFC prefix has a genuinely accepted old-pair gate near its nondegenerate quadratic reference.
Article: main_krylov, prop:Fcycle and lem:U.
Proof: each actual retained pair is continuous with a real nonzero CG step
and its true positive quadratic image. The strict observed defect test
therefore persists locally in the original source variables. -/
theorem rfcFunctionGate_eventually
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X)
    (hA : ∀ i, AnalyticAt ℝ (fun z=>A z i) x)
    (hB : ∀ i, AnalyticAt ℝ (fun z=>B z i) x) (hg : AnalyticAt ℝ g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _=>Q) (hBx : B x=fun _=>Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hk : 0<k) (hpre : ∀ i≤k,CG.gradient Q (g x) i≠0) :
    ∀ᶠ z in 𝓝 x, rfcFunctionGate fullMemory (methodRun (rfcMethod fullMemory 1) (A z) (B z) (g z) k) := by
  let m := rfcMethod fullMemory 1 (E := E)
  let S := fun z (i : Fin k)=>probedStep m (A z) (B z) (g z) (k-1-i.val)
  let Y := fun z (i : Fin k)=>probedSecant m (A z) (B z) (g z) (k-1-i.val)
  have ht := quadraticRFC_prefix_analytic fullMemory 1 A B g x hA hB hg Q hAx hBx hQ hpos
    (fun _ _ ha=>ha) (k+1) (fun i hi=>hpre i (by omega))
  have href := rfc_reference_augmented_data fullMemory 1 Q hQ hpos (g x) (fun _ _ ha=>ha) k hpre
  rw [show min (fullMemory k) k=k from min_self k] at href
  have hn (i : Fin k) : S x i≠0 := by
    have h := href.1 i.succ
    dsimp only [S]
    rw [hAx,hBx]
    exact h
  have hyQ (i : Fin k) : Y x i=Q (S x i) := by
    have h := congrFun href.2.1 i.succ
    dsimp only [Y,S]
    rw [hAx,hBx]
    exact h
  have he := quadratic_pairDefect_gate S Y x (fun i=>(ht.2 (k-1-i.val) (by omega)).2.1.continuousAt)
    (fun i=>(ht.2 (k-1-i.val) (by omega)).2.2.continuousAt) Q hQ hpos hn hyQ
  exact he.mono fun z hz=>(rfcFunctionGate_operator_iff (A z) (B z) (g z) k hk).mpr hz

end
end krylov.Functions
