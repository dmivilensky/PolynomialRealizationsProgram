import krylov.Envelope.XRFCNativeWeights
import krylov.Envelope.TrialReferenceSums
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual chronological reference weighted-prefix identity.
Use: connect true full-memory XRFC reference steps to the printed physical back-substitution prefix formulas at every genuine bounded horizon.
Source: actual empty initial solve, proved true bidiagonal noninitial steps and genuine finite trial-product prefix theorem.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual initial full-memory XRFC evaluated query is its genuine trial times the original initial CG direction.
Use: The actual initial full-memory XRFC evaluated query is its genuine trial times the original initial CG direction.
Article: main_krylov, thm:E1, actual chronological reference weighted-prefix identity.
Proof: Both genuine initial stored-window combinations are empty and the actual conjugacy direction is the negative initial gradient. -/
theorem xrfc_reference_step_zero (trial : History E → ℝ) (Q : E →L[ℝ] E) (g : E) :
    let m := xrfcMethod fullMemory trial
    oneGradientStep m (fun _ => Q) g 0=
      trial (oneGradientRun m (fun _ => Q) g 0) • CG.direction Q g 0 := by
  -- The genuine initial virtual and conjugacy solves have empty physical windows.
  have hc : virtualCorrection ([] : List (E × E)) g=0 := by
    change (∑ i : Fin 0,virtualCoefficients [] g i • windowSteps [] i)=0
    exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
  have hv : virtualGradient ([] : List (E × E)) g=g := by
    change g+(∑ i : Fin 0,virtualCoefficients [] g i • windowImages [] i)=g
    simp
  have hd : windowDirection ([] : List (E × E)) g= -g := by
    change -g+(∑ i : Fin 0,conjugacyCoefficients (windowSteps []) (windowImages []) g i • windowSteps [] i)= -g
    simp
  dsimp only
  change virtualCorrection [] g+trial _ • windowDirection [] (virtualGradient [] g)=_ • (-g)
  rw [hc,hv,hd,zero_add]

/-- Every genuine actual XRFC reference weighted-step prefix equals the printed signed later-correction product times its real final missed CG component.
Use: Every genuine actual XRFC reference weighted-step prefix equals the printed signed later-correction product times its real final missed CG component.
Article: main_krylov, thm:E1, actual chronological reference weighted-prefix identity.
Proof: Insert the true initial query, actual noninitial bidiagonal steps and genuine bounded nonzero trials into the proved physical prefix synthesis. -/
theorem xrfc_reference_weighted_prefix (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k l : ℕ) (hk : k≤N) (hl : l<k) :
    let m := xrfcMethod fullMemory trial
    let tau := fun j => trial (oneGradientRun m (fun _ => Q) g j)
    let rho := fun j => CG.length Q g j-tau j
    (∑ i∈Finset.range (l+1),trialWeightAt (fun j => rho j/tau j) k i • oneGradientStep m (fun _ => Q) g i)=
      trialTailFactor tau rho k l • (rho l • CG.direction Q g l) := by
  dsimp only
  apply trialWeights_prefix_sum
  · exact hl
  · intro j hj
    exact ht j (hj.trans_le hk)
  · exact xrfc_reference_step_zero trial Q g
  · intro j hj
    exact xrfc_full_step_succ trial Q hQ hpos g N hpre ht j (hj.trans_le hk)
end
end krylov.Envelope
