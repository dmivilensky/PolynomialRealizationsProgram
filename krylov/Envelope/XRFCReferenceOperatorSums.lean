import krylov.Envelope.XRFCReferenceBidiagonal
import krylov.Envelope.TrialOperatorIdentities
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual computed reference virtual trial operator sums.
Use: identify original native virtual output and effective-injection sums with the printed chronological increment factors using true executed reference data.
Source: proved actual native back-substitution weights, real bounded bidiagonal XRFC steps and genuine physical operator summation by parts.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual native-weighted reference output tail actions equal the printed signed later-correction products acting on the true missed CG directions.
Use: The actual native-weighted reference output tail actions equal the printed signed later-correction products acting on the true missed CG directions.
Article: main_krylov, thm:E1, actual computed reference virtual trial operator sums.
Proof: Replace the genuine computed native weights by their proved back substitution and apply exact original operator tail-prefix summation. -/
theorem xrfc_reference_output_increment_sum (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (D : ℕ → E →ₗ[ℝ] E) :
    let m := xrfcMethod fullMemory trial
    let tau := fun j => trial (oneGradientRun m (fun _ => Q) g j)
    let rho := fun j => CG.length Q g j-tau j
    (∑ i : Fin N,oneGradientVirtualCoefficients m (fun _ => Q) g N i •
      (∑ l∈Finset.Ico i.val N,D l) (oneGradientStep m (fun _ => Q) g i.val))=
    ∑ l∈Finset.range N,trialTailFactor tau rho N l • D l (rho l • CG.direction Q g l) := by
  dsimp only
  -- Identify actual computed native weights before transforming the original physical operator sums.
  let m := xrfcMethod fullMemory trial (E := E)
  let tau := fun j => trial (oneGradientRun m (fun _ => Q) g j)
  let rho := fun j => CG.length Q g j-tau j
  let s := oneGradientStep m (fun _ => Q) g
  have hw := xrfc_native_reference_weights trial Q hQ hpos g N hpre ht N le_rfl
  dsimp only at hw
  rw [hw]
  have he : (∑ i : Fin N,trialWeights (fun j => rho j/tau j) N i • (∑ l∈Finset.Ico i.val N,D l) (s i.val))=
      ∑ i∈Finset.range N,(∑ l∈Finset.Ico i N,D l) (trialWeightAt (fun j => rho j/tau j) N i • s i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [trialWeightAt_used,map_smul]
  rw [he]
  exact trial_output_increment_sum (CG.length Q g) tau (CG.direction Q g) s D N ht
    (xrfc_reference_step_zero trial Q g) (fun j hj => xrfc_full_step_succ trial Q hQ hpos g N hpre ht j hj)

/-- The actual native-weighted reference effective injection minus its genuine ordinary CG injection equals the printed finite trial-delta increment sum.
Use: The actual native-weighted reference effective injection minus its genuine ordinary CG injection equals the printed finite trial-delta increment sum.
Article: main_krylov, thm:E1, actual computed reference virtual trial operator sums.
Proof: Use actual native coefficient uniqueness and the genuine zero total weighted CG displacement in physical operator summation by parts; remove the true zero final increment. -/
theorem xrfc_reference_injection_increment_sum (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (D : ℕ → E →ₗ[ℝ] E) :
    let m := xrfcMethod fullMemory trial
    let tau := fun j => trial (oneGradientRun m (fun _ => Q) g j)
    let rho := fun j => CG.length Q g j-tau j
    (∑ i : Fin N,(1+oneGradientVirtualCoefficients m (fun _ => Q) g N i) •
      (∑ l∈Finset.range i.val,D l) (oneGradientStep m (fun _ => Q) g i.val))-
    (∑ i∈Finset.range N,(∑ l∈Finset.range i,D l) (referenceStep Q g i))=
    ∑ l∈Finset.range (N-1),(1-trialTailFactor tau rho N l) • D l (rho l • CG.direction Q g l) := by
  dsimp only
  let m := xrfcMethod fullMemory trial (E := E)
  let tau := fun j => trial (oneGradientRun m (fun _ => Q) g j)
  let rho := fun j => CG.length Q g j-tau j
  let s := oneGradientStep m (fun _ => Q) g
  have hw := xrfc_native_reference_weights trial Q hQ hpos g N hpre ht N le_rfl
  dsimp only at hw
  rw [hw]
  have he : (∑ i : Fin N,(1+trialWeights (fun j => rho j/tau j) N i) • (∑ l∈Finset.range i.val,D l) (s i.val))=
      ∑ i∈Finset.range N,(∑ l∈Finset.range i,D l) ((1+trialWeightAt (fun j => rho j/tau j) N i) • s i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [trialWeightAt_used,map_smul]
  rw [he,← Finset.sum_sub_distrib]
  -- The genuine total weighted reference displacement is zero, so actual summation by parts leaves precisely the printed trial increments.
  have hh := trial_injection_increment_sum (CG.length Q g) tau (CG.direction Q g) s D N ht
    (xrfc_reference_step_zero trial Q g) (fun j hj => xrfc_full_step_succ trial Q hQ hpos g N hpre ht j hj)
  have htrim := trial_injection_last_zero tau rho (CG.direction Q g) D N
  simpa only [referenceStep,map_sub,map_smul] using hh.trans htrim
end
end krylov.Envelope
