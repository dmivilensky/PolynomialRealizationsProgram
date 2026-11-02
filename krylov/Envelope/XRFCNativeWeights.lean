import krylov.Envelope.TrialWeightPrefix
import krylov.Methods.OneGradientChronological
import krylov.Methods.XRFCShortPrefix
import krylov.Stability.XRFCModelDomains
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine native virtual weights and printed back substitution.
Use: identify actual chronological coefficients computed by the true full-memory XRFC model inverse with the exact signed trial-product construction.
Source: genuine actual missed-direction correction, bounded bidiagonal step identities and proved original positive model independence.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual native full-memory XRFC reference virtual-solve coefficients are exactly the printed chronological back-substitution weights for every true bounded nonzero trial prefix.
Use: The actual native full-memory XRFC reference virtual-solve coefficients are exactly the printed chronological back-substitution weights for every true bounded nonzero trial prefix.
Article: main_krylov, thm:E1, genuine native virtual weights and printed back substitution.
Proof: Both true coefficient families synthesize the actual missed newest direction in the same genuine stored-step basis. Its independence follows from the actual positive reference model, so the computed coefficients coincide. -/
theorem xrfc_native_reference_weights (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let m := xrfcMethod fullMemory trial (E := E)
    let tau := fun j => trial (oneGradientRun m (fun _ => Q) g j)
    oneGradientVirtualCoefficients m (fun _ => Q) g k=
      trialWeights (fun j => (CG.length Q g j-tau j)/tau j) k := by
  dsimp only
  let m := xrfcMethod fullMemory trial (E := E)
  let tau := fun j => trial (oneGradientRun m (fun _ => Q) g j)
  let rho := fun j => CG.length Q g j-tau j
  let s := oneGradientStep m (fun _ => Q) g
  -- Compare genuine physical syntheses in the actual independent reference stored-step basis.
  cases k with
  | zero => exact funext fun i => Fin.elim0 i
  | succ k =>
    have hs0 : s 0=tau 0 • CG.direction Q g 0 := by
      have h := xrfc_full_evaluated trial Q hQ hpos g N hpre ht 0 (by omega)
      dsimp only at h
      rw [oneGradientRun_displacement_sum] at h
      simpa only [Finset.sum_range_one,CG.displacement,Finset.sum_range_zero,zero_add] using h
    have hs (j : ℕ) (hj : j<k) : s (j+1)=rho j • CG.direction Q g j+tau (j+1) • CG.direction Q g (j+1) :=
      xrfc_full_step_succ trial Q hQ hpos g N hpre ht j (by omega)
    have hsum := trialWeights_bidiagonal_bounded tau rho (CG.direction Q g) s k
      (fun j hj => ht j (by omega)) hs0 hs
    have hactual := (oneGradient_chronological_virtual m (fun _ => Q) g (k+1)).1
    have hout := xrfc_full_next_correction trial Q hQ hpos g N hpre ht k (by omega)
    have hc : (∑ i : Fin (k+1),oneGradientVirtualCoefficients m (fun _ => Q) g (k+1) i • s i.val)=
        ∑ i : Fin (k+1),trialWeights (fun j => rho j/tau j) (k+1) i • s i.val := by
      rw [hsum]
      exact hactual.symm.trans hout
    -- The original positive model proves true stored-step independence before uniqueness of the actual inverse coefficients is used.
    let S := fun i : Fin (k+1) => s (k+1-1-i.val)
    have hdom := (xrfc_full_array_domains trial Q hQ hpos g N hpre ht (k+1) hk).2
    have hunit : IsUnit (correctionCompression S Q).det := by
      rw [← pairModel_quadratic S Q hQ]
      exact isUnit_iff_ne_zero.mpr hdom
    have hLI := compression_unit_independent S Q hunit
    have hChron : LinearIndependent ℝ (fun i : Fin (k+1) => s i.val) := by
      have h := hLI.comp (Fin.revPerm (n := k+1)) (Fin.revPerm (n := k+1)).injective
      convert h using 1
      funext i
      change s i.val=s (k+1-1-i.rev.val)
      congr 1
      rw [Fin.val_rev]
      omega
    apply funext
    intro i
    apply sub_eq_zero.mp
    apply Fintype.linearIndependent_iff.mp hChron (fun j =>
      oneGradientVirtualCoefficients m (fun _ => Q) g (k+1) j-trialWeights (fun j => rho j/tau j) (k+1) j) _ i
    simp only [sub_smul,Finset.sum_sub_distrib,hc,sub_self]
end
end krylov.Envelope
