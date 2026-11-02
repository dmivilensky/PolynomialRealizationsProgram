import krylov.XR.LocalNativeResponse

/-!
Article: main_krylov, lem:xr-local and thm:E1, assembled native prefix jet.
Use: transfer the complete physical output-defect formula to the actual
native adaptive trial. The primitive endpoint trial hypotheses derive all
regularity; no native trial jet or output expansion is supplied as a field.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Envelope
open Filter Topology
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The genuine native partial-cycle semantic output derivative is the
printed E1 effective-gradient derivative plus the actual reference-weighted
output-segment defect. Reference steps and weights are those of the native
computed reference trials, without an external trial/output certificate. -/
theorem native_XR_operator_prefix_E1 (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g : E) (constant : ℝ)
    (hg : ∀ i < n, CG.gradient Q g i ≠ 0)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g constant) (quadraticGradient Q g) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C)
    (N : ℕ) (hN : N ≤ n) (e : ℝ → Fin (N+1) → E →L[ℝ] E)
    (he : ContDiffAt ℝ 2 e 0) (he₀ : e 0 = 0) :
    let tau₀ := nativeOperatorTrialVector P bounds Q g constant N 0
    let trial : History E → ℝ := prescribedTrial tau₀
    let A := fun t => prescribedOperatorPath Q (e t)
    let B := fun t => Q+e t (Fin.last N)
    deriv (fun t => (nativeOperatorOutput P bounds Q g constant N (e t)).2) 0 =
      deriv (fun t => xrfcVirtualGradient trial (A t) g N) 0+xrfcOutputJet trial A B Q g N := by
  let tau₀ := nativeOperatorTrialVector P bounds Q g constant N 0
  let trial : History E → ℝ := prescribedTrial tau₀
  let A := fun t => prescribedOperatorPath Q (e t)
  let B := fun t => Q+e t (Fin.last N)
  let F := fun z => prescribedXRFCOutput Q g N (z,tau₀)
  have hpre : ∀ i<N, CG.gradient Q g i ≠ 0 := fun i hi => hg i (hi.trans_le hN)
  have hposTau := nativeOperatorTrialVector_zero_pos P bounds Q g constant N
    (fun k hk => (htrial k (hk.trans_le hN)).1)
  have ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i) ≠ 0 := by
    intro i hi
    change prescribedTrial tau₀ (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i) ≠ 0
    rw [prescribedTrial_run_scalar tau₀ _ _ g i hi]
    exact (hposTau ⟨i,hi⟩).ne'
  have hA : ∀ i,ContDiffAt ℝ 2 (fun t => A t i) 0 := by
    intro i
    dsimp only [A, prescribedOperatorPath]
    split_ifs with hi
    · exact contDiffAt_const.add ((contDiffAt_pi.mp he) ⟨i,by omega⟩)
    · exact contDiffAt_const
  have hB : ContDiffAt ℝ 2 B 0 := contDiffAt_const.add ((contDiffAt_pi.mp he) (Fin.last N))
  have hA₀ : A 0 = fun _ => Q := by rw [show A 0 = prescribedOperatorPath Q (e 0) from rfl, he₀, prescribedOperatorPath_zero]
  have hB₀ : B 0 = Q := by simp only [B, he₀, Pi.zero_apply, add_zero]
  have hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A 0) g k) :=
    fun k hk => prescribedTrial_coordinate_contDiff tau₀ hk _
  have hfixed := xrfc_output_first_jet trial A B g Q hQ hpos hA₀ hB₀ N hA hB hpre ht hT
  have hpair := native_operator_prefix_path_deriv_eq P bounds hinit hmax Q hQ hpos g constant hg htrial N hN e he he₀
  have hnativeOuter : ContDiffAt ℝ 2 (nativeOperatorOutput P bounds Q g constant N) (e 0) := by
    rw [he₀]
    exact nativeOperatorOutput_contDiffAt P bounds hinit hmax Q hQ hpos g constant hg htrial N hN
  have hnative := (hnativeOuter.comp (0 : ℝ) he).differentiableAt (by norm_num)
  have hF : ContDiffAt ℝ 2 F 0 :=
    (prescribedXRFCOutput_contDiffAt Q hQ hpos g N hpre tau₀ (fun i => (hposTau i).ne')).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)
  have hfixedOuter : ContDiffAt ℝ 2 F (e 0) := by rw [he₀]; exact hF
  have hfixedDiff := (hfixedOuter.comp (0 : ℝ) he).differentiableAt (by norm_num)
  let sndMap := ContinuousLinearMap.snd ℝ E E
  have hproj1 := sndMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hnative.hasDerivAt
  have hproj2 := sndMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hfixedDiff.hasDerivAt
  have heq : deriv (fun t => (nativeOperatorOutput P bounds Q g constant N (e t)).2) 0 =
      deriv (fun t => (F (e t)).2) 0 :=
    hproj1.deriv.trans ((congrArg Prod.snd hpair).trans hproj2.deriv.symm)
  exact heq.trans hfixed

end
end krylov.XR
