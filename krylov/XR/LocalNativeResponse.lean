import krylov.XR.LocalNativeOperatorVariation
import krylov.OneGradient.XRFCStepTaylor
import krylov.Convergence.OneGradientRepresentatives

/-!
Article: main_krylov, lem:xr-local, assembled native I/E1 response.
Use: the real native adaptive trial has the complete first variation and
quadratic remainder of the original fixed-reference XRFC response. Trial
regularity is derived by the real finite operator-input endpoint induction.
The exact function/source dictionaries are proved in the imported leaves.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.OneGradient
open krylov.Envelope krylov.Secant krylov.Functions krylov.Convergence Filter Topology
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The original finite prescribed rule is C² in the actual observed
history chart, because its only read is the true record count. -/
theorem prescribedTrial_coordinate_contDiff {N k : ℕ} (tau : Fin N → ℝ) (hk : k < N)
    (data : E × (Fin k → E) × (Fin k → E)) :
    ContDiffAt ℝ 2 (trialCoordinate ((prescribedTrial tau) : History E → ℝ) k) data := by
  have he : trialCoordinate ((prescribedTrial tau) : History E → ℝ) k = fun _ => tau ⟨k,hk⟩ := by
    funext d
    simp only [trialCoordinate, prescribedTrial, oneGradientHistoryChart, List.length_ofFn,
      dite_eq_left hk]
  rw [he]
  exact contDiffAt_const

/-- Along every actual smooth operator path, the complete native pair
(point, semantic gradient) has the same derivative as its fixed-reference
trial vector, for each partial cycle. This is the E1 transfer identity. -/
theorem native_operator_prefix_path_deriv_eq (P : Parameters) (bounds : SpectralBounds)
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
    deriv (fun t => nativeOperatorOutput P bounds Q g constant N (e t)) 0 =
      deriv (fun t => prescribedXRFCOutput Q g N (e t,tau₀)) 0 := by
  let tau₀ := nativeOperatorTrialVector P bounds Q g constant N 0
  let F := fun z => prescribedXRFCOutput Q g N (z,tau₀)
  have hn := native_operator_prefix_first_variation P bounds hinit hmax Q hQ hpos g constant hg htrial N hN
  have hposTau := nativeOperatorTrialVector_zero_pos P bounds Q g constant N
    (fun k hk => (htrial k (hk.trans_le hN)).1)
  have hf : ContDiffAt ℝ 2 F 0 :=
    (prescribedXRFCOutput_contDiffAt Q hQ hpos g N (fun i hi => hg i (hi.trans_le hN))
      tau₀ (fun i => (hposTau i).ne')).comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hD := (he.differentiableAt (by norm_num)).hasDerivAt
  dsimp only at hn
  have h1 := hn.comp_hasDerivAt_of_eq (0 : ℝ) hD he₀.symm
  have h2 := (hf.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hD he₀.symm
  exact h1.deriv.trans h2.deriv.symm

/-- The actual complete native operator response has the printed
step-basis first variation of thm:I, with no assumed native trial jet. -/
theorem native_XR_operator_full_response (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (constant : ℝ) (hatoms : referenceAtomCount base hb g = n) (hn : 0 < n)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective (cgOperator base) g constant) (quadraticGradient (cgOperator base) g) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k, ContDiffAt ℝ 2 (fun t => A t k) 0)
    (hsym : ∀ t k, (A t k).IsSymm) (hA₀ : ∀ k, A 0 k = base) :
    let Q := cgOperator base
    let tau₀ := nativeOperatorTrialVector P bounds Q g constant n 0
    let R := cgOperator (metricRoot base)⁻¹
    let errors := fun t (i : Fin (n+1)) => cgOperator (A t i.val)-Q
    HasDerivAt (fun t => R (nativeOperatorOutput P bounds Q g constant n (errors t)).2)
      (xrfcStepResponse (prescribedTrial tau₀) base g
        (fun l => R*(deriv (fun t => cgOperator (A t (l+1))) 0-
          deriv (fun t => cgOperator (A t l)) 0)*R)) 0 := by
  let Q := cgOperator base
  let tau₀ := nativeOperatorTrialVector P bounds Q g constant n 0
  let R := cgOperator (metricRoot base)⁻¹
  let errors := fun t (i : Fin (n+1)) => cgOperator (A t i.val)-Q
  let trial : History E → ℝ := prescribedTrial tau₀
  let m := xrfcMethod fullMemory trial
  have hp := cgOperator_positive base hb
  have hg : ∀ i < n, CG.gradient Q g i ≠ 0 := by simpa only [hatoms] using cg_nonstagnation base hb g
  have htau := nativeOperatorTrialVector_zero_pos P bounds Q g constant n (fun k hk => (htrial k hk).1)
  have ht : ∀ i<n, trial (oneGradientRun m (fun _ => Q) g i) ≠ 0 := by
    intro i hi
    change prescribedTrial tau₀ (oneGradientRun m (fun _ => Q) g i) ≠ 0
    rw [prescribedTrial_run_scalar tau₀ m _ g i hi]
    exact (htau ⟨i,hi⟩).ne'
  have hT : ∀ i<n, ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData m (fun _ => Q) g i) :=
    fun i hi => prescribedTrial_coordinate_contDiff tau₀ hi _
  have herrors : ContDiffAt ℝ 2 errors 0 := by
    apply contDiffAt_pi.mpr
    intro i
    exact (matrixOperator_contDiffAt _ 0 (hA i.val)).sub contDiffAt_const
  have he₀ : errors 0 = 0 := by funext i; simp only [errors, hA₀, Q, sub_self, Pi.zero_apply]
  let F := fun z => prescribedXRFCOutput Q g n (z,tau₀)
  have hF : ContDiffAt ℝ 2 F 0 :=
    (prescribedXRFCOutput_contDiffAt Q hp.1 hp.2 g n hg tau₀ (fun i => (htau i).ne')).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)
  have hD := (herrors.differentiableAt (by norm_num)).hasDerivAt
  have hnD := native_operator_prefix_first_variation P bounds hinit hmax Q hp.1 hp.2 g constant hg htrial n le_rfl
  dsimp only at hnD
  let sndMap := ContinuousLinearMap.snd ℝ E E
  have hnativePair := hnD.comp_hasDerivAt_of_eq (0 : ℝ) hD he₀.symm
  have hfixedPair := (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hD he₀.symm
  have hnative := R.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (sndMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hnativePair)
  have hfixed := R.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (sndMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hfixedPair)
  have hdict (t : ℝ) : (F (errors t)).2 = m.outputGradient (cgOperator (A t n))
      (oneGradientRun m (fun i => cgOperator (A t i)) g n) := by
    have hpath : ∀ i<n, prescribedOperatorPath Q (errors t) i = cgOperator (A t i) := by
      intro i hi
      simp only [prescribedOperatorPath, dite_eq_left hi, errors, add_sub_cancel]
    unfold F prescribedXRFCOutput
    dsimp only
    rw [oneGradientRun_congr_prefix m _ _ g n hpath]
    simp only [errors, Fin.val_last, add_sub_cancel]
    rfl
  have hj := xrfc_step_output_first_jet trial base hb g hatoms hn A
    (fun k => (hA k).of_le (by norm_num)) hsym hA₀ ht (fun i hi => (hT i hi).of_le (by norm_num))
  have hfixed' := hj.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => congrArg R (hdict t)))
  exact hnative.congr_deriv (hfixed.unique hfixed')

end
end krylov.XR
