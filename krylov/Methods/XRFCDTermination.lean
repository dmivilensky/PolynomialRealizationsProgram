import krylov.Methods.XRFCD

/-!
Article: main_krylov, lem:consistent(c), actual direction-window termination and model domains.
Use: close the one-gradient count and the full/positive sliding quadratic
regimes with actual reconstructed observations and actual computed inverses.
Source: executed XRFC-D invariants and active-spectrum CG termination.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual retained direction model of an executed quadratic XRFC-D run is positive definite.
Use: all implemented virtual and conjugacy inverses have their genuine domain on the complete nonstagnating prefix.
Article: main_krylov, lem:consistent(c), DᵀAD positive diagonal model.
Proof: actual data-only replay equals the true retained conjugate direction list;
its nonzero conjugate independence gives the genuine positive operator Gram model. -/
theorem xrfcD_model_posDef (memory : ℕ → ℕ) (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (hm : ∀ i ≤ N, 0 < i → 0 < memory i)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcDMethod memory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    (windowModel (selectedDirectionWindow memory trial
      (oneGradientRun (xrfcDMethod memory trial) (fun _ => Q) g k))).PosDef := by
  -- Actual replay identifies this implemented model with a genuine positive quadratic Gram matrix.
  have hr := (xrfcD_state memory trial Q hQ hpos g N hg hm ht k hk).1
  have hW : selectedDirectionWindow memory trial (oneGradientRun (xrfcDMethod memory trial) (fun _ => Q) g k)=
      directionWindow Q g k (memory k) := by
    unfold selectedDirectionWindow
    rw [hr,oneGradientRun_length]
    rfl
  rw [hW,windowModel_quadratic _ Q hQ (directionWindow_images Q g k (memory k))]
  exact operatorGram_posDef Q hQ hpos (directionWindow_independent Q hQ hpos g k (memory k)
    (fun i hi => hg i (hi.trans_le hk)))

/-- The actual evaluated XRFC-D point is the true virtual CG point plus its actual trial direction step.
Use: retain the source's distinction between observed trial points and unevaluated virtual outputs.
Article: main_krylov, lem:consistent(c), x_(k+1)=x_k⁰+τ_kd_k⁰.
Proof: substitute the proved actual virtual point and direction into the actual one-gradient step. -/
theorem xrfcD_evaluated (memory : ℕ → ℕ) (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (hm : ∀ i ≤ N, 0 < i → 0 < memory i)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcDMethod memory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k<N) :
    let m := xrfcDMethod memory trial
    let H := oneGradientRun m (fun _ => Q) g k
    (oneGradientRun m (fun _ => Q) g (k+1)).displacement=
      CG.displacement Q g k+trial H • CG.direction Q g k := by
  -- Add the actual virtual correction and trial to the actual current physical point.
  let m := xrfcDMethod memory trial
  let H := oneGradientRun m (fun _ => Q) g k
  have hv := xrfcD_reference memory trial Q hQ hpos g N hg hm ht k hk.le
  have hp := hv.1
  change H.displacement+virtualCorrection (selectedDirectionWindow memory trial H) H.gradient=_ at hp
  change (virtualCorrection (selectedDirectionWindow memory trial H) H.gradient+
    trial H • windowDirection (selectedDirectionWindow memory trial H)
      (virtualGradient (selectedDirectionWindow memory trial H) H.gradient))+H.displacement=_
  rw [hv.2.2,← hp]
  abel

/-- The next actual XRFC-D virtual correction recovers exactly the missed true CG line component.
Use: even a one-pair direction window corrects every nonzero actual trial.
Article: main_krylov, lem:consistent(c), Sw=(α_k−τ_k)d_k⁰.
Proof: subtract the actual evaluated displacement from the actual next virtual CG displacement. -/
theorem xrfcD_next_correction (memory : ℕ → ℕ) (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (hm : ∀ i ≤ N, 0 < i → 0 < memory i)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcDMethod memory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k<N) :
    let m := xrfcDMethod memory trial
    let H := oneGradientRun m (fun _ => Q) g k
    m.output (oneGradientRun m (fun _ => Q) g (k+1))=
      (CG.length Q g k-trial H) • CG.direction Q g k := by
  -- Both points are outputs of the actual data-only execution already proved above.
  have hv := (xrfcD_reference memory trial Q hQ hpos g N hg hm ht (k+1) (by omega)).1
  have he := xrfcD_evaluated memory trial Q hQ hpos g N hg hm ht k hk
  dsimp only at hv he ⊢
  rw [OneGradientMethod.outputDisplacement,he,CG.displacement_succ] at hv
  have hh := congrArg (fun v => v-(CG.displacement Q g k+trial (oneGradientRun (xrfcDMethod memory trial)
    (fun _ => Q) g k) • CG.direction Q g k)) hv
  rw [add_sub_cancel_left] at hh
  rw [hh,sub_smul]
  abel

/-- Actual newest-retaining XRFC-D reaches the true solution as its unevaluated output after the active-atom cycle with exactly N+1 gradients.
Use: full memory and every positive sliding direction window have the source's true one-gradient termination and cost.
Article: main_krylov, lem:consistent(c), x̂_n=x_* after n+1 gradients.
Proof: actual active-spectrum nonstagnation supplies the complete real execution
invariant; true terminal CG balance identifies the output gradient and the real query transcript gives its exact cost. -/
theorem xrfcD_terminates {n : ℕ} (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (memory : ℕ → ℕ) (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hm : ∀ i ≤ referenceAtomCount base hb g, 0 < i → 0 < memory i)
    (ht : ∀ i<referenceAtomCount base hb g,
      trial (oneGradientRun (xrfcDMethod memory trial) (fun _ => cgOperator base) g i)≠0) :
    let m := xrfcDMethod memory trial
    let H := oneGradientRun m (fun _ => cgOperator base) g (referenceAtomCount base hb g)
    m.outputDisplacement H=CG.displacement (cgOperator base) g (referenceAtomCount base hb g) ∧
      m.outputGradient (cgOperator base) H=0 ∧ oneGradientCost H=referenceAtomCount base hb g+1 := by
  -- No observation of the terminal virtual output appears in the actual transcript.
  let m := xrfcDMethod memory trial
  let H := oneGradientRun m (fun _ => cgOperator base) g (referenceAtomCount base hb g)
  have hv := (xrfcD_reference memory trial _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2
    g _ (cg_nonstagnation base hb g) hm ht _ le_rfl).1
  refine ⟨hv,?_,oneGradientCost_run m _ g _⟩
  change H.gradient+cgOperator base (m.output H)=0
  rw [oneGradientRun_quadratic_gradient]
  change g+cgOperator base H.displacement+cgOperator base (m.output H)=0
  rw [add_assoc,← map_add,← OneGradientMethod.outputDisplacement,hv,← CG.gradient_displacement]
  exact cg_terminates base hb g

end
end krylov.Methods
