import krylov.Methods.VirtualReference

/-!
Article: Lemma A.2 [lem:consistent] of krylov.tex.
Use: prove the actual stored steps form a complete independent CG flag for
every nonzero trial sequence, then derive its real virtual/evaluated/output identities.
Source: the actual virtual Galerkin solve and nonzero-trial basis induction.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual full-memory XRFC recorded steps form an independent basis of the genuine reference CG flag.
Use: all virtual model domains and actual reference identities follow from an executed basis invariant.
Article: main_krylov, lem:consistent(b), span S_k=K_k.
Proof: the computed virtual solve identifies the actual current direction;
its nonzero true-curvature component lies outside the old flag, and a nonzero actual trial adds it to the real recorded basis. -/
theorem xrfc_full_basis (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g k
    LinearIndependent ℝ (windowSteps H.pairs) ∧ pairSpan H.pairs=directionFlag Q g k := by
  -- The actual independent stored basis is established before identifying any later virtual iterate.
  induction k with
  | zero =>
    constructor
    · change LinearIndependent ℝ (fun i : Fin 0 => windowSteps ([] : List (E × E)) i)
      exact linearIndependent_empty_type
    · change pairSpan ([] : List (E × E))=directionFlag Q g 0
      rw [directionFlag_zero]
      simp only [pairSpan, windowSteps_range, List.not_mem_nil, Set.ofPred_false, Set.image_empty, Submodule.span_empty]
  | succ k ih =>
    let m := xrfcMethod fullMemory trial
    let H := oneGradientRun m (fun _ => Q) g k
    have ht' : trial H≠0 := ht k (by omega)
    have hs := ih (by omega)
    have hpre : ∀ i<k, CG.gradient Q g i≠0 := fun i hi => hg i (by omega)
    have hy : ∀ i, windowImages H.pairs i=Q (windowSteps H.pairs i) :=
      fun i => oneGradientRun_pairs_quadratic m Q g k (H.pairs.get i) (List.get_mem _ i)
    have hv := virtual_reference_basis H Q hQ hpos g k hpre
      (oneGradientRun_quadratic_gradient m Q g k) hy hs.1 hs.2
    have hu : CG.displacement Q g k-H.displacement∈directionFlag Q g k := by
      rw [← hs.2]
      rw [← hv.1]
      exact combine_mem_span _ _
    have hstep : m.step H=(CG.displacement Q g k-H.displacement)+trial H • CG.direction Q g k := by
      change virtualCorrection (selectedWindow fullMemory H) H.gradient+
        trial H • windowDirection (selectedWindow fullMemory H) (virtualGradient (selectedWindow fullMemory H) H.gradient)=_
      rw [selectedWindow_full, hv.1, hv.2.2]
    have hd : CG.direction Q g k∉directionFlag Q g k := by
      intro hd
      have he := directionFlag_conjugate Q hQ hpos g k hpre hd
      have hn := (CG.invariant_line_pos Q hpos g k (CG.invariant Q hQ hpos g k hpre) (hg k (by omega))).1
      exact (hpos _ hn).ne' he
    have hnew : m.step H∉pairSpan H.pairs := by
      rw [hs.2, hstep]
      intro hh
      have hb := Submodule.smul_mem (directionFlag Q g k) (trial H)⁻¹
        (Submodule.sub_mem _ hh hu)
      apply hd
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht', one_smul] at hb
      exact hb
    change LinearIndependent ℝ (windowSteps (oneGradientRun m (fun _ => Q) g (k+1)).pairs) ∧
      pairSpan (oneGradientRun m (fun _ => Q) g (k+1)).pairs=directionFlag Q g (k+1)
    rw [oneGradientRun_pairs_succ]
    constructor
    · rw [windowSteps_cons]
      exact hs.1.finCons hnew
    · rw [pairSpan_cons, hs.2, hstep, trial_span_extension _ _ _ hu _ ht', directionFlag_succ]

/-- Actual full-memory XRFC has the true virtual CG point, gradient and direction through the complete nonstagnating prefix.
Use: arbitrary actual nonzero trial choices are allowed; no line-search equality is assumed.
Article: main_krylov, lem:consistent(b), x̂_k=x_k⁰, ĝ_k=g_k⁰, d_k=d_k⁰.
Proof: the actual execution theorem supplies the genuine independent stored
CG basis, and computed virtual Galerkin uniqueness supplies all three actual identities. -/
theorem xrfc_full_reference (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let m := xrfcMethod fullMemory trial
    let H := oneGradientRun m (fun _ => Q) g k
    m.outputDisplacement H=CG.displacement Q g k ∧
      virtualGradient H.pairs H.gradient=CG.gradient Q g k ∧
      windowDirection H.pairs (virtualGradient H.pairs H.gradient)=CG.direction Q g k := by
  -- The same genuine computed virtual solve serves as the final unevaluated output.
  let m := xrfcMethod fullMemory trial
  let H := oneGradientRun m (fun _ => Q) g k
  have hs := xrfc_full_basis trial Q hQ hpos g N hg ht k hk
  have hy : ∀ i, windowImages H.pairs i=Q (windowSteps H.pairs i) :=
    fun i => oneGradientRun_pairs_quadratic m Q g k (H.pairs.get i) (List.get_mem _ i)
  have hv := virtual_reference_basis H Q hQ hpos g k (fun i hi => hg i (hi.trans_le hk))
    (oneGradientRun_quadratic_gradient m Q g k) hy hs.1 hs.2
  refine ⟨?_,hv.2⟩
  change H.displacement+virtualCorrection (selectedWindow fullMemory H) H.gradient=_
  rw [selectedWindow_full, hv.1, add_sub_cancel]

/-- The actual full-memory quadratic XRFC latest-information model is positive definite throughout its actual active prefix.
Use: every implemented virtual and conjugacy model inverse has its genuine domain, including the final unevaluated output.
Article: main_krylov, lem:consistent(b), SᵀAS positive definite.
Proof: actual observed secants are true quadratic images and the actual
nonzero-trial basis induction proves independence of the real recorded steps. -/
theorem xrfc_full_model_posDef (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    (windowModel (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g k).pairs).PosDef := by
  let m := xrfcMethod fullMemory trial
  let H := oneGradientRun m (fun _ => Q) g k
  have hy : ∀ i, windowImages H.pairs i=Q (windowSteps H.pairs i) :=
    fun i => oneGradientRun_pairs_quadratic m Q g k (H.pairs.get i) (List.get_mem _ i)
  rw [windowModel_quadratic H.pairs Q hQ hy]
  exact operatorGram_posDef Q hQ hpos (xrfc_full_basis trial Q hQ hpos g N hg ht k hk).1

/-- The actual full-memory XRFC evaluated point is the virtual CG point plus its actual trial direction step.
Use: evaluated and virtual points remain distinct in the actual one-gradient execution.
Article: main_krylov, lem:consistent(b), x_(k+1)=x_k⁰+τ_kd_k⁰.
Proof: the actual recorded step is the computed virtual correction plus the
actual trial; the proved virtual point and direction identities identify its total physical displacement. -/
theorem xrfc_full_evaluated (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k<N) :
    let m := xrfcMethod fullMemory trial
    let H := oneGradientRun m (fun _ => Q) g k
    (oneGradientRun m (fun _ => Q) g (k+1)).displacement=
      CG.displacement Q g k+trial H • CG.direction Q g k := by
  -- The actual next point includes its one evaluated query and does not spend an output query.
  let m := xrfcMethod fullMemory trial
  let H := oneGradientRun m (fun _ => Q) g k
  have hv := xrfc_full_reference trial Q hQ hpos g N hg ht k hk.le
  have hpoint : H.displacement+virtualCorrection H.pairs H.gradient=CG.displacement Q g k := by
    have hv' := hv.1
    change H.displacement+virtualCorrection (selectedWindow fullMemory H) H.gradient=_ at hv'
    simpa only [selectedWindow_full] using hv'
  change m.step H+H.displacement=_
  change (virtualCorrection (selectedWindow fullMemory H) H.gradient+
    trial H • windowDirection (selectedWindow fullMemory H) (virtualGradient (selectedWindow fullMemory H) H.gradient))+
      H.displacement=_
  rw [selectedWindow_full, hv.2.2, ← hpoint]
  abel

/-- The actual next full-memory XRFC output correction recovers exactly the missed true CG line component.
Use: arbitrary nonzero trials still generate the same virtual CG trajectory.
Article: main_krylov, lem:consistent(b), x̂_(k+1)−x_(k+1)=(α_k−τ_k)d_k⁰.
Proof: subtract the proved actual evaluated displacement from the proved next actual virtual CG point. -/
theorem xrfc_full_next_correction (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k<N) :
    let m := xrfcMethod fullMemory trial
    let H := oneGradientRun m (fun _ => Q) g k
    m.output (oneGradientRun m (fun _ => Q) g (k+1))=
      (CG.length Q g k-trial H) • CG.direction Q g k := by
  -- Recover the actual physical correction from the two already proved actual point identities.
  have hv := (xrfc_full_reference trial Q hQ hpos g N hg ht (k+1) (by omega)).1
  have he := xrfc_full_evaluated trial Q hQ hpos g N hg ht k hk
  dsimp only at hv he ⊢
  rw [OneGradientMethod.outputDisplacement, he, CG.displacement_succ] at hv
  have hh := congrArg (fun v => v-(CG.displacement Q g k+trial (oneGradientRun (xrfcMethod fullMemory trial)
    (fun _ => Q) g k) • CG.direction Q g k)) hv
  rw [add_sub_cancel_left] at hh
  rw [hh, sub_smul]
  abel

/-- Full-memory XRFC reaches the true quadratic solution as its unevaluated output after the actual active-atom cycle.
Use: the result includes arbitrary data-dependent nonzero trials and the true N+1-gradient cost.
Article: main_krylov, lem:consistent(b), x̂_n=x_* after n+1 gradients.
Proof: actual active-spectrum nonstagnation discharges the complete executed
basis induction; the true terminal CG residual vanishes, and quadratic output balance identifies the actual final semantic gradient. -/
theorem xrfc_full_terminates {n : ℕ} (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (ht : ∀ i<referenceAtomCount base hb g,
      trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0) :
    let m := xrfcMethod fullMemory trial
    let H := oneGradientRun m (fun _ => cgOperator base) g (referenceAtomCount base hb g)
    m.outputDisplacement H=CG.displacement (cgOperator base) g (referenceAtomCount base hb g) ∧
      m.outputGradient (cgOperator base) H=0 ∧ oneGradientCost H=referenceAtomCount base hb g+1 := by
  -- Termination concerns the actual unevaluated output, not the last evaluated trial point.
  let m := xrfcMethod fullMemory trial
  let H := oneGradientRun m (fun _ => cgOperator base) g (referenceAtomCount base hb g)
  have hv := (xrfc_full_reference trial _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2
    g _ (cg_nonstagnation base hb g) ht _ le_rfl).1
  refine ⟨hv,?_,oneGradientCost_run m _ g _⟩
  change H.gradient+cgOperator base (m.output H)=0
  rw [oneGradientRun_quadratic_gradient]
  change g+cgOperator base H.displacement+cgOperator base (m.output H)=0
  rw [add_assoc, ← map_add, ← OneGradientMethod.outputDisplacement, hv, ← CG.gradient_displacement]
  exact cg_terminates base hb g

end
end krylov.Methods
