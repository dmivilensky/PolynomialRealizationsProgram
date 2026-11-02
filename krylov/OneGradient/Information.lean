import krylov.Methods.InformationSpan
import krylov.Methods.OneGradientCoordinates
import krylov.Reference.PolynomialAction
set_option autoImplicit false
/-!
Article: main_krylov, apE:info.
Use: prove information dependence for arbitrary nonanticipating span-restricted
one-gradient methods, without a CG-consistency assumption.
Source: the classical polynomial Krylov flag and induction on the actual
observed history; no hidden matrix action enters either decision function.
-/

/-!
Article: krylov, Lemma C.7 [apE:info].

A single old-flag vector and last-direction coefficient are chosen before every completion; the
actual histories and final query point agree.
OneGradientSpanRestricted is the observed-span condition in the article information class; CG
consistency is not assumed for this information lemma.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference Polynomial
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual polynomial Krylov flag equals the span of physical operator powers.
Use: information arguments need no positivity or nonstagnation hypothesis.
Article: main_krylov, apE:info.
Proof: reuse the degree-graded polynomial spanning theorem with monomials. -/
theorem krylov_space_powers (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    CG.krylovSpace Q g k=Submodule.span ℝ ((fun i : ℕ => (Q^i) g) '' Set.Iio k) := by
  have h := CG.polynomialAction_span Q g (fun i => X^i) k (by intro i _; simp)
  simpa only [CG.polynomialAction,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
    ContinuousLinearMap.coe_coe,ContinuousLinearMap.apply_apply,map_pow,aeval_X] using h

/-- Krylov flags are increasing even after exhaustion.
Use: place every actual earlier observation in the current information flag.
Article: main_krylov, apE:info.
Proof: every physical power in the shorter prefix belongs to the longer one. -/
theorem krylov_space_mono (Q : E →L[ℝ] E) (g : E) {j k : ℕ} (hjk : j≤k) :
    CG.krylovSpace Q g j≤CG.krylovSpace Q g k := by
  rw [krylov_space_powers,krylov_space_powers]
  apply Submodule.span_mono
  rintro _ ⟨i,hi,rfl⟩
  exact ⟨i,lt_of_lt_of_le hi hjk,rfl⟩

/-- The initial gradient belongs to every positive Krylov prefix.
Use: initialize arbitrary-policy information-span induction.
Article: main_krylov, apE:info.
Proof: the zeroth physical operator power is the identity. -/
theorem initial_mem_krylov (Q : E →L[ℝ] E) (g : E) {k : ℕ} (hk : 0<k) :
    g∈CG.krylovSpace Q g k := by
  rw [krylov_space_powers]
  apply Submodule.subset_span
  exact ⟨0,hk,by simp⟩

/-- A single physical operator action raises the Krylov prefix by one.
Use: control the actual returned gradient after each new evaluated step.
Article: main_krylov, apE:info.
Proof: apply linearity to the physical power generators. -/
theorem action_mem_krylov (Q : E →L[ℝ] E) (g : E) (k : ℕ)
    {v : E} (hv : v∈CG.krylovSpace Q g k) : Q v∈CG.krylovSpace Q g (k+1) := by
  rw [krylov_space_powers] at hv ⊢
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i,hi,rfl⟩ := hv
    apply Submodule.subset_span
    refine ⟨i+1,Nat.succ_lt_succ hi,?_⟩
    simp only [pow_succ',mul_apply_eq_comp]
  | zero => simpa only [map_zero] using (Submodule.zero_mem _)
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c v _ hv => simpa only [map_smul] using Submodule.smul_mem _ c hv

private theorem observed_initial (H : History E) : H.initial∈H.observedSpan := by
  apply Submodule.subset_span
  exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))

private theorem observed_pair_step (H : History E) (p : E × E) (hp : p∈H.pairs) :
    p.1∈H.observedSpan := by
  apply Submodule.subset_span
  exact Or.inl (Or.inl (Or.inr ⟨p,hp,rfl⟩))

private theorem observed_pair_image (H : History E) (p : E × E) (hp : p∈H.pairs) :
    p.2∈H.observedSpan := by
  apply Submodule.subset_span
  exact Or.inl (Or.inr ⟨p,hp,rfl⟩)

private theorem observed_record (H : History E) (r : IterationRecord E) (hr : r∈H.records)
    (v : E) (hv : v=r.direction ∨ v=r.probe ∨ ∃ p∈r.corrections,v=p.1 ∨ v=p.2) :
    v∈H.observedSpan := by
  apply Submodule.subset_span
  exact Or.inr ⟨r,hr,hv⟩

/-- One actual one-gradient update uses only the previous observed span and its
chosen step and returned operator image.
Use: exclude fictitious direction/probe observations from information lower bounds.
Article: main_krylov, apE:info.
Proof: inspect the real prepended record. Its auxiliary fields and correction
list are zero; its only new secant is the actual queried operator image. -/
theorem one_gradient_advance_observed (m : OneGradientMethod E) (Q : E →L[ℝ] E)
    (H : History E) (K : Submodule ℝ E) (hH : H.observedSpan≤K)
    (hs : m.step H∈K) (hy : Q (m.step H)∈K) :
    (oneGradientAdvance m Q H).observedSpan≤K := by
  have hg := hH H.gradient_mem_observedSpan
  have hp : (oneGradientAdvance m Q H).pairs=(m.step H,Q (m.step H))::H.pairs := by
    change (m.step H,H.gradient+Q (m.step H)-H.gradient)::H.pairs=_
    rw [add_sub_cancel_left]
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ((hv|hv)|hv)|hv
  · rcases hv with hv|hv
    · subst v
      exact hH (observed_initial H)
    · subst v
      exact K.add_mem hg hy
  · obtain ⟨p,hp',rfl⟩ := hv
    rw [hp] at hp'
    rcases List.mem_cons.mp hp' with rfl|h
    · exact hs
    · exact hH (observed_pair_step H p h)
  · obtain ⟨p,hp',rfl⟩ := hv
    rw [hp] at hp'
    rcases List.mem_cons.mp hp' with rfl|h
    · exact hy
    · exact hH (observed_pair_image H p h)
  · obtain ⟨r,hr,hv⟩ := hv
    change r∈(⟨0,0,m.step H,H.gradient+Q (m.step H),[]⟩::H.records) at hr
    rcases List.mem_cons.mp hr with rfl|hr
    · rcases hv with rfl|rfl|⟨p,hp,_⟩
      · exact K.zero_mem
      · exact K.zero_mem
      · exact False.elim (List.not_mem_nil hp)
    · exact hH (observed_record H r hr v hv)

/-- Every actual observation of an arbitrary admissible one-gradient method
belongs to the appropriate reference Krylov flag.
Use: the information lower bound applies to methods without CG consistency.
Article: main_krylov, apE:info.
Proof: induct over actual histories, using the source's evaluated-step span
restriction before applying the new unknown operator action. -/
theorem one_gradient_observed_krylov (m : OneGradientMethod E)
    (hm : OneGradientSpanRestricted m) (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    (oneGradientRun m (fun _ => Q) g k).observedSpan≤CG.krylovSpace Q g (k+1) := by
  induction k with
  | zero =>
    apply Submodule.span_le.mpr
    intro v hv
    simp only [oneGradientRun,History.gradient,History.pairs,recordPairs,
      Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_image,
      Set.mem_ofPred_eq,List.not_mem_nil,false_and,exists_false,or_false] at hv
    have hv' : v=g := hv.elim id id
    subst v
    exact initial_mem_krylov Q g (by omega)
  | succ k ih =>
    have hs := ih (hm _)
    exact one_gradient_advance_observed m Q _ _
      (ih.trans (krylov_space_mono Q g (Nat.le_succ _)))
      (krylov_space_mono Q g (Nat.le_succ _) hs) (action_mem_krylov Q g (k+1) hs)

/-- Every actually evaluated step is in the next Krylov flag.
Use: the final step is selected before the missing last curvature is observed.
Article: main_krylov, apE:info.
Proof: apply the proved observed-history bound to the actual span-restricted step. -/
theorem one_gradient_step_krylov (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    oneGradientStep m (fun _ => Q) g k∈CG.krylovSpace Q g (k+1) :=
  one_gradient_observed_krylov m hm Q g k (hm _)

/-- Every actual returned gradient is in the next Krylov flag.
Use: identify the full nonanticipating transcript, not only its evaluated points.
Article: main_krylov, apE:info.
Proof: the current gradient is one of the actual observed-span generators. -/
theorem one_gradient_gradient_krylov (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    oneGradientGradient m (fun _ => Q) g k∈CG.krylovSpace Q g (k+1) :=
  one_gradient_observed_krylov m hm Q g k (History.gradient_mem_observedSpan _)

/-- The actual evaluated iterate lies in the Krylov flag of its evaluation count.
Use: no consistency or independence of the method's own steps is assumed.
Article: main_krylov, apE:info.
Proof: sum the actual evaluated steps and use their proved prefix membership. -/
theorem one_gradient_displacement_krylov (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    (oneGradientRun m (fun _ => Q) g k).displacement∈CG.krylovSpace Q g k := by
  rw [oneGradientRun_displacement_sum]
  apply Submodule.sum_mem
  intro i hi
  exact krylov_space_mono Q g (Finset.mem_range.mp hi) (one_gradient_step_krylov m hm Q g i)

/-- Operators with the same actual Krylov restriction give the same complete
one-gradient history up to the last unqueried direction.
Use: the missing-pivot lower bound holds for arbitrary data-only policies.
Article: main_krylov, apE:info.
Proof: at every earlier query, the true chosen step lies in the common action
space. Equal complete histories force equal next decisions and returned gradients. -/
theorem one_gradient_information_history (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q C : E →L[ℝ] E) (g : E) (N : ℕ)
    (hact : ∀ v∈CG.krylovSpace Q g N,C v=Q v) (k : ℕ) (hk : k≤N) :
    oneGradientRun m (fun _ => C) g k=oneGradientRun m (fun _ => Q) g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [oneGradientRun,oneGradientRun,ih (by omega)]
    have hs := krylov_space_mono Q g (show k+1≤N by omega) (one_gradient_step_krylov m hm Q g k)
    have he := hact _ hs
    unfold oneGradientAdvance
    dsimp only
    change C (m.step (oneGradientRun m (fun _ => Q) g k))=Q (m.step (oneGradientRun m (fun _ => Q) g k)) at he
    rw [he]

/-- The final evaluated displacement is common to every completion of the
last unqueried curvature, even though the gradient returned there may differ.
Use: isolate exactly which last decisions precede the missing-pivot observation.
Article: main_krylov, apE:info.
Proof: both actual steps are functions of the proved common preceding history. -/
theorem one_gradient_information_last_step (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q C : E →L[ℝ] E) (g : E) (N : ℕ)
    (hact : ∀ v∈CG.krylovSpace Q g N,C v=Q v) :
    oneGradientStep m (fun _ => C) g N=oneGradientStep m (fun _ => Q) g N := by
  exact congrArg m.step (one_gradient_information_history m hm Q C g N hact N le_rfl)

/-- The final evaluated point is fixed across all completions of the known
operator restriction, although its newly returned gradient need not be fixed.
Use: distinguish the final evaluated point from the subsequent output decision.
Article: main_krylov, apE:info.
Proof: the preceding complete history and the last chosen step are common. -/
theorem one_gradient_information_last_point (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q C : E →L[ℝ] E) (g : E) (N : ℕ)
    (hact : ∀ v∈CG.krylovSpace Q g N,C v=Q v) :
    (oneGradientRun m (fun _ => C) g (N+1)).displacement=
      (oneGradientRun m (fun _ => Q) g (N+1)).displacement := by
  change oneGradientStep m (fun _ => C) g N+(oneGradientRun m (fun _ => C) g N).displacement=
    oneGradientStep m (fun _ => Q) g N+(oneGradientRun m (fun _ => Q) g N).displacement
  rw [one_gradient_information_last_step m hm Q C g N hact,
    one_gradient_information_history m hm Q C g N hact N le_rfl]

/-- A nondegenerate Krylov prefix splits into its old flag and its final CG direction.
Use: derive the article's scalar last-step parameter from the genuine reference.
Article: main_krylov, apE:info.
Proof: the proved actual CG direction basis spans the flag; separate its newest
generator and use the exact sum-of-submodules membership criterion. -/
theorem krylov_last_direction_decomposition (Q : E →L[ℝ] E) (g : E) (N : ℕ)
    (hl : ∀ i<N+1,CG.length Q g i≠0) (w : E) (hw : w∈CG.krylovSpace Q g (N+1)) :
    ∃ v∈CG.krylovSpace Q g N,∃ t : ℝ,w=v+t • CG.direction Q g N := by
  have hflag := CG.krylovSpace_eq_span_directions Q g (N+1) hl
  have hold := CG.krylovSpace_eq_span_directions Q g N (fun i hi => hl i (by omega))
  have hle : CG.krylovSpace Q g (N+1)≤
      CG.krylovSpace Q g N ⊔ Submodule.span ℝ {CG.direction Q g N} := by
    rw [hflag]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    by_cases h : i<N
    · apply Submodule.mem_sup_left
      rw [hold]
      exact Submodule.subset_span ⟨i,h,rfl⟩
    · have he : i=N := by change i<N+1 at hi; omega
      subst i
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  obtain ⟨v,hv,z,hz,he⟩ := Submodule.mem_sup.mp (hle hw)
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨v,hv,t,he.symm⟩

/-- The common final evaluated point of any admissible one-gradient method has
the article's old-flag plus last-CG-direction representation, with coefficients
chosen once before all hidden completions.
Use: supply the quantified information reduction needed by the lower bound
without imposing CG consistency on the candidate method.
Article: main_krylov, apE:info.
Proof: subtract the actual reference iterate inside the Krylov flag, decompose
once, then transfer the common final evaluated point to every completion. -/
theorem one_gradient_information_decomposition (m : OneGradientMethod E)
    (hm : OneGradientSpanRestricted m) (Q : E →L[ℝ] E) (g : E) (N : ℕ)
    (hl : ∀ i<N+1,CG.length Q g i≠0) :
    ∃ v∈CG.krylovSpace Q g N,∃ t : ℝ,∀ C : E →L[ℝ] E,
      (∀ u∈CG.krylovSpace Q g N,C u=Q u) →
      (oneGradientRun m (fun _ => C) g (N+1)).displacement-CG.displacement Q g N=
        v+t • CG.direction Q g N := by
  have href : CG.displacement Q g N∈CG.krylovSpace Q g (N+1) := by
    rw [CG.displacement,CG.krylovSpace_eq_span_directions Q g (N+1) hl]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i,show i<N+1 from (Finset.mem_range.mp hi).trans (Nat.lt_succ_self N),rfl⟩
  obtain ⟨v,hv,t,he⟩ := krylov_last_direction_decomposition Q g N hl _
    (Submodule.sub_mem _ (one_gradient_displacement_krylov m hm Q g (N+1)) href)
  refine ⟨v,hv,t,fun C hC => ?_⟩
  rw [one_gradient_information_last_point m hm Q C g N hC]
  exact he

end
end krylov.OneGradient
