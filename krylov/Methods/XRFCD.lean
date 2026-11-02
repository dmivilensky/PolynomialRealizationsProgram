import krylov.Methods.DirectionReplay

/-!
Article: main_krylov, lem:consistent(c), actual XRFC-D execution.
Use: prove data-only direction replay, genuine retained model domains and
virtual CG consistency together for every positive newest-retaining window.
Source: induction on the real one-gradient protocol and positive Galerkin uniqueness.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual XRFC-D reconstructs true quadratic direction images and its evaluated point differs from CG only within its actual retained direction window.
Use: the invariant validates every implemented model solve and all positive-window regimes without a presumed CG response.
Article: main_krylov, lem:consistent(c), q_k=Ad_k⁰ and newest-component virtual correction.
Proof: the computed virtual solve removes the retained off-iterate component;
the actual next gradient then reconstructs Qd by dividing its observed difference by the nonzero actual trial, and the next point differs from CG only along the newest retained direction. -/
theorem xrfcD_state (memory : ℕ → ℕ) (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (hm : ∀ i ≤ N, 0 < i → 0 < memory i)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcDMethod memory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (xrfcDMethod memory trial) (fun _ => Q) g k
    directionReplay memory trial H.initial H.records=
      executedPairs (CG.direction Q g) (fun i => Q (CG.direction Q g i)) k ∧
      ∃ v∈pairSpan (directionWindow Q g k (memory k)), H.displacement=CG.displacement Q g k+v := by
  -- Replay correctness and the physical off-iterate invariant are proved simultaneously on actual queries.
  induction k with
  | zero =>
    refine ⟨rfl,0,Submodule.zero_mem _,?_⟩
    change (0 : E)=0+0
    exact (add_zero _).symm
  | succ k ih =>
    let m := xrfcDMethod memory trial
    let H := oneGradientRun m (fun _ => Q) g k
    obtain ⟨hr,v,hv,hpoint⟩ := ih (by omega)
    have hW : selectedDirectionWindow memory trial H=directionWindow Q g k (memory k) := by
      unfold selectedDirectionWindow
      rw [hr,oneGradientRun_length]
      rfl
    have hgrad : H.gradient=CG.gradient Q g k+Q v := by
      rw [oneGradientRun_quadratic_gradient, hpoint, map_add, CG.gradient_displacement]
      abel
    have hs := directionWindow_virtual Q hQ hpos g k (memory k)
      (fun i hi => hg i (by omega)) (hm k (by omega)) v hv
    have heval : (oneGradientRun m (fun _ => Q) g (k+1)).displacement=
        CG.displacement Q g k+trial H • CG.direction Q g k := by
      change m.step H+H.displacement=_
      change (virtualCorrection (selectedDirectionWindow memory trial H) H.gradient+
        trial H • windowDirection (selectedDirectionWindow memory trial H)
          (virtualGradient (selectedDirectionWindow memory trial H) H.gradient))+H.displacement=_
      rw [hW,hgrad,hs.1,hs.2.2,hpoint]
      abel
    have hobs : H.gradient+Q (m.step H)-CG.gradient Q g k=trial H • Q (CG.direction Q g k) := by
      change H.gradient+Q (virtualCorrection (selectedDirectionWindow memory trial H) H.gradient+
        trial H • windowDirection (selectedDirectionWindow memory trial H)
          (virtualGradient (selectedDirectionWindow memory trial H) H.gradient))-CG.gradient Q g k=_
      rw [hW,hgrad,hs.1,hs.2.2,map_add,map_smul,map_neg]
      abel
    constructor
    · change directionReplay memory trial (oneGradientAdvance m Q H).initial
        (oneGradientAdvance m Q H).records=_
      rw [directionReplay_advance]
      change (windowDirection (selectedDirectionWindow memory trial H)
        (virtualGradient (selectedDirectionWindow memory trial H) H.gradient),
        (trial H)⁻¹ • (H.gradient+Q (m.step H)-virtualGradient (selectedDirectionWindow memory trial H) H.gradient))::
          directionReplay memory trial H.initial H.records=_
      rw [hW,hgrad,hs.2.2,hs.2.1,← hgrad,hobs,smul_smul,inv_mul_cancel₀ (ht k (by omega)),one_smul,hr]
      rfl
    · refine ⟨(trial H-CG.length Q g k) • CG.direction Q g k,?_,?_⟩
      · exact Submodule.smul_mem _ _ (directionWindow_newest Q g (Nat.succ_pos _) (hm (k+1) hk (Nat.succ_pos _)))
      · rw [heval,CG.displacement_succ,sub_smul]
        abel

/-- Actual positive-window XRFC-D has the true virtual CG point, gradient and direction throughout its nonstagnating prefix.
Use: one theorem covers full memory and every fixed positive sliding direction window with arbitrary nonzero actual trials.
Article: main_krylov, lem:consistent(c), x̂_k=x_k⁰, ĝ_k=g_k⁰ and d_k=d_k⁰.
Proof: actual replay supplies the true retained reference pairs and its physical
off-iterate invariant; computed Galerkin uniqueness removes precisely that component. -/
theorem xrfcD_reference (memory : ℕ → ℕ) (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (hm : ∀ i ≤ N, 0 < i → 0 < memory i)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcDMethod memory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let m := xrfcDMethod memory trial
    let H := oneGradientRun m (fun _ => Q) g k
    let W := selectedDirectionWindow memory trial H
    m.outputDisplacement H=CG.displacement Q g k ∧
      virtualGradient W H.gradient=CG.gradient Q g k ∧
      windowDirection W (virtualGradient W H.gradient)=CG.direction Q g k := by
  -- Each quantity is the actual policy computation on its real observed history.
  let m := xrfcDMethod memory trial
  let H := oneGradientRun m (fun _ => Q) g k
  obtain ⟨hr,v,hv,hpoint⟩ := xrfcD_state memory trial Q hQ hpos g N hg hm ht k hk
  have hW : selectedDirectionWindow memory trial H=directionWindow Q g k (memory k) := by
    unfold selectedDirectionWindow
    rw [hr,oneGradientRun_length]
    rfl
  have hgrad : H.gradient=CG.gradient Q g k+Q v := by
    rw [oneGradientRun_quadratic_gradient,hpoint,map_add,CG.gradient_displacement]
    abel
  have hs := directionWindow_virtual Q hQ hpos g k (memory k)
    (fun i hi => hg i (hi.trans_le hk)) (hm k hk) v hv
  refine ⟨?_,?_,?_⟩
  · change H.displacement+virtualCorrection (selectedDirectionWindow memory trial H) H.gradient=_
    rw [hW,hgrad,hs.1,hpoint,add_neg_cancel_right]
  · rw [hW,hgrad]
    exact hs.2.1
  · rw [hW,hgrad]
    exact hs.2.2

end
end krylov.Methods
