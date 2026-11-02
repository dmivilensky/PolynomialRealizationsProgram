import krylov.Cancellation.DCOneGradientState
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(b), complete actual one-gradient DC quadratic trajectory.
Use: obtain the original positive t_k recurrence, genuine evaluated CG-line
points, old-flag residual orthogonality and actual XRFC trajectory dictionary.
Source: the proved original execution/basis induction, true native query
identity and genuine CG quadratic/Galerkin orthogonality.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual effective CG-line length of the one-gradient DC evaluated point.
Use: the chosen native estimate is multiplied by the derived actual incoming factor.
Article: main_krylov, thm:dcs(b), t_k. -/
def dcEvaluatedLength (estimate : History E → ℝ) (Q : E →L[ℝ] E) (g : E) (k : ℕ) : ℝ :=
  estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g k)*dcIncomingFactor estimate Q g k

/-- The genuine initial effective length is exactly the original chosen estimate.
Use: initialize the printed t_k recurrence on actual data.
Article: main_krylov, thm:dcs(b).
Proof: the proved actual incoming-factor definition starts at one. -/
theorem dc_evaluated_length_zero (estimate : History E → ℝ) (Q : E →L[ℝ] E) (g : E) :
    dcEvaluatedLength estimate Q g 0=
      estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g 0) := by
  rw [dcEvaluatedLength,dcIncomingFactor,mul_one]

/-- The original effective evaluated lengths have exactly the printed true
chosen-estimate/preceding-CG-line recurrence.
Use: no line length is prescribed independently of its real observed history.
Article: main_krylov, thm:dcs(b), t_(k+1)=tau_(k+1)t_k/alpha_k.
Proof: substitute the genuine actual incoming-factor recurrence and collect real scalars. -/
theorem dc_evaluated_length_succ (estimate : History E → ℝ) (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    dcEvaluatedLength estimate Q g (k+1)=
      estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g (k+1))*
        dcEvaluatedLength estimate Q g k/CG.length Q g k := by
  simp only [dcEvaluatedLength,dcIncomingFactor]
  ring

/-- Every actual one-gradient DC evaluated point lies at its derived positive
length on the genuine current CG line and its real gradient annihilates the
entire preceding true CG flag.
Use: close the original full-memory quadratic trajectory without assuming
CG-consistency of the unevaluated output or a reference-step formula.
Article: main_krylov, thm:dcs(b), x_(k+1)=x_k^0+t_k d_k^0 and g_(k+1) perpendicular K_k.
Proof: the real execution induction gives the genuine independent full flag,
positive incoming factor and actual gradient decomposition. Native Galerkin
and tilted-trial identities identify the true query; actual quadratic balance
and genuine CG residual/conjugacy orthogonality give the source's full old-flag pairing. -/
theorem dc_one_gradient_evaluated (estimate : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0<estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g i))
    (k : ℕ) (hk : k<N) :
    0<dcEvaluatedLength estimate Q g k ∧
      (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g (k+1)).displacement=
        CG.displacement Q g k+dcEvaluatedLength estimate Q g k • CG.direction Q g k ∧
      ∀ v∈directionFlag Q g k,inner ℝ v
        (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g (k+1)).gradient=0 := by
  let m := dcSlideOneGradient fullMemory estimate
  let H := oneGradientRun m (fun _ => Q) g k
  obtain ⟨hrho,hLI,hspan,v,hv,hgrad⟩ := dc_one_gradient_state estimate Q hQ hpos g N hpre ht k hk.le
  have hprefix : ∀ i<k,CG.gradient Q g i≠0 := fun i hi => hpre i (hi.trans hk)
  have hy : ∀ i,windowImages H.pairs i=Q (windowSteps H.pairs i) := fun i =>
    oneGradientRun_pairs_quadratic m Q g k (H.pairs.get i) (List.get_mem _ i)
  have hstep := dc_one_gradient_step_from_flag estimate Q hQ hpos g k hprefix H
    (oneGradientRun_quadratic_gradient m Q g k) hy hLI hspan (dcIncomingFactor estimate Q g k) v hv hgrad (ht k hk).ne'
  have hpoint : (oneGradientRun m (fun _ => Q) g (k+1)).displacement=
      CG.displacement Q g k+dcEvaluatedLength estimate Q g k • CG.direction Q g k := by
    change m.step H+H.displacement=_
    rw [hstep]
    change (CG.displacement Q g k-H.displacement+
      dcEvaluatedLength estimate Q g k • CG.direction Q g k)+H.displacement=_
    abel
  refine ⟨mul_pos (ht k hk) hrho,hpoint,?_⟩
  have hnext : (oneGradientRun m (fun _ => Q) g (k+1)).gradient=
      CG.gradient Q g k+dcEvaluatedLength estimate Q g k • Q (CG.direction Q g k) := by
    rw [oneGradientRun_quadratic_gradient,hpoint,map_add,map_smul,CG.gradient_displacement]
    abel
  intro w hw
  rw [hnext,inner_add_right,real_inner_smul_right,
    directionFlag_gradient_orthogonal Q hQ hpos g k hprefix hw,
    directionFlag_conjugate Q hQ hpos g k hprefix hw,mul_zero,add_zero]

/-- A genuine data-only XRFC trial realizing the actual one-gradient DC
effective reference lengths on the same positive quadratic.
Use: compare the original actual evaluated trajectories under the same true
relative CG-line trial errors, without an assumed trial sequence field.
Article: main_krylov, thm:dcs(b). -/
def dcReferenceXRFCTrial (estimate : History E → ℝ) (Q : E →L[ℝ] E) (g : E) : History E → ℝ :=
  fun H => dcEvaluatedLength estimate Q g H.records.length

/-- The actual one-gradient DC quadratic evaluated trajectory is exactly
the genuine full-memory XRFC trajectory with the same effective reference trials.
Use: the source's reference comparison concerns real original executors.
Article: main_krylov, thm:dcs(b).
Proof: actual DC execution proves every effective length positive. The real
XRFC history reads precisely its true iteration count, so genuine full-memory
virtual consistency gives exactly the same actual evaluated CG-line point. -/
theorem dc_one_gradient_matches_xrfc_reference (estimate : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0<estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g i))
    (k : ℕ) (hk : k<N) :
    (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g (k+1)).displacement=
      (oneGradientRun (xrfcMethod fullMemory (dcReferenceXRFCTrial estimate Q g)) (fun _ => Q) g (k+1)).displacement := by
  have htrial : ∀ i<N,dcReferenceXRFCTrial estimate Q g (oneGradientRun
      (xrfcMethod fullMemory (dcReferenceXRFCTrial estimate Q g)) (fun _ => Q) g i)≠0 := by
    intro i hi
    rw [dcReferenceXRFCTrial,oneGradientRun_length]
    exact (dc_one_gradient_evaluated estimate Q hQ hpos g N hpre ht i hi).1.ne'
  have hx := xrfc_full_evaluated (dcReferenceXRFCTrial estimate Q g) Q hQ hpos g N hpre htrial k hk
  dsimp only at hx
  rw [dcReferenceXRFCTrial,oneGradientRun_length] at hx
  exact (dc_one_gradient_evaluated estimate Q hQ hpos g N hpre ht k hk).2.1.trans hx.symm

end
end krylov.Cancellation
