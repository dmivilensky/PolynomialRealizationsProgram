import krylov.Methods.EvaluatedLaunch
import krylov.Methods.WindowCoordinates
import Mathlib.Data.List.GetD
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(a,b), actual evaluated-launch geometry.
Use: derive exact evaluated-point line lengths, genuine conjugate recorded
pairs and the literal diagonal latest-information model and its coefficients.
Source: original positive quadratic CG conjugacy and the implemented
Hestenes/Dixon predicted-point projection procedure.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact line length from the real evaluated point is the true CG
length along its actually computed CG direction, despite all earlier misses.
Use: the source relative trial errors really are measured from evaluated points.
Article: main_krylov, prop:classical(a).
Proof: the actual virtual correction lies in the genuine old CG flag;
conjugacy removes its entire contribution to the current line pairing. -/
theorem evaluated_launch_exact_length (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k
    lineLength H.gradient (CG.direction Q g k) (Q (CG.direction Q g k))=CG.length Q g k := by
  let method := evaluatedLaunchMethod trial
  let H := oneGradientRun method (fun _ => Q) g k
  have hs := evaluated_launch_basis trial Q hQ hpos g N hg ht k hk
  have hv := (evaluated_launch_reference trial Q hQ hpos g N hg ht k hk).2.1
  have hy : ∀ i,windowImages H.pairs i=Q (windowSteps H.pairs i) := fun i =>
    oneGradientRun_pairs_quadratic method Q g k (H.pairs.get i) (List.get_mem _ i)
  have hu : virtualCorrection H.pairs H.gradient∈directionFlag Q g k := by
    rw [← hs.2]
    exact combine_mem_span _ _
  have hconj : inner ℝ (CG.direction Q g k) (Q (virtualCorrection H.pairs H.gradient))=0 := by
    have he : inner ℝ (Q (virtualCorrection H.pairs H.gradient)) (CG.direction Q g k)=
        inner ℝ (virtualCorrection H.pairs H.gradient) (Q (CG.direction Q g k)) :=
      hQ _ _
    rw [real_inner_comm,he]
    exact directionFlag_conjugate Q hQ hpos g k (fun i hi => hg i (hi.trans_le hk)) hu
  have he : H.gradient+Q (virtualCorrection H.pairs H.gradient)=CG.gradient Q g k := by
    rw [← virtualGradient_quadratic H.pairs Q _ hy]
    exact hv
  have hpair := congrArg (fun v => inner ℝ (CG.direction Q g k) v) he
  rw [inner_add_right,hconj,add_zero] at hpair
  change -inner ℝ (CG.direction Q g k) H.gradient/inner ℝ (CG.direction Q g k) (Q (CG.direction Q g k))=_
  rw [hpair]
  rfl

/-- Every pair of distinct genuine evaluated-launch steps is A-conjugate.
Use: the real stored latest-information model is diagonal on quadratic data.
Article: main_krylov, prop:classical(b).
Proof: actual executed steps are true trial multiples of actual CG directions;
the real CG invariant supplies their exact cross-conjugacy. -/
theorem evaluated_launch_conjugate (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g i)≠0)
    (i j : ℕ) (hi : i<N) (hj : j<N) (hij : i≠j) :
    inner ℝ (oneGradientStep (evaluatedLaunchMethod trial) (fun _ => Q) g i)
      (Q (oneGradientStep (evaluatedLaunchMethod trial) (fun _ => Q) g j))=0 := by
  have h := CG.invariant Q hQ hpos g N hg
  have hc : inner ℝ (CG.direction Q g i) (Q (CG.direction Q g j))=0 := by
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact h.conjugate i j hij hj.le
    · have he : inner ℝ (Q (CG.direction Q g j)) (CG.direction Q g i)=
          inner ℝ (CG.direction Q g j) (Q (CG.direction Q g i)) := hQ _ _
      rw [real_inner_comm,he]
      exact h.conjugate j i hji hi.le
  rw [oneGradientStep,oneGradientStep,evaluated_launch_step trial Q hQ hpos g N hg ht i hi.le,
    evaluated_launch_step trial Q hQ hpos g N hg ht j hj.le,map_smul,
    real_inner_smul_left,real_inner_smul_right,hc,mul_zero,mul_zero]

/-- The actual newest-first latest-information model of the evaluated
procedure is exactly the diagonal of the genuine observed pair energies.
Use: no full-model or conjugacy assumption is supplied to the correction.
Article: main_krylov, prop:classical(b).
Proof: genuine recorded images are quadratic actions and distinct actual
recorded steps are conjugate; exact chronological getters transfer the result. -/
theorem evaluated_launch_model_diagonal (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k
    windowModel H.pairs=diagonal (fun i => inner ℝ (windowSteps H.pairs i) (windowImages H.pairs i)) := by
  let method := evaluatedLaunchMethod trial
  let H := oneGradientRun method (fun _ => Q) g k
  have hy : ∀ i,windowImages H.pairs i=Q (windowSteps H.pairs i) := fun i =>
    oneGradientRun_pairs_quadratic method Q g k (H.pairs.get i) (List.get_mem _ i)
  have hlen : H.pairs.length=k := H.pairs_length.trans (oneGradientRun_length method _ g k)
  have hs (i : Fin H.pairs.length) :
      windowSteps H.pairs i=oneGradientStep method (fun _ => Q) g (k-1-i.val) := by
    let R := executedPairs (oneGradientStep method (fun _ => Q) g)
      (fun j => Q (oneGradientStep method (fun _ => Q) g j)) k
    have he : (H.pairs.getD i.val (0,0)).1=(R.getD i.val (0,0)).1 :=
      congrArg (fun L : List (E × E) => (L.getD i.val (0,0)).1)
        (oneGradientRun_pairs_segmentOperators method (fun _ => Q) g k)
    have hi : i.val<k := by have := i.isLt;omega
    have hr : R.length=k := executedPairs_length _ _ k
    rw [List.getD_eq_get H.pairs (0,0) i,
      List.getD_eq_get R (0,0) ⟨i.val,by omega⟩] at he
    exact he.trans (congrArg Prod.fst (executedPairs_get _ _ k i.val hi))
  change windowModel H.pairs=_
  rw [windowModel_quadratic H.pairs Q hQ hy]
  ext i j
  by_cases hij : i=j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    change inner ℝ (Q (windowSteps H.pairs i)) (windowSteps H.pairs i)=
      inner ℝ (windowSteps H.pairs i) (windowImages H.pairs i)
    rw [hy]
    exact real_inner_comm _ _
  · rw [Matrix.diagonal_apply_ne _ hij]
    change inner ℝ (Q (windowSteps H.pairs i)) (windowSteps H.pairs j)=0
    rw [real_inner_comm,hs i,hs j]
    apply evaluated_launch_conjugate trial Q hQ hpos g N hg ht
    · have := i.isLt;omega
    · have := j.isLt;omega
    · intro he
      apply hij
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega

/-- The genuine evaluated-procedure correction uses the literal diagonal
observed energy reciprocals, including the original negative residual pairing.
Use: the source point/gradient projection is the actual latest-model solve.
Article: main_krylov, prop:classical(b).
Proof: substitute the proved actual diagonal model into the genuine computed
inverse coefficients and evaluate its true diagonal inverse action. -/
theorem evaluated_launch_coefficient (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k
    ∀ i,virtualCoefficients H.pairs H.gradient i=
      -inner ℝ (windowSteps H.pairs i) H.gradient/
        inner ℝ (windowSteps H.pairs i) (windowImages H.pairs i) := by
  let method := evaluatedLaunchMethod trial
  let H := oneGradientRun method (fun _ => Q) g k
  change ∀ i : Fin H.pairs.length,virtualCoefficients H.pairs H.gradient i=
    -inner ℝ (windowSteps H.pairs i) H.gradient/inner ℝ (windowSteps H.pairs i) (windowImages H.pairs i)
  let c := fun i : Fin H.pairs.length => inner ℝ (windowSteps H.pairs i) (windowImages H.pairs i)
  have hc (i : Fin H.pairs.length) : c i≠0 := by
    have hy : windowImages H.pairs i=Q (windowSteps H.pairs i) :=
      oneGradientRun_pairs_quadratic method Q g k (H.pairs.get i) (List.get_mem _ i)
    change inner ℝ (windowSteps H.pairs i) (windowImages H.pairs i)≠0
    rw [hy]
    exact (hpos _ ((evaluated_launch_basis trial Q hQ hpos g N hg ht k hk).1.ne_zero i)).ne'
  have hdiag : windowModel H.pairs=diagonal c :=
    evaluated_launch_model_diagonal trial Q hQ hpos g N hg ht k hk
  have hinv : (windowModel H.pairs)⁻¹=diagonal (fun i => (c i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [hdiag,Matrix.diagonal_mul_diagonal]
    have he : (fun i => c i*(c i)⁻¹)=(1 : Fin H.pairs.length → ℝ) :=
      funext (fun i => mul_inv_cancel₀ (hc i))
    rw [he]
    exact Matrix.diagonal_one
  intro i
  rw [virtualCoefficients,modelCoefficients,hinv]
  simp only [Pi.neg_apply,Matrix.mulVec_diagonal]
  change -((c i)⁻¹*inner ℝ (windowSteps H.pairs i) H.gradient)=_
  dsimp only [c]
  ring

end
end krylov.Methods
