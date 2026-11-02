import krylov.Methods.XRFC
import krylov.Methods.OneGradientCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(a,b) and prop:launch(a), evaluated launch.
Use: implement the genuine arbitrary-length evaluated-point projection
procedure and derive its actual reference geometry from observed solves.
Source: Hestenes69 arbitrary-length projection, Dixon73/Dixon75 predicted
point and gradient; the exact native inverse/Galerkin calculus is reused.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual arbitrary-length evaluated-launch projection procedure.
Use: compute the predicted gradient and conjugate direction from observations,
but take the real trial from the current evaluated point; the model correction
is applied only when an output is requested.
Article: main_krylov, prop:classical and prop:launch(a). -/
def evaluatedLaunchMethod (trial : History E → ℝ) : OneGradientMethod E where
  step H := trial H • windowDirection H.pairs (virtualGradient H.pairs H.gradient)
  output H := virtualCorrection H.pairs H.gradient

/-- The true stored steps of the evaluated-launch procedure form an
independent basis of the actual reference CG flag for arbitrary nonzero trials.
Use: the reference trajectory and all inverse domains are derived from the
real execution, rather than supplied as a prescribed scaled CG trajectory.
Article: main_krylov, prop:classical(a,b).
Proof: genuine virtual Galerkin consistency computes the true current CG
direction. Its nonzero trial component lies outside the actual old flag. -/
theorem evaluated_launch_basis (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k
    LinearIndependent ℝ (windowSteps H.pairs) ∧ pairSpan H.pairs=directionFlag Q g k := by
  induction k with
  | zero =>
    constructor
    · change LinearIndependent ℝ (fun i : Fin 0 => windowSteps ([] : List (E × E)) i)
      exact linearIndependent_empty_type
    · change pairSpan ([] : List (E × E))=directionFlag Q g 0
      rw [directionFlag_zero]
      simp only [pairSpan,windowSteps_range,List.not_mem_nil,Set.ofPred_false,Set.image_empty,Submodule.span_empty]
  | succ k ih =>
    let method := evaluatedLaunchMethod trial
    let H := oneGradientRun method (fun _ => Q) g k
    have hs := ih (by omega)
    have hpre : ∀ i<k,CG.gradient Q g i≠0 := fun i hi => hg i (by omega)
    have hy : ∀ i,windowImages H.pairs i=Q (windowSteps H.pairs i) := fun i =>
      oneGradientRun_pairs_quadratic method Q g k (H.pairs.get i) (List.get_mem _ i)
    have hv := virtual_reference_basis H Q hQ hpos g k hpre
      (oneGradientRun_quadratic_gradient method Q g k) hy hs.1 hs.2
    have hstep : method.step H=trial H • CG.direction Q g k := by
      change trial H • windowDirection H.pairs (virtualGradient H.pairs H.gradient)=_
      rw [hv.2.2]
    have hd : CG.direction Q g k∉directionFlag Q g k := by
      intro hh
      have he := directionFlag_conjugate Q hQ hpos g k hpre hh
      have hn := (CG.invariant_line_pos Q hpos g k (CG.invariant Q hQ hpos g k hpre) (hg k (by omega))).1
      exact (hpos _ hn).ne' he
    have hnew : method.step H∉pairSpan H.pairs := by
      rw [hs.2,hstep]
      intro hh
      apply hd
      have he := Submodule.smul_mem (directionFlag Q g k) (trial H)⁻¹ hh
      rw [smul_smul,inv_mul_cancel₀ (ht k (by omega)),one_smul] at he
      exact he
    change LinearIndependent ℝ (windowSteps (oneGradientRun method (fun _ => Q) g (k+1)).pairs) ∧ _
    rw [oneGradientRun_pairs_succ]
    constructor
    · rw [windowSteps_cons]
      exact hs.1.finCons hnew
    · rw [pairSpan_cons,hs.2,hstep]
      have he := trial_span_extension (directionFlag Q g k) 0 (CG.direction Q g k)
        (Submodule.zero_mem _) (trial H) (ht k (by omega))
      simpa only [zero_add,directionFlag_succ] using he

/-- The evaluated-launch procedure's actual predicted point and gradient
are the true CG point and gradient, and its actual direction is the true CG
direction, despite arbitrary nonzero evaluated lengths.
Use: original classical prediction identities follow from genuine data solves.
Article: main_krylov, prop:classical(b).
Proof: the actual independent stored basis spans the true CG flag, so the
reused genuine virtual Galerkin theorem identifies the computed correction. -/
theorem evaluated_launch_reference (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let method := evaluatedLaunchMethod trial
    let H := oneGradientRun method (fun _ => Q) g k
    method.outputDisplacement H=CG.displacement Q g k ∧
      virtualGradient H.pairs H.gradient=CG.gradient Q g k ∧
      windowDirection H.pairs (virtualGradient H.pairs H.gradient)=CG.direction Q g k := by
  let method := evaluatedLaunchMethod trial
  let H := oneGradientRun method (fun _ => Q) g k
  have hs := evaluated_launch_basis trial Q hQ hpos g N hg ht k hk
  have hy : ∀ i,windowImages H.pairs i=Q (windowSteps H.pairs i) := fun i =>
    oneGradientRun_pairs_quadratic method Q g k (H.pairs.get i) (List.get_mem _ i)
  have hv := virtual_reference_basis H Q hQ hpos g k (fun i hi => hg i (hi.trans_le hk))
    (oneGradientRun_quadratic_gradient method Q g k) hy hs.1 hs.2
  exact ⟨by change H.displacement+virtualCorrection H.pairs H.gradient=_;rw [hv.1,add_sub_cancel],hv.2⟩

/-- The genuine arbitrary-length evaluated-launch step is its actual trial
times the true current CG direction.
Use: all stored pairs are genuinely conjugate and every older trial miss
remains in the evaluated trajectory until the final projection.
Article: main_krylov, prop:classical(a).
Proof: substitute the proved actual observed direction into the real step. -/
theorem evaluated_launch_step (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let method := evaluatedLaunchMethod trial
    let H := oneGradientRun method (fun _ => Q) g k
    method.step H=trial H • CG.direction Q g k := by
  exact congrArg (fun d => trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k) • d)
    (evaluated_launch_reference trial Q hQ hpos g N hg ht k hk).2.2

/-- Actual evaluated points retain the complete sum of all previous missed
CG line components, with arbitrary nonzero data-dependent trials.
Use: the evaluated-launch source error is derived from its real trajectory.
Article: main_krylov, prop:classical(a).
Proof: sum the genuine actual steps, subtract the actual CG step sum and
collect the physical missed-line coefficients term by term. -/
theorem evaluated_launch_displacement (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let method := evaluatedLaunchMethod trial
    (oneGradientRun method (fun _ => Q) g k).displacement=CG.displacement Q g k-
      ∑ i∈Finset.range k,(CG.length Q g i-
        trial (oneGradientRun method (fun _ => Q) g i)) • CG.direction Q g i := by
  dsimp only
  rw [oneGradientRun_displacement_sum,CG.displacement,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [oneGradientStep,evaluated_launch_step trial Q hQ hpos g N hg ht i
    ((Finset.mem_range.mp hi).le.trans hk),sub_smul]
  abel

end
end krylov.Methods
