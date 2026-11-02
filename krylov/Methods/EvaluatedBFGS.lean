import krylov.Methods.BFGSConjugateInverse
import krylov.Methods.EvaluatedGeometry
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(b), true full-cycle BFGS projection.
Use: derive all actual conjugate secant domains on evaluated transcripts
and prove the genuine accumulated quasi-Newton terminal correction.
Source: actual positive stored CG basis, real diagonal observed model,
true BFGS secant recursion and the genuine zero terminal CG residual. -/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Genuine evaluated-launch observations derive every actual energy and
pairwise conjugacy domain of the accumulated BFGS inverse secant theorem.
Use: no abstract quasi-Newton model property or secant domain is supplied.
Article: main_krylov, prop:classical(b).
Proof: the actual independent stored quadratic basis gives positive energies.
The genuine observed latest model equals the true diagonal cross-Gram, so
both real ordered cross pairings vanish at every pair of distinct indices. -/
theorem evaluated_bfgs_secant_domains (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0)
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k
    (∀ p∈H.pairs,inner ℝ p.1 p.2≠0) ∧
      H.pairs.Pairwise (fun p q => inner ℝ p.1 q.2=0 ∧ inner ℝ p.2 q.1=0) := by
  let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k
  have hb := (evaluated_launch_basis trial Q hQ hpos g N hpre ht k hk).1
  have hy (i : Fin H.pairs.length) : windowImages H.pairs i=Q (windowSteps H.pairs i) :=
    oneGradientRun_pairs_quadratic _ _ _ _ (H.pairs.get i) (List.get_mem _ i)
  have hG : crossGram (windowImages H.pairs) (windowSteps H.pairs)=windowModel H.pairs := by
    rw [show windowImages H.pairs=(fun i => Q (windowSteps H.pairs i)) from funext hy,
      windowModel_quadratic H.pairs Q hQ hy]
  have hoff (i j : Fin H.pairs.length) (hij : i≠j) :
      inner ℝ (windowImages H.pairs i) (windowSteps H.pairs j)=0 := by
    have he := congrFun (congrFun hG i) j
    rw [evaluated_launch_model_diagonal trial Q hQ hpos g N hpre ht k hk,
      Matrix.diagonal_apply_ne _ hij] at he
    exact he
  constructor
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
    change inner ℝ (windowSteps H.pairs i) (windowImages H.pairs i)≠0
    rw [hy]
    exact (hpos _ (hb.ne_zero i)).ne'
  · apply List.pairwise_iff_get.mpr
    intro i j hij
    exact ⟨(real_inner_comm _ _).trans (hoff j i (Ne.symm (ne_of_lt hij))),hoff i j (ne_of_lt hij)⟩

/-- At genuine CG termination, the actual accumulated BFGS inverse action
on the evaluated gradient equals the real full observed projection correction.
Use: the original Dixon quasi-Newton final step is not replaced by a latest
model output in its implementation; equality is proved for its actual model.
Article: main_krylov, prop:classical(b).
Proof: true evaluated observations derive the BFGS secant domains and its
inverse action on the actual stored span. The genuine projected residual is
zero at real CG termination, so minus the true correction is a stored-span
preimage of the actual evaluated gradient. The accumulated model inverts it. -/
theorem evaluated_bfgs_terminal_correction (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0)
    (hstop : CG.gradient Q g N=0) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g N
    show Prop from -inverseBFGSApply 1 H.pairs H.gradient=virtualCorrection H.pairs H.gradient := by
  let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g N
  have hy : ∀ p∈H.pairs,p.2=Q p.1 := oneGradientRun_pairs_quadratic _ _ _ _
  have hya (i : Fin H.pairs.length) : windowImages H.pairs i=Q (windowSteps H.pairs i) :=
    hy (H.pairs.get i) (List.get_mem _ i)
  have hd := evaluated_bfgs_secant_domains trial Q hQ hpos g N hpre ht N le_rfl
  have hu : virtualCorrection H.pairs H.gradient∈pairSpan H.pairs := combine_mem_span _ _
  have hz : H.gradient+Q (virtualCorrection H.pairs H.gradient)=0 := by
    rw [← virtualGradient_quadratic H.pairs Q _ hya,
      (evaluated_launch_reference trial Q hQ hpos g N hpre ht N le_rfl).2.1,hstop]
  have he : Q (-virtualCorrection H.pairs H.gradient)=H.gradient := by
    rw [map_neg,eq_neg_of_add_eq_zero_right hz,neg_neg]
  have hInv := inverseBFGSApply_conjugate_on_span 1 H.pairs Q hy hd.1 hd.2
    (-virtualCorrection H.pairs H.gradient) (Submodule.neg_mem _ hu)
  rw [he] at hInv
  dsimp only
  rw [hInv,neg_neg]

end
end krylov.Methods
