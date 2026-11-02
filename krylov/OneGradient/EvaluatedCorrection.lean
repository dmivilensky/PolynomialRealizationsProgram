import krylov.OneGradient.EvaluatedCanonical
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(b), genuine evaluated correction identities.
Use: prove the original newly observed residual pairing and the actual final
Hestenes inverse action on the real evaluated-launch transcript.
Source: actual conjugate recorded steps, genuine quadratic gradient balance
and the proved native predicted-point projection, not an assumed correction.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true pairing of an actual evaluated step with every later returned
gradient depends only on its own newly observed secant and initial gradient.
Use: replace the final residual pairing by the original g_(j+1) pairing in
the literal diagonal Dixon/Nazareth correction formula.
Article: main_krylov, prop:classical(b).
Proof: the real quadratic gradient is the initial gradient plus the actual
sum of recorded operator actions; conjugacy kills every other true step. -/
theorem evaluated_step_later_pairing (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0)
    (i k : ℕ) (hi : i<k) (hk : k≤N) :
    let method := evaluatedLaunchMethod trial
    let s := oneGradientStep method (fun _ => Q) g i
    inner ℝ s (oneGradientGradient method (fun _ => Q) g k)=inner ℝ s g+inner ℝ s (Q s) := by
  let method := evaluatedLaunchMethod trial
  let s := oneGradientStep method (fun _ => Q) g i
  change inner ℝ s (oneGradientRun method (fun _ => Q) g k).gradient=inner ℝ s g+inner ℝ s (Q s)
  rw [oneGradientRun_quadratic_gradient,inner_add_right,oneGradientRun_displacement_sum,map_sum,inner_sum]
  congr 1
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact evaluated_launch_conjugate trial Q hQ hpos g N hg ht i j (hi.trans_le hk)
      ((Finset.mem_range.mp hj).trans_le hk) hji.symm
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hi))

/-- The actual final and newly observed residual pairings on every old
evaluated step are exactly equal.
Use: the original source correction reads each true g_(j+1), with no further
gradient query and no approximate replacement of the final residual.
Article: main_krylov, prop:classical(b).
Proof: both real returned gradients have the same proved actual pair energy. -/
theorem evaluated_step_returned_pairing (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0)
    (i k : ℕ) (hi : i<k) (hk : k≤N) :
    let method := evaluatedLaunchMethod trial
    let s := oneGradientStep method (fun _ => Q) g i
    inner ℝ s (oneGradientGradient method (fun _ => Q) g k)=
      inner ℝ s (oneGradientGradient method (fun _ => Q) g (i+1)) :=
  (evaluated_step_later_pairing trial Q hQ hpos g N hg ht i k hi hk).trans
    (evaluated_step_later_pairing trial Q hQ hpos g N hg ht i (i+1) (by omega) (by omega)).symm

end

noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
variable {n : ℕ}

/-- The actual full-cycle projection correction is exactly the original
Hestenes inverse-matrix action on its true evaluated gradient.
Use: this concerns the real native output and spends no additional query.
Article: main_krylov, prop:classical(b).
Proof: genuine predicted-gradient termination gives Q u=-g_evaluated for
the actual computed correction. Apply the real positive matrix inverse and
cancel its true inverse domain. -/
theorem evaluated_final_inverse_action
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g i)≠0) :
    let method := evaluatedLaunchMethod trial
    let H := oneGradientRun method (fun _ => cgOperator base) g n
    method.output H= -cgOperator base⁻¹ H.gradient := by
  let method := evaluatedLaunchMethod trial
  let H := oneGradientRun method (fun _ => cgOperator base) g n
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by omega)
  have hvirt := (evaluated_launch_reference trial (cgOperator base) hp.1 hp.2 g n hpre ht n le_rfl).2.1
  have hstop := cg_terminates base hb g
  rw [hc] at hstop
  have hy : ∀ i,windowImages H.pairs i=cgOperator base (windowSteps H.pairs i) := fun i =>
    oneGradientRun_pairs_quadratic method (cgOperator base) g n (H.pairs.get i) (List.get_mem _ i)
  have hzero : H.gradient+cgOperator base (method.output H)=0 := by
    have he : virtualGradient H.pairs H.gradient=0 := hvirt.trans hstop
    rwa [virtualGradient_quadratic H.pairs (cgOperator base) _ hy] at he
  have he := congrArg (cgOperator base⁻¹) (eq_neg_of_add_eq_zero_right hzero)
  rw [map_neg] at he
  have hinv : cgOperator base⁻¹ (cgOperator base (method.output H))=method.output H := by
    simp only [cgOperator,← mul_apply_eq_comp,← map_mul,Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr hb.det_pos.ne'),map_one,one_apply_eq_self]
  rw [hinv] at he
  exact he

end
end krylov.OneGradient
