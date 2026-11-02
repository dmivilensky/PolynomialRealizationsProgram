import krylov.Reference.Stopping
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
Article: main_krylov, lem:U, actual reference CG analyticity.
Use: prove local analyticity of the actual executed CG gradients and directions
on every nonstagnating positive quadratic prefix, including its terminal residual.
Source: the actual rational Fletcher--Reeves recurrence, analytic bounded
bilinear maps and reciprocal scalars away from zero (mathlib).
-/

namespace krylov.Stability
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual inner product of two real-analytic vector functions is real analytic.
Use: every executed line numerator, curvature and squared residual is an analytic observed-data quantity.
Article: main_krylov, lem:U, reference coefficient regularity.
Source: mathlib's analytic bounded bilinear-map theorem applied to the true real inner product.
Proof: compose the actual inner-product bilinear map with the analytic vector pair. -/
theorem analytic_inner {f h : X → E} {x : X} (hf : AnalyticAt ℝ f x) (hh : AnalyticAt ℝ h x) :
    AnalyticAt ℝ (fun p => inner ℝ (f p) (h p)) x :=
  ((innerSL ℝ (E := E)).analyticAt_bilinear (f x,h x)).comp
    (f := fun p => (f p,h p)) (hf.prod hh)

/-- Applying an actual analytic operator-valued function to an analytic vector function is analytic.
Use: actual CG probes depend analytically on the operator and the computed direction together.
Article: main_krylov, lem:U, actual reference probe.
Source: mathlib's analytic bounded bilinear-map theorem for continuous operator evaluation.
Proof: compose true bounded evaluation with the analytic operator/vector pair. -/
theorem analytic_operator_apply {Q : X → E →L[ℝ] E} {f : X → E} {x : X}
    (hQ : AnalyticAt ℝ Q x) (hf : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun p => Q p (f p)) x := by
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
    ((ContinuousLinearMap.apply ℝ (E := E) E).analyticAt_bilinear (f x,Q x)).comp
      (f := fun p => (f p,Q p)) (hf.prod hQ)

/-- The actual CG gradients and directions are jointly real analytic through every active positive reference prefix.
Use: source reference regularity is discharged for the genuine computed trajectory, rather than supplied as a trajectory field.
Article: main_krylov, lem:U, the first N CG steps are real analytic on U_N.
Proof: induct through the actual recurrence; true CG positivity makes each
search denominator nonzero, and actual prefix nonstagnation makes each residual-ratio denominator nonzero. -/
theorem cg_prefix_analytic (Q : X → E →L[ℝ] E) (g : X → E) (x : X)
    (haQ : AnalyticAt ℝ Q x) (hag : AnalyticAt ℝ g x)
    (hQ : (Q x).toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q x v)) (k : ℕ)
    (hpre : ∀ i<k, CG.gradient (Q x) (g x) i≠0) :
    AnalyticAt ℝ (fun p => CG.gradient (Q p) (g p) k) x ∧
      AnalyticAt ℝ (fun p => CG.direction (Q p) (g p) k) x := by
  -- Only denominators of genuinely executed earlier steps are used; the final current residual may be zero.
  induction k with
  | zero => exact ⟨hag,hag.neg⟩
  | succ k ih =>
    obtain ⟨hG,hD⟩ := ih (fun i hi => hpre i (by omega))
    have hi := CG.invariant (Q x) hQ hpos (g x) k (fun i hi => hpre i (by omega))
    have hd := (CG.invariant_line_pos (Q x) hpos (g x) k hi (hpre k (by omega))).1
    have hc : inner ℝ (CG.direction (Q x) (g x) k) (Q x (CG.direction (Q x) (g x) k))≠0 := (hpos _ hd).ne'
    have hZ := analytic_operator_apply haQ hD
    have hα := (analytic_inner hD hG).neg.div (analytic_inner hD hZ) hc
    have hnext : AnalyticAt ℝ (fun p => CG.gradient (Q p) (g p) (k+1)) x := hG.add (hα.smul hZ)
    have hn : inner ℝ (CG.gradient (Q x) (g x) k) (CG.gradient (Q x) (g x) k)≠0 := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hpre k (by omega)))
    have hβ := (analytic_inner hnext hnext).div (analytic_inner hG hG) hn
    refine ⟨hnext,?_⟩
    convert! hnext.neg.add (hβ.smul hD) using 1
    funext p
    simp only [CG.direction_succ, CG.beta, real_inner_self_eq_norm_sq,
      Pi.add_apply, Pi.neg_apply, Pi.smul_apply', Pi.div_apply]

/-- The actual reference CG trajectory is jointly analytic in its true operator and initial gradient.
Use: the general analytic-parameter theorem is instantiated with actual reference coordinates.
Article: main_krylov, lem:U, reference regularity on U_N.
Proof: the genuine operator and gradient coordinate projections are analytic,
and the proved actual finite CG recurrence theorem applies directly. -/
theorem referenceCG_analytic (Q : E →L[ℝ] E) (g : E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i<k, CG.gradient Q g i≠0) :
    AnalyticAt ℝ (fun p : (E →L[ℝ] E) × E => CG.gradient p.1 p.2 k) (Q,g) ∧
      AnalyticAt ℝ (fun p : (E →L[ℝ] E) × E => CG.direction p.1 p.2 k) (Q,g) :=
  cg_prefix_analytic Prod.fst Prod.snd (Q,g) analyticAt_fst analyticAt_snd hQ hpos k hpre

/-- The article's actual active-atom condition discharges all denominators in the joint reference-analyticity theorem.
Use: no reference trajectory analyticity or nonstagnation is assumed as input data.
Article: main_krylov, lem:U, at least N active atoms.
Proof: true active-spectrum nonstagnation holds at every genuinely required
earlier step, so the proved actual operator/gradient reference analyticity applies. -/
theorem activeReferenceCG_analytic {n : ℕ} (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k≤referenceAtomCount base hb g) :
    AnalyticAt ℝ (fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n) => CG.gradient p.1 p.2 k) (cgOperator base,g) ∧
      AnalyticAt ℝ (fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n) => CG.direction p.1 p.2 k) (cgOperator base,g) :=
  referenceCG_analytic _ g (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 k
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hk))

variable [CompleteSpace E]

/-- Every actual nonstagnating positive CG prefix is C^r for every differentiability order.
Use: supplies the reference-side regularity hypotheses of later compact Taylor and base-variation estimates.
Article: main_krylov, lem:U, analytic reference trajectory.
Proof: the proved actual analytic trajectory has derivatives of every order by mathlib's analytic regularity theorem. -/
theorem cg_prefix_contDiffAt (Q : X → E →L[ℝ] E) (g : X → E) (x : X)
    (haQ : AnalyticAt ℝ Q x) (hag : AnalyticAt ℝ g x)
    (hQ : (Q x).toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q x v)) (k : ℕ)
    (hpre : ∀ i<k, CG.gradient (Q x) (g x) i≠0) (r : WithTop ℕ∞) :
    ContDiffAt ℝ r (fun p => CG.gradient (Q p) (g p) k) x ∧
      ContDiffAt ℝ r (fun p => CG.direction (Q p) (g p) k) x :=
  ⟨(cg_prefix_analytic Q g x haQ hag hQ hpos k hpre).1.contDiffAt,
    (cg_prefix_analytic Q g x haQ hag hQ hpos k hpre).2.contDiffAt⟩

end
end krylov.Stability
