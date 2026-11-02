import krylov.Envelope.PositiveReferenceCurve
import krylov.Stability.AnalyticCG
import krylov.Reference.GradientMeasure

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual positive CG shadow references.
Use: transfer the true positive matrix shadow curve to actual Euclidean
operators and derive its genuine prescribed first jet, analytic CG states
and real active positive neighborhood directly from the reference.
Source: actual matrix/operator identification, standard finite analytic
calculus and proved genuine active CG trajectory regularity.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Secant krylov.Stability Matrix Filter Topology
open scoped Matrix.Norms.L2Operator ContDiff
variable {n : ℕ}

/-- The genuine Euclidean operator of the actual analytic positive quadratic reference shadow curve.
Use: The genuine Euclidean operator of the actual analytic positive quadratic reference shadow curve.
Article: main_krylov, apB:lem:mu(c), actual positive CG shadow references.
Proof: Apply the true matrix/operator identification to the genuine matrix shadow. -/
def positiveReferenceOperator (base D : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  cgOperator (positiveReferenceCurve base D t)

/-- The actual positive quadratic shadow operator starts at its genuine supplied reference.
Use: The actual positive quadratic shadow operator starts at its genuine supplied reference.
Article: main_krylov, apB:lem:mu(c), actual positive CG shadow references.
Proof: Use the true zero-parameter matrix shadow identity. -/
theorem positiveReferenceOperator_zero (base D : Matrix (Fin n) (Fin n) ℝ) :
    positiveReferenceOperator base D 0=cgOperator base := by rw [positiveReferenceOperator,positiveReferenceCurve_zero]

/-- The actual positive quadratic shadow operator has exactly the genuine prescribed physical perturbation derivative.
Use: The actual positive quadratic shadow operator has exactly the genuine prescribed physical perturbation derivative.
Article: main_krylov, apB:lem:mu(c), actual positive CG shadow references.
Proof: Compose the true matrix shadow derivative with its genuine continuous linear matrix/operator identification. -/
theorem positiveReferenceOperator_hasDeriv (base D : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (positiveReferenceOperator base D) (cgOperator D) 0 := by
  let L := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt 0 (positiveReferenceCurve_hasDeriv base D)

/-- The genuine positive quadratic shadow operator is actually real analytic.
Use: The genuine positive quadratic shadow operator is actually real analytic.
Article: main_krylov, apB:lem:mu(c), actual positive CG shadow references.
Proof: Transfer the true analytic finite matrix curve through its actual continuous linear operator identification. -/
theorem positiveReferenceOperator_analytic (base D : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    AnalyticAt ℝ (positiveReferenceOperator base D) t :=
  (matrixOperator_contDiffAt (positiveReferenceCurve base D) t (r := ω)
    (positiveReferenceCurve_analytic base D t).contDiffAt).analyticAt

/-- The actual CG gradients and directions of the genuine positive quadratic shadow are real analytic on every true active reference prefix.
Use: The actual CG gradients and directions of the genuine positive quadratic shadow are real analytic on every true active reference prefix.
Article: main_krylov, apB:lem:mu(c), actual positive CG shadow references.
Proof: The true reference shadow operator is analytic and equals the genuine positive reference at zero, so actual reference CG analyticity derives every real state domain. -/
theorem positiveReferenceOperator_gradient_analytic (base D : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (hpre : ∀ j < i, CG.gradient (cgOperator base) g j≠0) :
    AnalyticAt ℝ (fun t => CG.gradient (positiveReferenceOperator base D t) g i) 0 ∧
      AnalyticAt ℝ (fun t => CG.direction (positiveReferenceOperator base D t) g i) 0 := by
  -- Genuine shadow operator analyticity and the actual positive reference derive every true executed CG denominator.
  apply cg_prefix_analytic (positiveReferenceOperator base D) (fun _ => g) 0
    (positiveReferenceOperator_analytic base D 0) analyticAt_const
  · rw [positiveReferenceOperator_zero]
    exact (cgOperator_positive base hb).1
  · rw [positiveReferenceOperator_zero]
    exact (cgOperator_positive base hb).2
  · rwa [positiveReferenceOperator_zero]

/-- The genuine positive quadratic shadow has a true neighborhood of positive symmetric operators with every actual prescribed CG prefix gradient nonzero.
Use: The genuine positive quadratic shadow has a true neighborhood of positive symmetric operators with every actual prescribed CG prefix gradient nonzero.
Article: main_krylov, apB:lem:mu(c), actual positive CG shadow references.
Proof: True determinant continuity gives actual local matrix positivity. Genuine CG gradient continuity preserves each real nonzero active reference gradient; finiteness gives one actual common neighborhood. -/
theorem positiveReferenceOperator_eventually_active (base D : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (hD : D.IsSymm) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient (cgOperator base) g i≠0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (positiveReferenceOperator base D t).toLinearMap.IsSymmetric ∧
      (∀ v : EuclideanSpace ℝ (Fin n), v≠0 → 0 < inner ℝ v (positiveReferenceOperator base D t v)) ∧
      ∀ i<N, CG.gradient (positiveReferenceOperator base D t) g i≠0 := by
  -- Intersect the true positive shadow neighborhood with all actual finitely many nonstagnation neighborhoods.
  have hne (i : Fin N) : ∀ᶠ t in 𝓝 (0 : ℝ), CG.gradient (positiveReferenceOperator base D t) g i.val≠0 := by
    have hc := (positiveReferenceOperator_gradient_analytic base D hb g i.val (fun j hj => hpre j (hj.trans i.isLt))).1.continuousAt
    apply hc.eventually_ne
    rw [positiveReferenceOperator_zero]
    exact hpre i.val i.isLt
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : Fin N, CG.gradient (positiveReferenceOperator base D t) g i.val≠0 :=
    Filter.eventually_all.mpr hne
  filter_upwards [positiveReferenceCurve_eventually_posDef base D hb hD,hall] with t ht hg
  exact ⟨(cgOperator_positive _ ht).1,(cgOperator_positive _ ht).2,fun i hi => hg ⟨i,hi⟩⟩
end
end krylov.Envelope
