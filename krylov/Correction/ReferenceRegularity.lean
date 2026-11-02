import krylov.Correction.CanonicalCoefficient
import krylov.Stability.CanonicalRegularity

/-!
Article: main_krylov, thm:C and lem:U, actual moving-reference model data.
Use: establish joint reference-side analyticity and inverse domains for the
native quadratic coefficient before proving compact-uniform cubic remainders.
Source: actual quadratic RFC execution, true CG nonstagnation and the existing
analytic matrix, operator evaluation and rational CG recurrences.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Reference krylov.Methods krylov.Stability krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine reference CG step is analytic in the actual varying operator and initial gradient on its nonstagnating domain.
Use: the frozen incoming coefficient may vary with the true compact reference.
Article: main_krylov, lem:U and thm:C, actual reference-step regularity.
Proof: actual CG gradient and direction regularity follow from the proved
rational recurrence. Positive true reference curvature discharges the line
denominator, so its actual line length and total step are analytic.
-/
theorem referenceStep_analyticAt (Q : X → E →L[ℝ] E) (g : X → E) (x : X)
    (hQa : AnalyticAt ℝ Q x) (hg : AnalyticAt ℝ g x)
    (hQ : (Q x).toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q x v))
    (i : ℕ) (hpre : ∀ j ≤ i, CG.gradient (Q x) (g x) j ≠ 0) :
    AnalyticAt ℝ (fun p => referenceStep (Q p) (g p) i) x := by
  -- The actual positive CG direction gives the true nonzero line denominator.
  have hd := cg_prefix_analytic Q g x hQa hg hQ hpos i (fun j hj => hpre j hj.le)
  have hi := CG.invariant (Q x) hQ hpos (g x) i (fun j hj => hpre j hj.le)
  have hn := (CG.invariant_line_pos (Q x) hpos (g x) i hi (hpre i le_rfl)).1
  have hc := (hpos _ hn).ne'
  have hz := analytic_operator_apply hQa hd.2
  exact ((analytic_inner hd.2 hd.1).neg.div (analytic_inner hd.2 hz) hc).smul hd.2

/-- The true frozen incoming vector is jointly analytic when the actual reference varies.
Use: its reference dependence is proved from real CG steps, not assumed as a coefficient field.
Article: main_krylov, thm:C, joint regularity of r₁.
Proof: each true CG reference step is analytic on its nonstagnating domain.
Actual operator-difference actions and inner products form the finite real
coordinates; the Euclidean coordinate equivalence assembles the vector.
-/
theorem frozenIncoming_variable_analyticAt (Q : X → E →L[ℝ] E) (g : X → E)
    (A : X → ℕ → E →L[ℝ] E) (x : X)
    (hQa : AnalyticAt ℝ Q x) (hg : AnalyticAt ℝ g x)
    (hA : ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hQ : (Q x).toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q x v))
    (k : ℕ) (hpre : ∀ j ≤ k, CG.gradient (Q x) (g x) j ≠ 0) :
    AnalyticAt ℝ (fun p => frozenIncoming (Q p) (g p) (A p) k) x := by
  -- Assemble the genuine head and all old-coordinate analytic pairings.
  have hs (i : ℕ) (hi : i ≤ k) : AnalyticAt ℝ (fun p => referenceStep (Q p) (g p) i) x :=
    referenceStep_analyticAt Q g x hQa hg hQ hpos i (fun j hj => hpre j (hj.trans hi))
  have ha : AnalyticAt ℝ (fun p => WithLp.ofLp (frozenIncoming (Q p) (g p) (A p) k)) x := by
    apply AnalyticAt.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact analyticAt_const
    · exact analytic_inner (hs _ (by omega))
        (analytic_operator_apply ((hA k).sub (hA (k-1-j.val))) (hs k le_rfl))
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (k+1) => ℝ)).symm.toContinuousLinearMap.analyticAt _).comp ha

/-- The actual full reference RFC columns and their true Gram and physical matrices are jointly analytic with proved inverse domains.
Use: freeze the coefficient at each genuine varying reference while keeping one common analytic parameter chart.
Article: main_krylov, thm:C and lem:U, genuine reference U₀,H₀ and full reconstruction.
Proof: apply the actual quadratic RFC prefix regularity to the varying
static operator and gradient. True CG consistency supplies the positive
model and independent full column family; actual pairings and physical
coordinates assemble the two analytic matrices.
-/
theorem reference_model_data_analyticAt {k : ℕ}
    (base : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : X → EuclideanSpace ℝ (Fin (k+1))) (x : X)
    (hb : AnalyticAt ℝ base x) (hpos : (base x).PosDef) (hg : AnalyticAt ℝ g x)
    (hpre : ∀ j ≤ k, CG.gradient (cgOperator (base x)) (g x) j ≠ 0) :
    let U := fun p => referenceModelBasis (base p) (g p) k
    let H := fun p => pairModel (U p) (fun i => cgOperator (base p) (U p i))
    let R := fun p => fullBasisMatrix (U p)
    (∀ i, AnalyticAt ℝ (fun p => U p i) x) ∧ AnalyticAt ℝ H x ∧ AnalyticAt ℝ R x ∧
      IsUnit (H x).det ∧ IsUnit (R x).det := by
  -- Regularity and nonsingularity are both derived from the same actual quadratic window.
  let Q := fun p => cgOperator (base p)
  let U := fun p => referenceModelBasis (base p) (g p) k
  let H := fun p => pairModel (U p) (fun i => Q p (U p i))
  let R := fun p => fullBasisMatrix (U p)
  have hQa : AnalyticAt ℝ Q x := (matrixOperator_contDiffAt base x hb.contDiffAt).analyticAt
  have hp := cgOperator_positive (base x) hpos
  have ht := quadraticRFC_prefix_analytic fullMemory 1 (fun p _ => Q p) (fun p _ => Q p)
    g x (fun _ => hQa) (fun _ => hQa) hg (Q x) rfl rfl hp.1 hp.2 (fun _ _ ha => ha)
      (k+1) (fun j hj => hpre j (by omega))
  have hU (i : Fin (k+1)) : AnalyticAt ℝ (fun p => U p i) x := by
    refine Fin.cases (ht.2 k (by omega)).1 (fun j => ?_) i
    exact (ht.2 (k-1-j.val) (by omega)).2.1
  have hH : AnalyticAt ℝ H x := analytic_spectral_matrix _ x fun i j =>
    analytic_inner (hU _) (analytic_operator_apply hQa (hU _))
  have hR : AnalyticAt ℝ R x := analytic_spectral_matrix _ x fun i j =>
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k+1) => ℝ) i).analyticAt _).comp (hU j)
  have hHu : IsUnit (H x).det := by
    have he : H x=pairModel (U x) (probedImageBasis (rfcMethod fullMemory 1)
        (fun _ => Q x) (fun _ => Q x) (g x) k) := by
      rw [quadratic_imageBasis]
      rfl
    rw [he]
    exact isUnit_iff_ne_zero.mpr (quadratic_probedModel_posDef _
      (rfcMethod_consistent fullMemory (fun _ ha => ha) 1) (Q x) hp.1 hp.2 (g x) k (fun i hi => hpre i (by omega))).det_pos.ne'
  have hRu : IsUnit (R x).det := fullBasisMatrix_unit _ (probedStepBasis_independent _
    (rfcMethod_consistent fullMemory (fun _ ha => ha) 1) (Q x) hp.1 hp.2 (g x) k hpre)
  exact ⟨hU,hH,hR,hHu,hRu⟩

end
end krylov.Correction
