import krylov.Stability.AnalyticCG
import krylov.Stability.MetricRootRegularity
import krylov.Stability.ContDiffSpectralMatrix
import krylov.Stability.CanonicalResponseCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), moving actual CG frame regularity.
Use: derive the real canonical unit directions, step scales and full
frame inverse from primitive C-one reference data on the positive domain.
Source: genuine joint CG analyticity, actual positive-root regularity
and normalization of true active nonzero canonical steps.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Topology krylov.Reference krylov.Secant
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every actual active canonical step, its norm and its true normalized
direction are C-one in primitive moving positive reference data.
Use: changing to the actual A0 CG frame has derived first-order cost.
Article: main_krylov, thm:local(a), genuine moving CG coordinates.
Proof: compose the actual jointly analytic CG gradient and direction with
the C-one physical operator. The true positive search curvature gives a
smooth actual length. Apply the genuine moving root and normalize the
derived nonzero active canonical step, using the standard smooth norm. -/
theorem canonicalCG_step_contDiffAt
    (B : X → Matrix (Fin n) (Fin n) ℝ) (hB : ContDiffAt ℝ 1 B 0)
    (hpos : ∀ᶠ z in 𝓝 (0 : X),(B z).PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hk : k<referenceAtomCount (B 0) hpos.self_of_nhds g) :
    ContDiffAt ℝ 1 (fun z => canonicalCGStep (B z) g k) 0 ∧
      ContDiffAt ℝ 1 (fun z => ‖canonicalCGStep (B z) g k‖) 0 ∧
      ContDiffAt ℝ 1 (fun z => canonicalCGUnitStep (B z) g k) 0 := by
  let Q := fun z => cgOperator (B z)
  let G := fun z => CG.gradient (Q z) g k
  let D := fun z => CG.direction (Q z) g k
  have hp := cgOperator_positive (B 0) hpos.self_of_nhds
  have hQ : ContDiffAt ℝ 1 Q 0 := matrixOperator_contDiffAt _ 0 hB
  have hj := activeReferenceCG_analytic (B 0) hpos.self_of_nhds g k hk.le
  have hG : ContDiffAt ℝ 1 G 0 := hj.1.contDiffAt.comp (g := fun p => CG.gradient p.1 p.2 k) (f := fun z => (Q z,g)) 0 (hQ.prodMk contDiffAt_const)
  have hD : ContDiffAt ℝ 1 D 0 := hj.2.contDiffAt.comp (g := fun p => CG.direction p.1 p.2 k) (f := fun z => (Q z,g)) 0 (hQ.prodMk contDiffAt_const)
  have hinv := CG.invariant (Q 0) hp.1 hp.2 g k
    (fun i hi => cg_nonstagnation (B 0) hpos.self_of_nhds g i (by omega))
  have hd := (CG.invariant_line_pos (Q 0) hp.2 g k hinv
    (cg_nonstagnation (B 0) hpos.self_of_nhds g k hk)).1
  have hden : inner ℝ (D 0) (Q 0 (D 0))≠0 := (hp.2 _ hd).ne'
  have hlength : ContDiffAt ℝ 1 (fun z => CG.length (Q z) g k) 0 :=
    (hD.inner ℝ hG).neg.div (hD.inner ℝ (hQ.clm_apply hD)) hden
  have hstep : ContDiffAt ℝ 1 (fun z => canonicalCGStep (B z) g k) 0 :=
    (matrixOperator_contDiffAt _ 0 (metricRoot_contDiffAt B 0 hB hpos)).clm_apply (hlength.smul hD)
  have hne : canonicalCGStep (B 0) g k≠0 := canonicalCGStep_ne_zero (B 0) hpos.self_of_nhds g k
    (fun i hi => cg_nonstagnation (B 0) hpos.self_of_nhds g i (by omega))
  have hnorm : ContDiffAt ℝ 1 (fun z => ‖canonicalCGStep (B z) g k‖) 0 := hstep.norm ℝ hne
  refine ⟨hstep,hnorm,?_⟩
  exact (hnorm.inv (norm_ne_zero_iff.mpr hne)).smul hstep

/-- The true full canonical unit-CG matrix and its actual inverse are
C-one from only primitive positive reference data and full reference atoms.
Use: derive every moving source flag instead of postulating smooth flags.
Article: main_krylov, thm:local(a), actual moving full reference frame.
Proof: genuine active canonical directions are C-one entrywise. Assemble
their true spectral-norm matrix; real full-atom orthogonality supplies its
reference inverse domain and the standard matrix inverse calculus. -/
theorem canonicalCG_frame_contDiffAt
    (B : X → Matrix (Fin n) (Fin n) ℝ) (hB : ContDiffAt ℝ 1 B 0)
    (hpos : ∀ᶠ z in 𝓝 (0 : X),(B z).PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount (B 0) hpos.self_of_nhds g=n) :
    ContDiffAt ℝ 1 (fun z => canonicalCGUnitMatrix (B z) g) 0 ∧
      ContDiffAt ℝ 1 (fun z => (canonicalCGUnitMatrix (B z) g)⁻¹) 0 := by
  have hmatrix : ContDiffAt ℝ 1 (fun z => canonicalCGUnitMatrix (B z) g) 0 := by
    apply contDiff_spectral_matrix
    intro i j
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff.contDiffAt.comp 0
      (canonicalCG_step_contDiffAt B hB hpos g j.val (by omega)).2.2
  exact ⟨hmatrix,contDiff_spectral_inverse _ 0 hmatrix
    (canonicalCGUnitMatrix_unit (B 0) hpos.self_of_nhds g hc)⟩

end
end krylov.Stability
