import krylov.Convergence.EvaluatedDomains
import krylov.OneGradient.EvaluatedCanonical
import krylov.OneGradient.XRFCLaunchDictionary

/-!
Article: main_krylov, prop:EL, actual full-window launch dictionary.
Use: derive real full-column inverse domains and identify the actual
unevaluated evaluated-launch output with its true observed-model solve.
Source: actual recorded quadratic basis and chronological solve covariance.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Correction krylov.OneGradient
open scoped BigOperators
variable {n : ℕ}

/-- Actual chronological physical columns of evaluated launch. Article: prop:EL. -/
def evaluatedLaunchPhysicalColumns (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun a j=>(oneGradientStep (evaluatedLaunchMethod trial) (fun _=>cgOperator base) g j.val) a

/-- The real evaluated-launch columns have their true inverse domain.
Article: main_krylov, prop:EL. -/
theorem evaluatedLaunch_columns_nonsingular (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g i)≠0) :
    IsUnit (evaluatedLaunchPhysicalColumns trial base g).det ∧ IsUnit (evaluatedCanonicalColumns trial base g).det := by
  let Q := cgOperator base
  let m := evaluatedLaunchMethod trial
  let s := oneGradientStep m (fun _ => Q) g
  let S := fun i : Fin n => s (n-1-i.val)
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i<n) : CG.gradient Q g i≠0 :=
    cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hdom := (evaluatedLaunch_array_domains trial Q hp.1 hp.2 g n hpre ht n le_rfl).2
  have hunit : IsUnit (correctionCompression S Q).det := by
    rw [← pairModel_quadratic S Q hp.1]
    exact isUnit_iff_ne_zero.mpr hdom
  have hLI := compression_unit_independent S Q hunit
  have hChron : LinearIndependent ℝ (fun i : Fin n => s i.val) := by
    have h := hLI.comp (Fin.revPerm (n := n)) (Fin.revPerm (n := n)).injective
    convert h using 1
    funext i
    change s i.val=s (n-1-i.rev.val)
    congr 1
    rw [Fin.val_rev]
    omega
  have hraw : LinearIndependent ℝ (evaluatedLaunchPhysicalColumns trial base g).col :=
    hChron.map' (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).ker
  have hS : IsUnit (evaluatedLaunchPhysicalColumns trial base g).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hraw)
  refine ⟨hS,?_⟩
  change IsUnit (metricRoot base*evaluatedLaunchPhysicalColumns trial base g).det
  rw [Matrix.det_mul]
  exact (metricRoot_det_unit base hb).mul hS


/-- The actual evaluated-launch output is its true observed full-model solve. Article: prop:EL. -/
theorem evaluatedLaunch_semantic_launch_dictionary
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (hu : IsUnit (fullBasisMatrix (fun i : Fin n => oneGradientStep (evaluatedLaunchMethod trial)
      (fun k => cgOperator (A k)) g i.val)).det) :
    let m := evaluatedLaunchMethod trial
    let H := oneGradientRun m (fun k => cgOperator (A k)) g n
    let S := fullBasisMatrix (fun i : Fin n => oneGradientStep m (fun k => cgOperator (A k)) g i.val)
    m.outputGradient (cgOperator (A n)) H=launchSemanticGradient S A H.gradient := by
  let m := evaluatedLaunchMethod trial
  let op := fun k => cgOperator (A k)
  let H := oneGradientRun m op g n
  let s := fun i : Fin n => oneGradientStep m op g i.val
  let y := fun i : Fin n => op i.val (s i)
  let S := fullBasisMatrix s
  have hcross : crossGram s y=Sᵀ*pairImages S A := by
    ext i j
    rw [← observed_compression]
    exact (compressed_entry_pairing S (A j.val) i j).symm
  have hchron := chronological_modelCorrection s y H.gradient
  rw [hcross] at hchron
  have hn := (oneGradient_full_virtual_coordinates m op g n).1
  have hquery : m.output H=combine s (modelCoefficients s (latest (Sᵀ*pairImages S A)) H.gradient) := by
    change virtualCorrection H.pairs H.gradient=_
    simp only [selectedWindow_full] at hn
    rw [hn]
    simpa only [s,y,H,Function.comp_def,Fin.revPerm_apply,Fin.val_rev,Nat.sub_sub,Nat.add_comm] using hchron.symm
  have hl := launch_semantic_coefficients S hu A H.gradient
  change H.gradient+cgOperator (A n) (m.output H)=_
  rw [hquery]
  exact hl.symm


end
end krylov.Convergence
