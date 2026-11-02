import krylov.Envelope.DeferredResidualJets
import krylov.Envelope.FreshDefectCoordinates
import krylov.Envelope.ResidualCoordinates
import krylov.Methods.CorrectionFreeSearch

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), actual calibrated DC fresh residual vector.
Use: prove the genuine source residual-variation identity for the actual
calibrated deferred method on every true symmetric increment scenario.
Source: actual old-step deferred first jets, genuine last own-step search
orthogonality and real finite explored residual coordinate reconstruction.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Filter Topology
variable {n : ℕ}

/-- Actual deferred cancellation supplied with the true last reference line length has residual variation exactly equal to square-root last CG energy times the genuine fresh defect on every real scenario.
Use: Actual deferred cancellation supplied with the true last reference line length has residual variation exactly equal to square-root last CG energy times the genuine fresh defect on every real scenario.
Article: main_krylov, apB:lem:mu(d), actual calibrated DC fresh residual vector.
Proof: All actual old recorded residual coordinates are their true fresh physical defect pairings. The genuine final own-step residual is identically zero. The actual fresh vector belongs to the true explored flag, so real orthonormal coordinate reconstruction gives the exact source vector identity. -/
theorem calibratedDeferred_residualVariation (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hB : ∀ i<k+1, ContDiffAt ℝ 2 (fun t => B t i) 0) (hB0 : B 0=fun _ => cgOperator base)
    (hcount : k+1≤referenceAtomCount base hb g) :
    residualVariation base g (deferredMethod fullMemory (k+1) (CG.length (cgOperator base) g k))
      (canonicalFCPath base E) B (k+1)=Real.sqrt (cgEnergy base g k) • freshDefect base g E (k+1) := by
  -- The actual calibrated source policy has the genuine old fresh-defect residual coordinates and true empty corrections.
  let m := deferredMethod fullMemory (k+1) (CG.length (cgOperator base) g k) (E := EuclideanSpace ℝ (Fin n))
  let A := canonicalFCPath base E
  let F := Real.sqrt (cgEnergy base g k) • freshDefect base g E (k+1)
  have hF : F∈exploredFlag base g (k+1) := by
    apply Submodule.smul_mem
    apply exploredFlag_mono base g (show k+1-1≤k+1 by omega)
    exact freshDefect_mem base g E (k+1)
  apply residualVariation_of_coordinates base hb g (k+1) hcount m A B F hF
  intro i hi
  -- Treat the genuine final own-step exact-search residual separately from the actual earlier fresh-defect coordinates.
  by_cases hik : i=k
  · subst i
    have heq : (fun t => inner ℝ (probedStep m (A t) (B t) g k) (probedGradient m (A t) (B t) g (k+1)))=
        fun _ : ℝ => (0 : ℝ) := by
      funext t
      exact correctionFree_last_residual m (deferredMethod_correctionFree _ _ _) (A t) (B t) g k
    rw [heq,deriv_const]
    have hz : inner ℝ (canonicalCGStep base g k) (freshDefect base g E (k+1))=0 := by
      simpa only [Nat.add_sub_cancel] using freshDefect_last_coordinate_zero base hb g hcount (by omega) E
    dsimp only [F]
    rw [real_inner_smul_right,hz,mul_zero]
  · have hil : i<k := by omega
    rw [deferred_residual_derivative base hb g E hE B k hB hB0 hcount i hil]
    exact freshDefect_physical_coordinates base hb g k hcount E i hil
end
end krylov.Envelope
