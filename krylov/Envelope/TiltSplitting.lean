import krylov.Envelope.ActualResidualJets
import krylov.Envelope.CanonicalFiltration
set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:tilt and apB:eq:nu, genuine common tilt and actual residual splitting.
Use: construct the actual common first-order Krylov rotation from genuine
frozen displacement increments and identify every real method-dependent
explored gradient component by its true observed step-gradient residuals.
Source: actual CG canonical step normalization and metric pairing, genuine
raw observed-residual differentiation and the true finite orthogonal projector.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped BigOperators
variable {n : ℕ}

/-- The genuine common reference-subspace tilt computed from actual measured frozen displacement increments and true CG step energies.
Use: The genuine common reference-subspace tilt computed from actual measured frozen displacement increments and true CG step energies.
Article: main_krylov, apB:eq:tilt and apB:eq:nu, genuine common tilt and actual residual splitting.
Proof: Use the true reference gradient, actual frozen displacement increments and genuine normalized computed CG steps; no actual method derivative enters. -/
def commonTilt (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (N : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin N, (inner ℝ (CG.gradient (cgOperator base) g N)
    (frozenDisplacement (cgOperator base) (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g)
      (referenceInjection (cgOperator base) g A) (i.val+1)-
     frozenDisplacement (cgOperator base) (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g)
      (referenceInjection (cgOperator base) g A) i.val)/‖canonicalCGStep base g i.val‖) • canonicalCGUnitStep base g i.val

/-- The true canonical vector of actual observed recorded-step/returned-gradient residual derivatives.
Use: The true canonical vector of actual observed recorded-step/returned-gradient residual derivatives.
Article: main_krylov, apB:eq:tilt and apB:eq:nu, genuine common tilt and actual residual splitting.
Proof: Read and differentiate the real executed residual pairings, then use their genuine CG step-energy normalization. -/
def residualVariation (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (N : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin N, (deriv (fun t => inner ℝ (probedStep m (A t) (B t) g i.val)
    (probedGradient m (A t) (B t) g N)) 0/‖canonicalCGStep base g i.val‖) • canonicalCGUnitStep base g i.val

/-- The genuine explored component of every actual smooth admissible globally CG-consistent raw gradient derivative is its real observed residual variation minus the true common frozen tilt.
Use: The genuine explored component of every actual smooth admissible globally CG-consistent raw gradient derivative is its real observed residual variation minus the true common frozen tilt.
Article: main_krylov, apB:eq:tilt and apB:eq:nu, genuine common tilt and actual residual splitting.
Proof: Expand the actual orthogonal projector in its genuine normalized CG prefix. The proved true residual derivative identity separates the common frozen step rotation; real metric pairing and actual nonzero step norms identify each genuine coordinate. Sum the true coordinate differences. -/
theorem actual_tilt_splitting (memory : ℕ → ℕ) (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (A B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hA0 : A 0=fun _ => cgOperator base) (hB0 : B 0=fun _ => cgOperator base) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (hcount : N≤referenceAtomCount base hb g) (hsmooth : SmoothProbedCycleAt m 2 (cgOperator base) g N) :
    (exploredFlag base g N).starProjection
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
        (deriv (fun t => probedGradient m (A t) (B t) g N) 0))=
      residualVariation base g m A B N-commonTilt base g A N := by
  -- Keep the genuine common frozen displacement and the actual raw gradient derivative separate in every real coordinate.
  let ξ := frozenDisplacement (cgOperator base) (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g)
    (referenceInjection (cgOperator base) g A)
  let δg := deriv (fun t => probedGradient m (A t) (B t) g N) 0
  let D := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ δg
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator base) g i≠0 := cg_nonstagnation base hb g i (hi.trans_le hcount)
  rw [exploredFlag_projection base hb g hcount,residualVariation,commonTilt,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hnorm : ‖canonicalCGStep base g i.val‖≠0 := norm_ne_zero_iff.mpr
    (canonicalCGStep_ne_zero base hb g i.val (fun j hj => hpre j (hj.trans_lt i.isLt)))
  have hunit : canonicalCGStep base g i.val=‖canonicalCGStep base g i.val‖ • canonicalCGUnitStep base g i.val :=
    (NormedSpace.norm_smul_normalize _).symm
  -- The true positive-root pairing converts actual physical step coordinates to their genuine canonical normalization.
  have hmtr := canonical_search_pairing base hb (referenceStep (cgOperator base) g i.val) δg
  change inner ℝ (referenceStep (cgOperator base) g i.val) δg=inner ℝ (canonicalCGStep base g i.val) D at hmtr
  rw [hunit,real_inner_smul_left] at hmtr
  -- Differentiate the actual observed residual; the proved genuine Krylov remainder has already been removed by true CG orthogonality.
  have hres := actual_residual_jet_coordinates memory m hm hspan A B g (cgOperator base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 hA0 hB0 N hA hB hpre hsmooth i.val i.isLt
  change deriv (fun t => inner ℝ (probedStep m (A t) (B t) g i.val) (probedGradient m (A t) (B t) g N)) 0=
    inner ℝ (referenceStep (cgOperator base) g i.val) δg+inner ℝ (ξ (i.val+1)-ξ i.val) (CG.gradient (cgOperator base) g N) at hres
  rw [hmtr,real_inner_comm (CG.gradient (cgOperator base) g N) (ξ (i.val+1)-ξ i.val)] at hres
  rw [← sub_smul,hres]
  congr 1
  field_simp
  dsimp only [D,δg,ξ]
  ring
end
end krylov.Envelope
