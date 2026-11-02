import krylov.Information.TransportedNormal
import krylov.Correction.ScenarioExpansion
import krylov.Correction.CycleData
import krylov.Methods.RFCReference

/-!
Article: main_krylov, thm:C2(c), the true finite query basis of the RFC prefix.
Use: derive actual moving-hyperplane normal regularity from genuine
observed raw directions and true reference CG geometry.
Source: the real complete RFC executor, actual full CG frame, coordinate
analyticity and proved inverse-transpose normal transport.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The actual canonical raw query directions of the genuine full-memory RFC prefix, in newest-first order.
Use: the missing old-first source entry corresponds to the last column and the observed later probes span all the preceding columns.
Article: main_krylov, thm:C2(c), the real query basis [d_(n−1),…,d₀]. -/
def sourceQueryColumns {N : ℕ} (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (Θ : symmetricScenarios (N+1) (N+1))
    (i : Fin (N+1)) : EuclideanSpace ℝ (Fin (N+1)) :=
  cgOperator (metricRoot base) (probedDirection (rfcMethod fullMemory 1)
    (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g (N-i.val))

/-- The actual full canonical matrix of the real raw RFC query directions.
Use: its genuine inverse transpose defines the unobserved normal from true finite query data.
Article: main_krylov, thm:C2(c), actual canonical full query matrix C. -/
def sourceQueryMatrix {N : ℕ} (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (Θ : symmetricScenarios (N+1) (N+1)) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ := fullBasisMatrix (sourceQueryColumns base g Θ)

/-- The true canonical reference raw query family is independent, with no assumed query frame or direction scale.
Use: discharge the actual reference determinant needed by the moving observed-hyperplane normal.
Article: main_krylov, thm:C2(c), genuine reference query-basis rank.
Proof: the actual full CG frame is orthonormal in newest-first order.
Each real canonical CG direction is its genuine unit step multiplied by
its nonzero true step norm and inverse true line length. Rescaling that
actual independent family by these real units preserves independence.
-/
theorem canonicalReferenceQueries_independent {N : ℕ}
    (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount base hb g=N+1) :
    LinearIndependent ℝ (fun i : Fin (N+1) =>
      cgOperator (metricRoot base) (CG.direction (cgOperator base) g (N-i.val))) := by
  -- The actual reference directions retain all true CG line and energy scales until rank is derived.
  let u := fun i : Fin (N+1) => canonicalCGUnitStep base g (N-i.val)
  have ho : Orthonormal ℝ u := by
    have hf := canonicalCG_frame_of_full_atoms base hb g hcount
    simpa only [u,Function.comp_def,Fin.val_rev,Nat.add_sub_add_right] using hf.comp Fin.rev Fin.rev_injective
  have hs (i : Fin (N+1)) : canonicalCGStep base g (N-i.val)≠0 := by
    intro hz
    have hh := ho.norm_eq_one i
    simp only [u,canonicalCGUnitStep,hz,NormedSpace.normalize_zero_eq_zero,norm_zero] at hh
    exact zero_ne_one hh
  let a := fun i : Fin (N+1) => (cgLine base g (N-i.val))⁻¹*‖canonicalCGStep base g (N-i.val)‖
  have ha (i : Fin (N+1)) : a i≠0 :=
    mul_ne_zero (inv_ne_zero (cgLine_ne_zero base g _ (hs i))) (norm_ne_zero_iff.mpr (hs i))
  have hcol (i : Fin (N+1)) : cgOperator (metricRoot base) (CG.direction (cgOperator base) g (N-i.val))=a i • u i := by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base))
      (cgRun (cgOperator base) g (N-i.val)).direction=_
    rw [canonicalCG_direction base g _ (hs i)]
    conv_lhs => rw [← NormedSpace.norm_smul_normalize (canonicalCGStep base g (N-i.val))]
    rw [smul_smul]
    rfl
  have hli := ho.linearIndependent.units_smul (fun i => Units.mk0 (a i) (ha i))
  convert hli using 1
  funext i
  exact hcol i

/-- The actual zero-scenario raw RFC query columns are precisely the genuine reference CG directions in the same canonical coordinates and storage order.
Use: both actual reference rank and geometric normal pairings concern the exact observed query basis.
Article: main_krylov, thm:C2(c), exact true query reference identification.
Proof: the original zero scenario has the actual constant quadratic operators;
the proved real RFC reference execution returns the genuine CG direction.
-/
theorem sourceQueryColumns_zero {N : ℕ}
    (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (i : Fin (N+1)) :
    sourceQueryColumns base g 0 i=
      cgOperator (metricRoot base) (CG.direction (cgOperator base) g (N-i.val)) := by
  unfold sourceQueryColumns
  change cgOperator (metricRoot base) (probedDirection (rfcMethod fullMemory 1)
    (scenarioProbe (N := N+1) base 0) (scenarioCorrection (N := N+1) base 0) g (N-i.val))=_
  rw [scenarioProbe_zero,scenarioCorrection_zero]
  exact congrArg (cgOperator (metricRoot base))
    (rfc_reference_direction fullMemory 1 _ (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 g (fun _ _ ha => ha) _)

/-- The real full RFC reference query matrix is genuinely nonsingular under the article's original full active-atom premise.
Use: the informed algorithm's query-basis inverse is derived from the actual execution.
Article: main_krylov, thm:C2(c), det C(0)≠0.
Proof: actual zero-scenario RFC queries are true CG directions, whose real canonical family is independently proved independent. -/
theorem sourceQueryMatrix_reference_unit {N : ℕ}
    (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount base hb g=N+1) :
    IsUnit (sourceQueryMatrix base g 0).det := by
  apply fullBasisMatrix_unit
  have he : sourceQueryColumns base g 0=(fun i : Fin (N+1) =>
      cgOperator (metricRoot base) (CG.direction (cgOperator base) g (N-i.val))) := funext (sourceQueryColumns_zero base hb g)
  rw [he]
  exact canonicalReferenceQueries_independent base hb g hcount

/-- Every entry of the genuine full raw RFC query matrix is analytic in all original finite symmetric source scenario variables near the full reference.
Use: the moving observed hyperplane's true first-order estimate is derived from primitive source data, not assumed.
Article: main_krylov, thm:C2(c), actual full query-basis joint regularity.
Proof: the actual finite source coordinates give analytic line and
independent correction operators. The genuine repeated-RFC prefix theorem
gives every actual raw direction at its original chronological index.
The fixed physical metric root and finite true coordinates preserve analyticity.
-/
theorem sourceQueryMatrix_entry_analytic {N : ℕ}
    (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount base hb g=N+1) :
    ∀ i j, AnalyticAt ℝ (fun Θ : symmetricScenarios (N+1) (N+1) => sourceQueryMatrix base g Θ i j) 0 := by
  -- Retain the genuine full source coordinates, including every independent intermediate correction defect.
  let E := fun Θ : symmetricScenarios (N+1) (N+1) => matrixSequenceExtension N Θ.val.1
  let F := fun Θ : symmetricScenarios (N+1) (N+1) => matrixSequenceExtension (N+1) Θ.val.2
  let A := fun Θ : symmetricScenarios (N+1) (N+1) => scenarioProbe base Θ.val
  let B := fun Θ : symmetricScenarios (N+1) (N+1) => scenarioCorrection base Θ.val
  have hE (i : ℕ) : AnalyticAt ℝ (fun Θ => E Θ i) 0 := symmetricScenario_increment_analytic i
  have hF (i : ℕ) : AnalyticAt ℝ (fun Θ => F Θ i) 0 := symmetricScenario_correction_analytic i
  have hA (i : ℕ) : AnalyticAt ℝ (fun Θ => A Θ i) 0 :=
    canonicalFCPath_analyticAt (fun _ => base) E 0 analyticAt_const (Eventually.of_forall fun _ => hb) hE i
  have hB (i : ℕ) : AnalyticAt ℝ (fun Θ => B Θ i) 0 := by
    have hm : AnalyticAt ℝ (fun Θ => metricRoot base*F Θ i*metricRoot base) 0 :=
      (analyticAt_const.mul (hF i)).mul analyticAt_const
    exact (hA i).add ((matrixOperator_contDiffAt _ 0 hm.contDiffAt).analyticAt)
  have hA0 : A 0=(fun _ => cgOperator base) := scenarioProbe_zero base
  have hB0 : B 0=(fun _ => cgOperator base) := scenarioCorrection_zero base
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i≤N) : CG.gradient (cgOperator base) g i≠0 := cg_nonstagnation base hb g i (by omega)
  intro i j
  have hq := (full_cycle_data_regular 1 A B (fun _ => g) hA hB analyticAt_const
    (cgOperator base) hA0 hB0 hp.1 hp.2 (N-j.val) (fun i hi => hpre i (by omega))).2.1 0
  have hcanonical := analytic_operator_apply (Q := fun _ : symmetricScenarios (N+1) (N+1) =>
    cgOperator (metricRoot base)) analyticAt_const hq
  exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (N+1) => ℝ) i).analyticAt _).comp hcanonical


/-- Every actual later reference query column is perpendicular to the true first CG unit step, in the genuine newest-first query order.
Use: identify precisely the observed hyperplane and its single missing original first direction.
Article: main_krylov, thm:C2(c), original later-probe reference orthogonality.
Proof: the true reference query is its actual canonical CG direction. Its
nonzero line length converts it to the corresponding actual canonical step;
the proved full CG frame makes every nonfirst step orthogonal to the first.
-/
theorem sourceQueryColumns_reference_orthogonal {N : ℕ}
    (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount base hb g=N+1)
    (i : Fin (N+1)) (hi : i.val<N) :
    inner ℝ (sourceQueryColumns base g 0 i) (canonicalCGUnitStep base g 0)=0 := by
  -- Use the true chronological index N−i, which is positive exactly for the observed later queries.
  let j : Fin (N+1) := ⟨N-i.val,by omega⟩
  have hf := canonicalCG_frame_of_full_atoms base hb g hcount
  have hs : canonicalCGStep base g j.val≠0 := by
    intro hz
    have hh := hf.norm_eq_one j
    simp only [canonicalCGUnitStep,hz,NormedSpace.normalize_zero_eq_zero,norm_zero] at hh
    exact zero_ne_one hh
  have horth : inner ℝ (canonicalCGUnitStep base g j.val) (canonicalCGUnitStep base g 0)=0 := by
    simpa only [Fin.val_zero] using hf.inner_eq_zero (i := j) (j := 0)
      (by intro h; have hv : N-i.val=0 := congrArg Fin.val h; omega)
  rw [sourceQueryColumns_zero base hb g]
  change inner ℝ ((Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base))
    (cgRun (cgOperator base) g j.val).direction) (canonicalCGUnitStep base g 0)=0
  rw [canonicalCG_direction base g j.val hs]
  conv_lhs => rw [← NormedSpace.norm_smul_normalize (canonicalCGStep base g j.val)]
  change inner ℝ (NormedSpace.normalize (canonicalCGStep base g j.val)) (canonicalCGUnitStep base g 0)=0 at horth
  simp only [real_inner_smul_left,horth,mul_zero]

end
end krylov.Information
