import krylov.Functions.RFCLeadingFields
import krylov.Correction.JointRemainder
import krylov.Stability.AnalyticFlatness

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, moving-first-secant RFC coefficient.
Use: retain every actual physical search operator, including its first
secant, in one finite symmetric chart. The genuine physical quadratic
coefficient depends only on operator differences and is therefore invariant
under any common operator shift.
Source: the already proved physical ordinary RFC second-order expansion;
no operator Taylor coefficient or response remainder is assumed.
-/

namespace krylov.Functions
noncomputable section
open Matrix Set Filter Asymptotics Topology krylov.Reference krylov.Methods krylov.Stability
  krylov.Correction krylov.Envelope krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}

/-- All actual symmetric physical search and correction perturbations, including the first search secant.
Article: main_krylov, thm:Htransfer.
The reused scenario space supplies k+1 search slots and k+2 correction slots;
its last unused correction slot is harmless and permits direct reuse. -/
abbrev RFCPhysicalData (k : ℕ) := symmetricScenarios (k+1) (k+2)

/-- The actual independent physical search path in the full finite symmetric chart.
Article: main_krylov, thm:Htransfer. -/
def rfcPhysicalSearch (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (Θ : RFCPhysicalData k)
    (i : ℕ) : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) :=
  cgOperator (base + matrixSequenceExtension (k+1) Θ.val.1 i)

/-- The actual independent physical correction path in the same symmetric chart.
Article: main_krylov, thm:Htransfer. -/
def rfcPhysicalCorrection (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (Θ : RFCPhysicalData k)
    (i : ℕ) : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) :=
  cgOperator (base + matrixSequenceExtension (k+2) Θ.val.2 i)

/-- The true frozen physical quadratic RFC coefficient for arbitrary physical query operators.
Article: main_krylov, thm:Htransfer, before canonical simplification.
Its reference basis and inverse are exactly those of the genuine quadratic run. -/
def rfcPhysicalQuadratic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) :
    EuclideanSpace ℝ (Fin (k+1)) :=
  let U := referenceModelBasis base g k
  let H := pairModel U (fun i => cgOperator base (U i))
  let R := fullBasisMatrix U
  let L := Matrix.of fun i j : Fin (k+1) =>
    inner ℝ (U i) ((B k - A (k-(min i j).val)) (U j))
  cgOperator (Rᵀ⁻¹ * (L * H⁻¹)) (frozenIncoming (cgOperator base) g A k)

/-- The actual second-order coefficient is unchanged by any common shift of all search and correction operators.
Article: main_krylov, thm:Htransfer, cancellation of the drifting first secant.
Proof: both the true latest-model error and true frozen incoming vector
contain only actual operator differences, which cancel the same shift. -/
theorem rfcPhysicalQuadratic_common_shift (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (C : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) :
    rfcPhysicalQuadratic base g (fun i => A i + C) (fun i => B i + C) =
      rfcPhysicalQuadratic base g A B := by
  simp only [rfcPhysicalQuadratic, add_sub_add_right_eq_sub, frozenIncoming]

/-- Every genuine physical symmetric search-coordinate map is analytic throughout its finite source chart.
Article: main_krylov, lem:U and thm:Htransfer.
Proof: actual finite coordinate projections, the true symmetric-subspace
inclusion and the genuine spectral matrix/operator correspondence. -/
theorem rfcPhysicalSearch_analyticAt (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (Θ : RFCPhysicalData k) (i : ℕ) : AnalyticAt ℝ (fun p => rfcPhysicalSearch base p i) Θ := by
  have hM : AnalyticAt ℝ
      (fun p : RFCPhysicalData k => matrixSequenceExtension (k+1) p.val.1 i) Θ := by
    by_cases hi : i < k+1
    · simp only [matrixSequenceExtension, dite_eq_left hi]
      exact ((ContinuousLinearMap.proj (⟨i,hi⟩ : Fin (k+1))) ∘L
        (ContinuousLinearMap.fst ℝ _ _) ∘L (symmetricScenarios (k+1) (k+2)).subtypeL).analyticAt Θ
    · simp only [matrixSequenceExtension, dite_eq_right hi]
      exact analyticAt_const
  exact (matrixOperator_contDiffAt _ Θ (analyticAt_const.add hM).contDiffAt).analyticAt

/-- Every actual independent correction-coordinate map is analytic on the same genuine chart.
Article: main_krylov, lem:U and thm:Htransfer. Proof: the actual second finite coordinate projection. -/
theorem rfcPhysicalCorrection_analyticAt (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (Θ : RFCPhysicalData k) (i : ℕ) : AnalyticAt ℝ (fun p => rfcPhysicalCorrection base p i) Θ := by
  have hM : AnalyticAt ℝ
      (fun p : RFCPhysicalData k => matrixSequenceExtension (k+2) p.val.2 i) Θ := by
    by_cases hi : i < k+2
    · simp only [matrixSequenceExtension, dite_eq_left hi]
      exact ((ContinuousLinearMap.proj (⟨i,hi⟩ : Fin (k+2))) ∘L
        (ContinuousLinearMap.snd ℝ _ _) ∘L (symmetricScenarios (k+1) (k+2)).subtypeL).analyticAt Θ
    · simp only [matrixSequenceExtension, dite_eq_right hi]
      exact analyticAt_const
  exact (matrixOperator_contDiffAt _ Θ (analyticAt_const.add hM).contDiffAt).analyticAt

/-- The actual finite physical paths at zero are precisely the true unperturbed quadratic operator.
Article: main_krylov, thm:Htransfer. -/
theorem rfcPhysicalPaths_zero (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) :
    rfcPhysicalSearch base 0 = (fun _ => cgOperator base) ∧
      rfcPhysicalCorrection base 0 = (fun _ => cgOperator base) := by
  constructor <;> funext i <;>
    simp only [rfcPhysicalSearch, rfcPhysicalCorrection, ZeroMemClass.coe_zero,
      Prod.fst_zero, Prod.snd_zero, matrixSequenceExtension_zero, add_zero]

/-- The full actual physical RFC remainder, including independent initial-gradient drift.
Article: main_krylov, lem:cycle-transfer and thm:Htransfer. -/
def rfcPhysicalRemainder (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (p : EuclideanSpace ℝ (Fin (k+1)) × (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k)) :
    EuclideanSpace ℝ (Fin (k+1)) :=
  probedGradient (rfcMethod fullMemory 1) (rfcPhysicalSearch base p.2.2)
    (rfcPhysicalCorrection base p.2.2) (p.1+p.2.1) (k+1) +
      rfcPhysicalQuadratic base p.1 (rfcPhysicalSearch base p.2.2) (rfcPhysicalCorrection base p.2.2)

/-- The real physical remainder is cubic jointly in initial drift and all actual symmetric query perturbations.
Article: main_krylov, thm:Htransfer, pointwise source remainder.
Proof: instantiate the previously proved actual physical RFC expansion
with the genuine entire finite source chart, allowing its first secant to vary. -/
theorem rfcPhysicalRemainder_order (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hk : 0 < k)
    (hpre : ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0) :
    (fun z => rfcPhysicalRemainder base (g,z)) =O[𝓝 0] (fun z => ‖z‖ ^ 3) := by
  let A := fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k => rfcPhysicalSearch base z.2
  let B := fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k => rfcPhysicalCorrection base z.2
  have hp : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k => z.2)
      (0 : EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) := analyticAt_snd
  have hA i : AnalyticAt ℝ (fun z => A z i) 0 := by
    simpa only [A, Function.comp_def] using (rfcPhysicalSearch_analyticAt base (0 : RFCPhysicalData k) i).comp
      (f := fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k => z.2) (x := 0) hp
  have hB i : AnalyticAt ℝ (fun z => B z i) 0 := by
    simpa only [B, Function.comp_def] using (rfcPhysicalCorrection_analyticAt base (0 : RFCPhysicalData k) i).comp
      (f := fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k => z.2) (x := 0) hp
  have hAz : A 0 = fun _ => cgOperator base := (rfcPhysicalPaths_zero base).1
  have hBz : B 0 = fun _ => cgOperator base := (rfcPhysicalPaths_zero base).2
  have hsym z i : (A z i).toLinearMap.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (hb.1.add (symmetricScenario_increment_symm z.2 i))
  have ho := full_physical_second_order A B (fun z => g+z.1) hA hB
    (analyticAt_const.add analyticAt_fst) hsym (cgOperator base) hAz hBz
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 hk
    (by simpa only [Prod.fst_zero, add_zero] using hpre)
  simpa only [rfcPhysicalRemainder, rfcPhysicalQuadratic, Prod.fst_zero, add_zero,
    hAz, hBz, quadratic_imageBasis, referenceModelBasis, A, B, cgOperator] using ho

end
end krylov.Functions
