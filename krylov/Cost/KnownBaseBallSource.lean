import krylov.OneGradient.KnownBaseCubeExpansion
import krylov.OneGradient.InformedOutputOrder
import krylov.OneGradient.InformedCalibration
import krylov.Information.ReferenceBall
import krylov.Stability.ContDiffXRFC
import krylov.Stability.ContDiffXRFCD

/-!
Article: `main_krylov`, `thm:hier`, actual known-base ball output.
Keep the physical base displacement and the true query/output drift in
independent normed coordinates. The actual informed S/D source output is
C² jointly, while its whole nearby zero-drift axis vanishes by genuine
full quadratic termination for every nearby positive full-active base.
-/

namespace krylov.Cost
noncomputable section
set_option maxHeartbeats 1000000
open Matrix Filter Topology Asymptotics Finset krylov.Reference krylov.Methods
  krylov.OneGradient krylov.Information krylov.Correction krylov.Envelope krylov.Stability
  krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual independent known-reference displacement coordinate. -/
abbrev KnownBasePrior (d : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℝ)

/-- Independent actual prior and finite query/output source coordinates. -/
abbrev KnownBaseBallParameters (d : ℕ) := KnownBasePrior d×symmetricScenarios d d

/-- The genuine physical source with independent prior and drift coordinates.
Only real query increments and the true unevaluated output form use the
drift coordinate; the prior is carried by the existing physical base chart. -/
def knownBaseBallSource (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (θ : KnownBaseBallParameters (n+1)) : Scenario (n+1) where
  base := referenceBaseChart base θ.1
  increment := (knownBaseSourceCube base θ.2).increment
  terminal := (knownBaseSourceCube base θ.2).terminal
  correction := fun _ ↦ 0

/-- The real informed S/D output on those actual independent source fields. -/
def knownBaseBallOutput (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (n+1))) (θ : KnownBaseBallParameters (n+1)) :=
  informedScenarioOutput directions base g (knownBaseBallSource base θ)

/-- All real query/output source operators are C-r at the true centre for
any order; this follows from primitive affine source fields themselves. -/
theorem knownBaseBallSource_operator_contDiffAt
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (r : WithTop ℕ∞) (j : ℕ) :
    ContDiffAt ℝ r (fun θ : KnownBaseBallParameters (n+1) ↦
      oneGradientScenarioMatrices (knownBaseBallSource base θ) n j) 0 := by
  let S := knownBaseBallSource base
  have hbase : ContDiffAt ℝ r (fun θ : KnownBaseBallParameters (n+1) ↦ (S θ).base) 0 := by
    change ContDiffAt ℝ r (fun θ : KnownBaseBallParameters (n+1) ↦ referenceBaseChart base θ.1) 0
    exact ContDiffAt.comp (g := referenceBaseChart base)
      (f := fun θ : KnownBaseBallParameters (n+1) ↦ θ.1) 0
      (referenceBaseChart_analyticAt base 0).contDiffAt contDiffAt_fst
  have hinc (l : ℕ) : ContDiffAt ℝ r (fun θ : KnownBaseBallParameters (n+1) ↦ (S θ).increment l) 0 := by
    have hcoord : ContDiffAt ℝ r (fun θ : KnownBaseBallParameters (n+1) ↦
        matrixSequenceExtension n θ.2.val.1 l) 0 :=
      ContDiffAt.comp
        (g := fun E : symmetricScenarios (n+1) (n+1) ↦ matrixSequenceExtension n E.val.1 l)
        (f := fun θ : KnownBaseBallParameters (n+1) ↦ θ.2) 0
        (symmetricScenario_increment_analytic l).contDiffAt contDiffAt_snd
    change ContDiffAt ℝ r (fun θ : KnownBaseBallParameters (n+1) ↦
      metricRoot base*matrixSequenceExtension n θ.2.val.1 l*metricRoot base) 0
    exact (contDiffAt_const.mul hcoord).mul contDiffAt_const
  have hterm : ContDiffAt ℝ r (fun θ : KnownBaseBallParameters (n+1) ↦ (S θ).terminal) 0 := by
    have hcoord : ContDiffAt ℝ r (fun θ : KnownBaseBallParameters (n+1) ↦
        matrixSequenceExtension (n+1) θ.2.val.2 n) 0 :=
      ContDiffAt.comp
        (g := fun E : symmetricScenarios (n+1) (n+1) ↦ matrixSequenceExtension (n+1) E.val.2 n)
        (f := fun θ : KnownBaseBallParameters (n+1) ↦ θ.2) 0
        (symmetricScenario_correction_analytic n).contDiffAt contDiffAt_snd
    change ContDiffAt ℝ r (fun θ : KnownBaseBallParameters (n+1) ↦
      metricRoot base*matrixSequenceExtension (n+1) θ.2.val.2 n*metricRoot base) 0
    exact (contDiffAt_const.mul hcoord).mul contDiffAt_const
  have hprobe (k : ℕ) : ContDiffAt ℝ r (fun θ : KnownBaseBallParameters (n+1) ↦ (S θ).probe k) 0 :=
    hbase.add (ContDiffAt.sum (fun l _ ↦ hinc l))
  by_cases hj : j≤n
  · simpa only [oneGradientScenarioMatrices, ite_eq_left hj] using hprobe j
  · simpa only [oneGradientScenarioMatrices, ite_eq_right hj, Scenario.lastOperator] using
      (hprobe n).add hterm

/-- Every actual joint source operator is symmetric, without any
unproved physical reference or hidden model-symmetry certificate. -/
theorem knownBaseBallSource_operator_isSymm
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (θ : KnownBaseBallParameters (n+1)) (j : ℕ) :
    (oneGradientScenarioMatrices (knownBaseBallSource base θ) n j).IsSymm := by
  have hs (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hQ : Q.IsSymm) :
      (metricRoot base*Q*metricRoot base).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, (metricRoot_isSymm base).eq, hQ.eq, Matrix.mul_assoc]
  apply scenario_operators_isSymm
  · change (referenceBaseChart base θ.1).IsSymm
    rw [referenceBaseChart, inverseRootForm base _ hb]
    exact hs _ (Matrix.isSymm_one.add (show θ.1.val.IsSymm from
      (show θ.1.val.IsHermitian from θ.1.property).isSymm))
  · intro l _
    exact hs _ (symmetricScenario_increment_symm θ.2 l)
  · apply hs
    rw [matrixSequenceExtension, dite_eq_left (show n<n+1 by omega)]
    exact θ.2.property.2 _

/-- At the actual centre every source operator is precisely the known base. -/
theorem knownBaseBallSource_operator_zero
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (j : ℕ) :
    oneGradientScenarioMatrices (knownBaseBallSource base 0) n j=base := by
  rw [scenario_operators_zero]
  · exact referenceBaseChart_zero base hb
  · intro l _
    simp [knownBaseBallSource, knownBaseSourceCube, matrixSequenceExtension]
  · simp [knownBaseBallSource, knownBaseSourceCube, matrixSequenceExtension]

/-- The actual informed full physical output is C² jointly in the true
prior and drift, with all virtual inverse domains and trial charts derived. -/
theorem knownBaseBallOutput_contDiffAt (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ContDiffAt ℝ 2 (knownBaseBallOutput directions base g) 0 := by
  let trial := informedTrial (cgOperator base)
  let A := fun θ j ↦ cgOperator (oneGradientScenarioMatrices (knownBaseBallSource base θ) n j)
  have hA (j : ℕ) : ContDiffAt ℝ 2 (fun θ : KnownBaseBallParameters (n+1) ↦ A θ j) 0 :=
    matrixOperator_contDiffAt _ 0 (knownBaseBallSource_operator_contDiffAt base 2 j)
  have hA0 : A 0=fun _ ↦ cgOperator base := by
    funext j
    change cgOperator (oneGradientScenarioMatrices (knownBaseBallSource base 0) n j)=cgOperator base
    rw [knownBaseBallSource_operator_zero base hb j]
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n+1,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi ↦ cg_nonstagnation base hb g i (by omega)
  have hout : ContDiffAt ℝ 2
      (fun θ : KnownBaseBallParameters (n+1) ↦
        (xrfcBasisMethod directions trial).outputGradient (A θ (n+1))
          (oneGradientRun (xrfcBasisMethod directions trial) (A θ) g (n+1))) 0 := by
    cases directions with
    | false =>
      apply (quadraticXRFC_output_contDiffAt trial A (fun θ ↦ A θ (n+1)) (fun _ ↦ g) 0 hA
        (hA (n+1)) contDiffAt_const (cgOperator base) hA0 hp.1 hp.2 (n+1) hpre
        (fun _ _ ↦ (informed_trial_positive (cgOperator base) _).ne') ?_).2
      intro i hi
      rw [hA0]
      exact informed_trial_reference_contDiff false base hb base hb g (n+1) hpre i hi 2
    | true =>
      apply (quadraticXRFCD_output_contDiffAt trial A (fun θ ↦ A θ (n+1)) (fun _ ↦ g) 0 hA
        (hA (n+1)) contDiffAt_const (cgOperator base) hA0 hp.1 hp.2 (n+1) hpre
        (fun _ _ ↦ (informed_trial_positive (cgOperator base) _).ne') ?_).2
      intro i hi
      rw [hA0]
      exact informed_trial_reference_contDiff true base hb base hb g (n+1) hpre i hi 2
  convert hout using 1
  funext θ
  simp only [knownBaseBallOutput, informedScenarioOutput, A,
    oneGradientScenarioMatrices_output,
    oneGradientScenarioMatrices_histories (knownBaseBallSource base θ) n
      (xrfcBasisMethod directions trial) g (n+1) le_rfl, trial]

/-- The actual informed output has zero true first derivative at the
known centre; this comes from its proved physical quadratic response. -/
theorem knownBaseBallOutput_hasFDerivAt_zero (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    HasFDerivAt (knownBaseBallOutput directions base g)
      (0 : KnownBaseBallParameters (n+1)→L[ℝ]EuclideanSpace ℝ (Fin (n+1))) 0 := by
  have ho := informed_native_output_quadratic directions base hb g hc
    (fun θ j ↦ oneGradientScenarioMatrices (knownBaseBallSource base θ) n j)
    (knownBaseBallSource_operator_contDiffAt base 1)
    (knownBaseBallSource_operator_isSymm base hb) (knownBaseBallSource_operator_zero base hb)
  have h : knownBaseBallOutput directions base g =O[𝓝 0]
      (fun θ : KnownBaseBallParameters (n+1) ↦ ‖θ-(0 : KnownBaseBallParameters (n+1))‖^2) := by
    apply ho.congr
    · intro θ
      simp only [knownBaseBallOutput, informedScenarioOutput,
        oneGradientScenarioMatrices_output,
        oneGradientScenarioMatrices_histories (knownBaseBallSource base θ) n
          (xrfcBasisMethod directions (informedTrial (cgOperator base))) g (n+1) le_rfl]
    · intro θ
      rw [sub_zero]
  exact h.hasFDerivAt (by decide)

end
end krylov.Cost
