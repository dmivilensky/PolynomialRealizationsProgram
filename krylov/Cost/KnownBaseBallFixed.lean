import krylov.Cost.KnownBaseBallSource
import krylov.Stability.MixedQuadratic
import krylov.OneGradient.FixedCGTrial
import krylov.OneGradient.CalibratedOutputOrder
import krylov.Methods.XRFCDTermination

/-!
Article: `main_krylov`, `thm:hier`, literal fixed known-CG trials.
Instantiate the real source map with τ_k=α_k(A), reading only the known
reference and the actual observed iteration count. Both C² regularity and
zero first derivative are derived for that precise implementation. Its
whole nearby no-drift axis vanishes by actual quadratic termination even
when the unknown constant base differs from the known centre.
-/

namespace krylov.Cost
noncomputable section
open Matrix Filter Topology Asymptotics Finset krylov.Reference krylov.Methods
  krylov.OneGradient krylov.Information krylov.Correction krylov.Envelope krylov.Stability
  krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual physical source output for the literal fixed known CG lengths. -/
def fixedScenarioOutput (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (n+1))) (S : Scenario (n+1)) :=
  let m := xrfcBasisMethod directions (fixedCGTrial base g)
  m.outputGradient (cgOperator (S.lastOperator n)) (oneGradientRun m S.probeOracle g (n+1))

/-- The same genuine fixed-trial output in independent prior/drift coordinates. -/
def fixedBallOutput (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (n+1))) (θ : KnownBaseBallParameters (n+1)) :=
  fixedScenarioOutput directions base g (knownBaseBallSource base θ)

/-- Every fixed known CG length used during the full cycle is strictly
positive, independently of the actual unknown source history. -/
theorem fixedCGTrial_run_pos
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1))))
    (A : ℕ→EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))
    (k : ℕ) (hk : k<n+1) : 0<fixedCGTrial base g (oneGradientRun m A g k) := by
  rw [fixedCGTrial_run]
  have hp := cgOperator_positive base hb
  exact (CG.invariant_line_pos (cgOperator base) hp.2 g k
    (CG.invariant _ hp.1 hp.2 g k (fun i hi ↦ cg_nonstagnation base hb g i (by omega)))
    (cg_nonstagnation base hb g k (by omega))).2.1

/-- Actual fixed-known-CG S/D outputs are C² in the independent physical
prior/drift coordinates, with no assumed execution smoothness. -/
theorem fixedBallOutput_contDiffAt (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ContDiffAt ℝ 2 (fixedBallOutput directions base g) 0 := by
  let trial := fixedCGTrial base g
  let A := fun θ j ↦ cgOperator (oneGradientScenarioMatrices (knownBaseBallSource base θ) n j)
  have hA (j : ℕ) : ContDiffAt ℝ 2 (fun θ : KnownBaseBallParameters (n+1) ↦ A θ j) 0 :=
    matrixOperator_contDiffAt _ 0 (knownBaseBallSource_operator_contDiffAt base 2 j)
  have hA0 : A 0=fun _ ↦ cgOperator base := by
    funext j
    change cgOperator (oneGradientScenarioMatrices (knownBaseBallSource base 0) n j)=_
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
      exact (quadraticXRFC_output_contDiffAt trial A (fun θ ↦ A θ (n+1)) (fun _ ↦ g) 0 hA
        (hA (n+1)) contDiffAt_const (cgOperator base) hA0 hp.1 hp.2 (n+1) hpre
        (fun i hi ↦ (fixedCGTrial_run_pos base hb g hc _ _ i hi).ne')
        (fun i _ ↦ (fixedCGTrial_contDiff base g i).contDiffAt)).2
    | true =>
      exact (quadraticXRFCD_output_contDiffAt trial A (fun θ ↦ A θ (n+1)) (fun _ ↦ g) 0 hA
        (hA (n+1)) contDiffAt_const (cgOperator base) hA0 hp.1 hp.2 (n+1) hpre
        (fun i hi ↦ (fixedCGTrial_run_pos base hb g hc _ _ i hi).ne')
        (fun i _ ↦ (fixedCGTrial_contDiff base g i).contDiffAt)).2
  convert hout using 1
  funext θ
  simp only [fixedBallOutput, fixedScenarioOutput, A, oneGradientScenarioMatrices_output,
    oneGradientScenarioMatrices_histories (knownBaseBallSource base θ) n
      (xrfcBasisMethod directions trial) g (n+1) le_rfl, trial]

/-- The actual fixed-trial output has zero first derivative at the known
centre, by the proved calibrated physical quadratic output theorem. -/
theorem fixedBallOutput_hasFDerivAt_zero (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    HasFDerivAt (fixedBallOutput directions base g)
      (0 : KnownBaseBallParameters (n+1)→L[ℝ]EuclideanSpace ℝ (Fin (n+1))) 0 := by
  have ho := calibrated_native_output_quadratic directions (fixedCGTrial base g) base hb g hc
    (fixedCGTrial_calibrated base g (n+1))
    (fun _ k _ ↦ (fixedCGTrial_contDiff base g k).contDiffAt)
    (fun θ j ↦ oneGradientScenarioMatrices (knownBaseBallSource base θ) n j)
    (knownBaseBallSource_operator_contDiffAt base 1)
    (knownBaseBallSource_operator_isSymm base hb) (knownBaseBallSource_operator_zero base hb)
  have h : fixedBallOutput directions base g =O[𝓝 0]
      (fun θ : KnownBaseBallParameters (n+1) ↦ ‖θ-(0 : KnownBaseBallParameters (n+1))‖^2) := by
    apply ho.congr
    · intro θ
      simp only [fixedBallOutput, fixedScenarioOutput, oneGradientScenarioMatrices_output,
        oneGradientScenarioMatrices_histories (knownBaseBallSource base θ) n
          (xrfcBasisMethod directions (fixedCGTrial base g)) g (n+1) le_rfl]
    · intro θ
      rw [sub_zero]
  exact h.hasFDerivAt (by decide)

/-- The full nearby zero-drift axis of the actual fixed-known-CG method
vanishes exactly on every genuine positive full-active unknown base. -/
theorem fixedBallOutput_zero_axis (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∀ᶠ Z : KnownBasePrior (n+1) in 𝓝 0,fixedBallOutput directions base g (Z,0)=0 := by
  obtain ⟨r,hr,_,hfull⟩ := referenceBaseChart_full_ball base hb g hc
  have hnear : ∀ᶠ Z : KnownBasePrior (n+1) in 𝓝 0,‖Z‖<r := by
    exact (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using hr))
  filter_upwards [hnear] with Z hZ
  obtain ⟨hB,hcount⟩ := hfull Z hZ.le
  let B := referenceBaseChart base Z
  change referenceAtomCount B hB g=n+1 at hcount
  let S := knownBaseBallSource base (Z,0)
  let trial := fixedCGTrial base g
  let m := xrfcBasisMethod directions trial
  have hinc : ∀ l<n,S.increment l=0 := by
    intro l _
    simp [S, knownBaseBallSource, knownBaseSourceCube, matrixSequenceExtension]
  have hterm : S.terminal=0 := by
    simp [S, knownBaseBallSource, knownBaseSourceCube, matrixSequenceExtension]
  have hop : oneGradientScenarioMatrices S n=fun _ ↦ B :=
    funext (fun j ↦ scenario_operators_zero S hinc hterm j)
  have hhist := oneGradientScenarioMatrices_histories S n m g (n+1) le_rfl
  rw [hop] at hhist
  have hout : S.lastOperator n=B := by
    have h := congrFun hop (n+1)
    rwa [oneGradientScenarioMatrices_output] at h
  change m.outputGradient (cgOperator (S.lastOperator n)) (oneGradientRun m S.probeOracle g (n+1))=0
  rw [hout,← hhist]
  have ht (k : ℕ) (hk : k<referenceAtomCount B hB g) :
      trial (oneGradientRun m (fun _ ↦ cgOperator B) g k)≠0 :=
    (fixedCGTrial_run_pos base hb g hc m _ k (by omega)).ne'
  cases directions with
  | false =>
    have h := (xrfc_full_terminates B hB g trial ht).2.1
    rwa [hcount] at h
  | true =>
    have h := (xrfcD_terminates B hB g fullMemory trial (fun _ _ hi ↦ hi) ht).2.1
    rwa [hcount] at h

/-- True independent-radius mixed estimate for the literal source policy
τ_k=α_k(A), in either actual native S/D implementation. -/
theorem fixedBallOutput_mixed_bound (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ δ C : ℝ,0<δ ∧ 0<C ∧ ∀ Z : KnownBasePrior (n+1),
      ∀ E : symmetricScenarios (n+1) (n+1),‖Z‖<δ → ‖E‖<δ →
        ‖fixedBallOutput directions base g (Z,E)‖≤C*‖Z‖*‖E‖+C*‖E‖^2 :=
  mixed_quadratic_of_zero_axis (fixedBallOutput directions base g)
    (fixedBallOutput_contDiffAt directions base hb g hc)
    (fixedBallOutput_hasFDerivAt_zero directions base hb g hc)
    (fixedBallOutput_zero_axis directions base hb g hc)

end
end krylov.Cost
