import krylov.Correction.ReferenceRegularity
import krylov.Correction.ScenarioExpansion

/-!
Article: main_krylov, thm:C and lem:U, the genuine joint cubic remainder.
Use: retain the original finite symmetric scenario variables while allowing
the positive quadratic base and initial gradient to vary in a common chart.
Source: the actual native physical coefficient, genuine moving-reference
analyticity and exact canonical coefficient identification.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator ContDiff
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Each real entry of a genuinely analytic spectral matrix family is analytic.
Use: derive the actual entry hypotheses of inverse-matrix regularity from its true spectral-norm matrix regularity.
Article: main_krylov, lem:U and thm:C, coordinate regularity of actual coefficient matrices.
Proof: compose the genuine analytic matrix family with a bounded linear
entry projection through the proved spectral matrix coordinate equivalence. -/
theorem analytic_matrix_entry {n : ℕ} {M : X → Matrix (Fin n) (Fin n) ℝ} {x : X}
    (hM : AnalyticAt ℝ M x) (i j : Fin n) : AnalyticAt ℝ (fun p => M p i j) x :=
  (((ContinuousLinearMap.proj (i,j)) ∘L
    (matrixEntryEquiv n n).toContinuousLinearMap).analyticAt _).comp hM

/-- The actual full RFC output plus its genuine frozen native quadratic coefficient in the true canonical metric.
Use: an analytic formula for the real remainder whose reference parameters may vary.
Article: main_krylov, thm:C and lem:U, actual joint native remainder. -/
def nativeScenarioRemainder {k : ℕ} (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (Θ : symmetricScenarios (k+1) (k+1)) :
    EuclideanSpace ℝ (Fin (k+1)) :=
  let A := scenarioProbe base Θ.val
  let B := scenarioCorrection base Θ.val
  let U := referenceModelBasis base g k
  let H := pairModel U (fun i => cgOperator base (U i))
  let R := fullBasisMatrix U
  let L := Matrix.of fun i j : Fin (k+1) =>
    inner ℝ (U i) ((B k-A (k-(min i j).val)) (U j))
  cgOperator (metricRoot base)⁻¹
    (probedGradient (rfcMethod fullMemory 1) A B g (k+1)+
      cgOperator Rᵀ⁻¹ (cgOperator (L*H⁻¹) (frozenIncoming (cgOperator base) g A k)))

/-- The genuine native remainder is exactly the source canonical staircase remainder at every true reference and scenario.
Use: prove joint regularity through the actual native formula while stating the final bound in the original article geometry.
Article: main_krylov, thm:C, identification of the actual cubic remainder.
Proof: the actual static quadratic images identify the true reference model.
The proved native coefficient cancellation gives exactly the source staircase
and fresh vector, with the true last-step norm; linearity transports the output.
-/
theorem nativeScenarioRemainder_eq {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g)
    (Θ : symmetricScenarios (k+1) (k+1)) :
    nativeScenarioRemainder base g Θ=
      cgOperator (metricRoot base)⁻¹ (probedGradient (rfcMethod fullMemory 1)
        (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g (k+1))+
      ‖canonicalCGStep base g k‖ • staircaseOperator base g
        (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
        (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1)) := by
  -- The reference Gram is the actual one computed from quadratic images.
  dsimp only [nativeScenarioRemainder]
  rw [map_add]
  congr 1
  change cgOperator (metricRoot base)⁻¹
    (cgOperator (fullBasisMatrix (referenceModelBasis base g k))ᵀ⁻¹
      (cgOperator ((Matrix.of fun i j : Fin (k+1) => inner ℝ (referenceModelBasis base g k i)
        ((canonicalCorrectionOperator base (matrixSequenceExtension k Θ.val.1)
          (matrixSequenceExtension (k+1) Θ.val.2 k) k-
          canonicalFCPath base (matrixSequenceExtension k Θ.val.1) 1 (k-(min i j).val))
            (referenceModelBasis base g k j)))*
        (pairModel (referenceModelBasis base g k) (fun i => cgOperator base (referenceModelBasis base g k i)))⁻¹)
        (frozenIncoming (cgOperator base) g (canonicalFCPath base (matrixSequenceExtension k Θ.val.1) 1) k)))=_
  have hc := native_coefficient_canonical base hb g hN
    (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k)
  simp only [quadratic_imageBasis] at hc
  simpa only [cgOperator,map_mul,mul_apply_eq_comp,scenarioProbe,scenarioCorrection,
    canonicalCorrectionOperator,referenceModelBasis,Nat.add_sub_cancel] using hc

/-- The actual native remainder has proved cubic order in all original finite symmetric scenario variables at each genuine reference.
Use: discharge the pointwise order used to identify the true Taylor jets in the compact argument.
Article: main_krylov, thm:C and lem:U, pointwise joint-scenario cubic order.
Proof: identify the actual native remainder with the already proved genuine
canonical remainder, whose cubic bound holds jointly in the entire original scenario space. -/
theorem nativeScenarioRemainder_order {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    nativeScenarioRemainder base g =O[𝓝 0] (fun Θ => ‖Θ‖^3) := by
  exact (scenario_second_order base hb g hN hk).congr_left
    (fun Θ => (nativeScenarioRemainder_eq base hb g hN Θ).symm)

/-- The actual native cubic remainder is jointly analytic in the genuine varying reference and all original scenario variables.
Use: derive compact-uniform cubic bounds without assuming a uniform remainder or its Taylor jet.
Article: main_krylov, thm:C and lem:U, joint analyticity of the true source remainder.
Proof: original finite scenario coordinates give analytic physical queries.
The actual gated RFC prefix supplies the true returned output regularity.
Actual moving-reference CG data give analytic frozen columns, model, full
reconstruction and incoming vector, with both inverse domains proved from
genuine CG nonstagnation. Compose these actual operators and vectors.
-/
theorem nativeScenarioRemainder_analyticAt {k : ℕ}
    (base : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : X → EuclideanSpace ℝ (Fin (k+1))) (x : X)
    (hb : AnalyticAt ℝ base x) (hpos : ∀ᶠ y in 𝓝 x, (base y).PosDef)
    (hg : AnalyticAt ℝ g x)
    (hN : k+1≤referenceAtomCount (base x) hpos.self_of_nhds (g x)) :
    AnalyticAt ℝ (fun p : X × symmetricScenarios (k+1) (k+1) =>
      nativeScenarioRemainder (base p.1) (g p.1) p.2) (x,0) := by
  -- Use exactly the original finite scenario coordinates and the actual varying base chart.
  let x₀ : X × symmetricScenarios (k+1) (k+1) := (x,0)
  let b := fun p : X × symmetricScenarios (k+1) (k+1) => base p.1
  let γ := fun p : X × symmetricScenarios (k+1) (k+1) => g p.1
  let E := fun p : X × symmetricScenarios (k+1) (k+1) => matrixSequenceExtension k p.2.val.1
  let F := fun p : X × symmetricScenarios (k+1) (k+1) => matrixSequenceExtension (k+1) p.2.val.2
  let A := fun p => scenarioProbe (b p) p.2.val
  let B := fun p => scenarioCorrection (b p) p.2.val
  let U := fun p => referenceModelBasis (b p) (γ p) k
  let H := fun p => pairModel (U p) (fun i => cgOperator (b p) (U p i))
  let R := fun p => fullBasisMatrix (U p)
  let L := fun p => Matrix.of fun i j : Fin (k+1) => inner ℝ (U p i)
    ((B p k-A p (k-(min i j).val)) (U p j))
  have hba : AnalyticAt ℝ b x₀ := hb.comp analyticAt_fst
  have hga : AnalyticAt ℝ γ x₀ := hg.comp analyticAt_fst
  have hbp : ∀ᶠ p in 𝓝 x₀, (b p).PosDef := by
    exact (continuous_fst.tendsto x₀).eventually hpos
  have hE (i : ℕ) : AnalyticAt ℝ (fun p => E p i) x₀ := by
    by_cases hi : i<k
    · simp only [E,matrixSequenceExtension,dite_eq_left hi]
      exact ((ContinuousLinearMap.proj (⟨i,hi⟩ : Fin k)) ∘L (ContinuousLinearMap.fst ℝ _ _) ∘L
        (symmetricScenarios (k+1) (k+1)).subtypeL ∘L (ContinuousLinearMap.snd ℝ X _)).analyticAt _
    · simp only [E,matrixSequenceExtension,dite_eq_right hi]
      exact analyticAt_const
  have hF (i : ℕ) : AnalyticAt ℝ (fun p => F p i) x₀ := by
    by_cases hi : i<k+1
    · simp only [F,matrixSequenceExtension,dite_eq_left hi]
      exact ((ContinuousLinearMap.proj (⟨i,hi⟩ : Fin (k+1))) ∘L (ContinuousLinearMap.snd ℝ _ _) ∘L
        (symmetricScenarios (k+1) (k+1)).subtypeL ∘L (ContinuousLinearMap.snd ℝ X _)).analyticAt _
    · simp only [F,matrixSequenceExtension,dite_eq_right hi]
      exact analyticAt_const
  have hroot : AnalyticAt ℝ (fun p => metricRoot (b p)) x₀ :=
    (metricRoot_contDiffAt b x₀ (r := ω) hba.contDiffAt hbp).analyticAt
  have hA (i : ℕ) : AnalyticAt ℝ (fun p => A p i) x₀ :=
    canonicalFCPath_analyticAt b E x₀ hba hbp hE i
  have hB (i : ℕ) : AnalyticAt ℝ (fun p => B p i) x₀ := by
    exact (hA i).add ((matrixOperator_contDiffAt _ x₀
      ((hroot.mul (hF i)).mul hroot).contDiffAt).analyticAt)
  have hA0 : A x₀=(fun _ => cgOperator (base x)) := scenarioProbe_zero _
  have hB0 : B x₀=(fun _ => cgOperator (base x)) := scenarioCorrection_zero _
  have hp := cgOperator_positive (base x) hpos.self_of_nhds
  have hpre (i : ℕ) (hi : i≤k) : CG.gradient (cgOperator (base x)) (g x) i≠0 :=
    cg_nonstagnation _ hpos.self_of_nhds _ i (by omega)
  have hQ : AnalyticAt ℝ (fun p => cgOperator (b p)) x₀ :=
    (matrixOperator_contDiffAt b x₀ hba.contDiffAt).analyticAt
  -- Every true terminal and frozen-reference inverse domain is derived before composing its action.
  have hdata := reference_model_data_analyticAt b γ x₀ hba hpos.self_of_nhds hga hpre
  have hLa : AnalyticAt ℝ L x₀ := analytic_spectral_matrix _ x₀ fun i j =>
    analytic_inner (hdata.1 i)
      (analytic_operator_apply ((hB k).sub (hA (k-(min i j).val))) (hdata.1 j))
  have hHi : AnalyticAt ℝ (fun p => (H p)⁻¹) x₀ := analytic_spectral_matrix_inv H x₀
    (fun i j => (analytic_matrix_entry (hdata.2.1) i j))
      (isUnit_iff_ne_zero.mp hdata.2.2.2.1)
  have hRi : AnalyticAt ℝ (fun p => (R p)ᵀ⁻¹) x₀ := analytic_spectral_matrix_inv _ x₀
    (fun i j => analytic_matrix_entry hdata.2.2.1 j i)
      (by simpa only [det_transpose] using isUnit_iff_ne_zero.mp hdata.2.2.2.2)
  have hIr : AnalyticAt ℝ (fun p => cgOperator (metricRoot (b p))⁻¹) x₀ :=
    (matrixOperator_contDiffAt _ x₀ (metricRoot_inverse_contDiffAt b x₀ (r := ω) hba.contDiffAt hbp)).analyticAt
  have hGrad := (quadraticRFC_prefix_analytic fullMemory 1 A B γ x₀ hA hB hga
    (cgOperator (base x)) hA0 hB0 hp.1 hp.2 (fun _ _ ha => ha) (k+1)
      (fun i hi => hpre i (by omega))).1
  have hr := frozenIncoming_variable_analyticAt (fun p => cgOperator (b p)) γ A x₀ hQ hga hA hp.1 hp.2 k hpre
  have hM := (matrixOperator_contDiffAt _ x₀ (hLa.mul hHi).contDiffAt).analyticAt
  have hI := (matrixOperator_contDiffAt _ x₀ hRi.contDiffAt).analyticAt
  exact analytic_operator_apply hIr (hGrad.add (analytic_operator_apply hI (analytic_operator_apply hM hr)))

end
end krylov.Correction
