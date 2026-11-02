import krylov.OneGradient.XRFCProjector
import krylov.Envelope.XRFCTrialDelta
import krylov.LinearAlgebra.TrialResponseSharp
import krylov.LinearAlgebra.MatrixSymmetricFamily
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, sharp constants of actual full-cycle XRFC response maps.
Use: specialize the reused exact symmetric-budget support to the true measured
trial amplitudes, actual unit CG steps and actual oblique evaluated-step flags.
Source: genuine executed full-cycle columns, original nonzero-trial inverse
domains, computed CG orthonormality and proved attained box-budget duality.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope krylov.LinearAlgebra
open scoped BigOperators NNReal Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual canonical matrix/operator dictionary sends a real transpose to
its true Hilbert-space adjoint.
Use: the source's printed Pi_l transpose is the actual response left action.
Article: main_krylov, thm:I.
Proof: the reused Euclidean identification is a genuine star-algebra equivalence. -/
theorem cgOperator_transpose (M : Matrix (Fin n) (Fin n) ℝ) :
    cgOperator Mᵀ=(cgOperator M).adjoint := by
  simpa only [cgOperator,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,ContinuousLinearMap.star_eq_adjoint]
    using map_star (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) M

/-- The true direction-basis first-order response with original measured XRFC amplitudes.
Use: its uncertainty maximum is the source's C_D, with actual attaining operators.
Article: main_krylov, thm:I. -/
def xrfcDirectionResponse (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ l∈Finset.range n,xrfcTrialCoefficient trial base g n l • E l (canonicalCGUnitStep base g l)

/-- The true step-basis response with the actual evaluated-step oblique flags.
Use: retain the original projector factors rather than substitute orthogonal CG flags.
Article: main_krylov, thm:I. -/
def xrfcStepResponse (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ l∈Finset.range n,xrfcTrialCoefficient trial base g n l •
    cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l)ᵀ (E l (canonicalCGUnitStep base g l))

/-- All genuine actual old XRFC oblique flags preserve one common true unit vector.
Use: compare the sharp step-basis and direction-basis constants without
presuming the source's explicit bidiagonal inverse formula.
Article: main_krylov, thm:I, C_S >= C_D.
Proof: the original canonical first column is nonzero by the actual executed
basis theorem. Each true prefix projector preserves this column and therefore
its actual normalized unit vector. -/
theorem xrfc_flags_common_unit
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (ht : ∀ i<n+1,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0) :
    ∃ u : EuclideanSpace ℝ (Fin (n+1)),‖u‖=1 ∧
      ∀ l : ℕ,cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l) u=u := by
  let T := xrfcCanonicalColumns trial base g
  let v := WithLp.toLp 2 (fun a => T a 0)
  have hT := (xrfc_columns_nonsingular trial base hb g hc ht).2
  have hv : v≠0 := by
    intro he
    have hcol : T.col 0=0 := by
      funext a
      exact congrArg (fun w : EuclideanSpace ℝ (Fin (n+1)) => w a) he
    exact (Matrix.linearIndependent_cols_of_det_ne_zero (isUnit_iff_ne_zero.mp hT)).ne_zero 0 hcol
  refine ⟨NormedSpace.normalize v,NormedSpace.norm_normalize hv,?_⟩
  intro l
  have hc' := transported_flag_column T hT l 0
  simp only [Fin.val_zero,Nat.zero_le,ite_true] at hc'
  simpa only [NormedSpace.normalize,map_smul] using congrArg (fun w => ‖v‖⁻¹ • w) hc'

/-- The original measured full-cycle XRFC-D response has exactly its printed
sharp attained independent-budget sum constant.
Use: amplitudes and unit steps come from the genuine reference executor.
Article: main_krylov, thm:I, C_D.
Proof: derive the actual nonstagnating CG orthonormal frame, then specialize
the proved exact direction response maximum. -/
theorem xrfc_direction_response_sharp
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (omega : ℕ → ℝ≥0) :
    IsGreatest {z : ℝ | ∃ E : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)),
      (∀ l<n+1,IsSelfAdjoint (E l) ∧ ‖E l‖≤(omega l : ℝ)) ∧ z=‖xrfcDirectionResponse trial base g E‖}
      (∑ l∈Finset.range (n+1),(omega l : ℝ)*|xrfcTrialCoefficient trial base g (n+1) l|) := by
  have ho := canonicalCGUnitStep_orthonormal base hb g (n+1)
    (fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi))
  simpa only [xrfcDirectionResponse,Finset.mem_range] using
    trial_direction_response_sharp (Finset.range (n+1)) omega
      (xrfcTrialCoefficient trial base g (n+1)) (canonicalCGUnitStep base g)
      (fun i hi => ho.norm_eq_one ⟨i,Finset.mem_range.mp hi⟩)

/-- The actual original step-basis response has its printed attained support
maximum, and this constant is at least the true direction-basis sharp sum.
Use: both sharpness and comparison concern the original physical reference
amplitudes and the actual executed evaluated-step projectors.
Article: main_krylov, thm:I, C_S=max_unit sum omega_l |a_l| norm(Pi_l u) >= C_D.
Proof: specialize actual symmetric box duality to the genuine adjoint old flags
and actual CG unit frame. The true preserved normalized first column yields
the comparison, even with zero budgets, zero trial errors or vanishing amplitudes. -/
theorem xrfc_step_response_sharp
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (ht : ∀ i<n+1,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (omega : ℕ → ℝ≥0) :
    ∃ C : ℝ≥0,
      IsGreatest ((fun u : EuclideanSpace ℝ (Fin (n+1)) =>
        ∑ l∈Finset.range (n+1),(omega l : ℝ)*|xrfcTrialCoefficient trial base g (n+1) l| *
          ‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l) u‖) '' {u | ‖u‖=1}) (C : ℝ) ∧
      IsGreatest {z : ℝ | ∃ E : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)),
        (∀ l<n+1,IsSelfAdjoint (E l) ∧ ‖E l‖≤(omega l : ℝ)) ∧ z=‖xrfcStepResponse trial base g E‖} (C : ℝ) ∧
      (∑ l∈Finset.range (n+1),(omega l : ℝ)*|xrfcTrialCoefficient trial base g (n+1) l|)≤(C : ℝ) := by
  have ho := canonicalCGUnitStep_orthonormal base hb g (n+1)
    (fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi))
  obtain ⟨C,hC,hout⟩ := trial_oblique_response_sharp (Finset.range (n+1)) omega
    (xrfcTrialCoefficient trial base g (n+1))
    (fun l => cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l))
    (canonicalCGUnitStep base g) (fun i hi => ho.norm_eq_one ⟨i,Finset.mem_range.mp hi⟩)
  refine ⟨C,hC,?_,?_⟩
  · simpa only [trialObliqueResponse,← cgOperator_transpose,xrfcStepResponse,Finset.mem_range] using hout
  · obtain ⟨u,hu,hP⟩ := xrfc_flags_common_unit trial base hb g hc ht
    exact trial_oblique_constant_ge_direction (Finset.range (n+1)) omega _ _ _ hC u hu (fun i _ => hP i)

/-- The exact actual direction-basis sharp constant is attained in the
source's original real symmetric canonical matrix scenario class.
Use: eliminate any matrix/operator relaxation in the original uncertainty maximum.
Article: main_krylov, thm:I, original matrix C_D maximum.
Proof: the genuine isometric symmetric matrix-family dictionary transfers the
proved attained actual XRFC operator response maximum in both directions. -/
theorem xrfc_direction_matrix_sharp
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (omega : ℕ → ℝ≥0) :
    IsGreatest {z : ℝ | ∃ E : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ,
      (∀ l<n+1,(E l).IsSymm ∧ ‖E l‖≤(omega l : ℝ)) ∧
      z=‖xrfcDirectionResponse trial base g (fun l => cgOperator (E l))‖}
      (∑ l∈Finset.range (n+1),(omega l : ℝ)*|xrfcTrialCoefficient trial base g (n+1) l|) := by
  have he := symmetric_matrix_family_values (Finset.range (n+1)) (fun l => (omega l : ℝ))
    (fun E => ‖xrfcDirectionResponse trial base g E‖)
  simp only [Finset.mem_range] at he
  rw [he]
  exact xrfc_direction_response_sharp trial base hb g hc omega

/-- The original real symmetric canonical matrices attain exactly the printed
step-basis sharp support maximum, which dominates C_D.
Use: all actual XRFC amplitudes and evaluated-step projectors are retained.
Article: main_krylov, thm:I, original matrix C_S maximum.
Proof: transfer the proved attained true operator sharpness through the
original isometric Euclidean symmetric matrix-family equivalence. -/
theorem xrfc_step_matrix_sharp
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (ht : ∀ i<n+1,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (omega : ℕ → ℝ≥0) :
    ∃ C : ℝ≥0,
      IsGreatest ((fun u : EuclideanSpace ℝ (Fin (n+1)) =>
        ∑ l∈Finset.range (n+1),(omega l : ℝ)*|xrfcTrialCoefficient trial base g (n+1) l| *
          ‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l) u‖) '' {u | ‖u‖=1}) (C : ℝ) ∧
      IsGreatest {z : ℝ | ∃ E : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ,
        (∀ l<n+1,(E l).IsSymm ∧ ‖E l‖≤(omega l : ℝ)) ∧
        z=‖xrfcStepResponse trial base g (fun l => cgOperator (E l))‖} (C : ℝ) ∧
      (∑ l∈Finset.range (n+1),(omega l : ℝ)*|xrfcTrialCoefficient trial base g (n+1) l|)≤(C : ℝ) := by
  obtain ⟨C,hC,hout,hcompare⟩ := xrfc_step_response_sharp trial base hb g hc ht omega
  have he := symmetric_matrix_family_values (Finset.range (n+1)) (fun l => (omega l : ℝ))
    (fun E => ‖xrfcStepResponse trial base g E‖)
  simp only [Finset.mem_range] at he
  exact ⟨C,hC,he.symm ▸ hout,hcompare⟩

/-- Exact original reference trials make both genuine full-cycle response maps
identically zero for every actual canonical perturbation family.
Use: the source's cancellation occurs coefficient by coefficient, including
all vanishing earlier trial errors and the true unobserved output increment.
Article: main_krylov, thm:I, exact reference trials.
Proof: each true measured XRFC amplitude has its zero actual missed-line factor;
both genuine finite response sums therefore vanish exactly. -/
theorem xrfc_exact_trial_responses
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (he : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)=
      CG.length (cgOperator base) g i)
    (E : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    xrfcDirectionResponse trial base g E=0 ∧ xrfcStepResponse trial base g E=0 := by
  have hz (i : ℕ) (hi : i∈Finset.range n) : xrfcTrialCoefficient trial base g n i=0 :=
    xrfcTrialCoefficient_exact trial base g n i (he i (Finset.mem_range.mp hi))
  constructor
  · exact Finset.sum_eq_zero (fun i hi => by rw [hz i hi,zero_smul])
  · exact Finset.sum_eq_zero (fun i hi => by rw [hz i hi,zero_smul])

end
end krylov.OneGradient
