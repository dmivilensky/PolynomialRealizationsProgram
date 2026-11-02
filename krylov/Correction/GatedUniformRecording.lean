import krylov.Correction.GatedRecordedBounds
import krylov.Correction.GatedCanonical

/-!
Article: main_krylov, thm:UCq and thm:UCg, actual uniform gated-RFC recording.
Use: Derive genuine physical correction and secant bounds from the measured
spectral test, without any minimum individual step or reference energy.
Source: original measured RFC execution, true canonical metric covariance,
the proved observed spectral-gate conditioning and coefficient noncancellation.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The genuine physical gated phase obeys the uniform correction-to-total-step bound in its original positive reference metric.
Use: Supply the actual finite uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform recording.
Proof: Apply the proved observed-pair gate bound to the actual canonical fields and use exact true phase and line-search covariance.
-/
theorem gatedArrayPhase_canonical_recorded_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (S Y : Fin p → EuclideanSpace ℝ (Fin n)) (g d : EuclideanSpace ℝ (Fin n))
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {N : ℕ} {γ η : ℝ} (hγ : 0<γ) (hη : 0≤η)
    (hsize : p+1≤N) (hhalf : η≤1/2) (hsmall : (N : ℝ)*η≤γ/4)
    (hηsize : (N : ℝ)*η≤1)
    (hA : ‖canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤η)
    (hy : ∀ j, ‖dualWindow base Y j-primalWindow base S j‖≤η*‖primalWindow base S j‖) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    ‖R (gatedArrayPhase γ S Y g d (A d) B).movement‖≤gatedCorrectionConstant N γ*
      ‖R (lineLength g d (A d) • d+(gatedArrayPhase γ S Y g d (A d) B).movement)‖ := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  have hmove := (gatedArrayPhase_canonical base hb γ S Y g d (A d) B).1
  have hbound := gatedArrayPhase_recorded_bound (primalWindow base S) (dualWindow base Y)
    (J g) (R d) (canonicalOperator base A) (canonicalOperator base B)
    hγ hη hsize hhalf hsmall hηsize hA hy
  rw [canonicalOperator_primal base hb,hmove,canonical_lineLength base hb] at hbound
  simpa only [map_add,map_smul] using hbound

/-- The real recorded secant of any actual probed method has its canonical relative pair-error bound from its true correction and actual segment budgets.
Use: Supply the actual finite uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform recording.
Proof: The exact executed secant defect is the genuine correction-operator mismatch acting on its actual movement. True primal/dual covariance bounds the mismatch by twice the original operator budget, then the actual pair triangle estimate applies.
-/
theorem probed_canonical_pair_error (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) {ε K : ℝ}
    (hA : ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hB : ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hχ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedPhase m A B g i).movement‖≤
      K*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)‖) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedSecant m A B g i)-
      Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)‖≤
        ((1+2*K)*ε)*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)‖ := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let s := R (probedStep m A B g i)
  let χ := R (probedPhase m A B g i).movement
  let y := J (probedSecant m A B g i)
  let C := canonicalOperator base (A i)
  let D := canonicalOperator base (B i)
  have he : y=C s+(D-C) χ := by
    have ht := congrArg J (probedSecant_defect_identity m A B g i)
    rw [_root_.sub_apply,map_sub,map_sub,← canonicalOperator_primal base hb,
      ← canonicalOperator_primal base hb,← canonicalOperator_primal base hb] at ht
    change y-C s=D χ-C χ at ht
    change y=C s+(D χ-C χ)
    exact eq_add_of_sub_eq' ht
  have hdiff : ‖D-C‖≤2*ε := by
    rw [show D-C=(D-ContinuousLinearMap.id ℝ _)-(C-ContinuousLinearMap.id ℝ _) by abel]
    exact (norm_sub_le _ _).trans ((add_le_add hB hA).trans_eq (by ring))
  have hξ : ‖(D-C) χ‖≤(2*K)*ε*‖s‖ := by
    have hε : 0≤ε := (norm_nonneg _).trans hA
    have h₁ := mul_le_mul_of_nonneg_right hdiff (norm_nonneg χ)
    have h₂ := mul_le_mul_of_nonneg_left hχ (by positivity : 0≤2*ε)
    exact ((D-C).le_opNorm χ).trans ((h₁.trans h₂).trans_eq (by ring))
  exact observed_pair_error_bound C s ((D-C) χ) y he hA hξ

/-- Every actual finite gated-RFC run has uniform correction-to-recorded-step and genuine relative secant-error bounds with constants depending only on horizon and gate threshold.
Use: Supply the actual finite uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform recording.
Proof: Induct on the actual measured prefix. Each earlier genuine correction bound controls its true stored secant error; the actual current spectral-gated phase then supplies the next bound. Both real fallback branches and zero steps are included, and no minimum reference energy or trajectory-conditioning hypothesis is assumed.
-/
theorem gated_uniform_recorded_bounds (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (memory : ℕ → ℕ) (γ : ℝ) (hγ : 0<γ)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) {ε : ℝ} (hε : 0≤ε)
    (hA : ∀ i<N, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hB : ∀ i<N, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hhalf : (1+2*gatedCorrectionConstant N γ)*ε≤1/2)
    (hsmall : (N : ℝ)*((1+2*gatedCorrectionConstant N γ)*ε)≤γ/4)
    (hsize : (N : ℝ)*((1+2*gatedCorrectionConstant N γ)*ε)≤1) :
    let m := gatedMethod memory γ (E := EuclideanSpace ℝ (Fin n))
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    (∀ i<N, ‖R (probedPhase m A B g i).movement‖≤gatedCorrectionConstant N γ*‖R (probedStep m A B g i)‖) ∧
      ∀ i<N, ‖J (probedSecant m A B g i)-R (probedStep m A B g i)‖≤
        ((1+2*gatedCorrectionConstant N γ)*ε)*‖R (probedStep m A B g i)‖ := by
  let m := gatedMethod memory γ (E := EuclideanSpace ℝ (Fin n))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let K := gatedCorrectionConstant N γ
  let η := (1+2*K)*ε
  have hK : 0≤K := gatedCorrectionConstant_nonneg N γ
  have hη : 0≤η := by dsimp only [η]; positivity
  have hεη : ε≤η := by dsimp only [η]; nlinarith
  have hprefix : ∀ q≤N, ∀ i<q, ‖R (probedPhase m A B g i).movement‖≤K*‖R (probedStep m A B g i)‖ := by
    intro q
    induction q with
    | zero => intro _ i hi; omega
    | succ q ih =>
      intro hq i hi
      have hqN : q<N := by omega
      have hprev := ih hqN.le
      by_cases he : i=q
      · subst i
        have hy (j : Fin (min (memory q) q)) :
            ‖dualWindow base (fun j : Fin (min (memory q) q) => probedSecant m A B g (q-1-j.val)) j-
              primalWindow base (fun j : Fin (min (memory q) q) => probedStep m A B g (q-1-j.val)) j‖≤
                η*‖primalWindow base (fun j : Fin (min (memory q) q) => probedStep m A B g (q-1-j.val)) j‖ := by
          have hj := j.isLt
          have ht : q-1-j.val<q := by omega
          exact probed_canonical_pair_error base hb m A B g _ (hA _ (ht.trans hqN))
            (hB _ (ht.trans hqN)) (hprev _ ht)
        have hnew := gatedArrayPhase_canonical_recorded_bound base hb
          (fun j : Fin (min (memory q) q) => probedStep m A B g (q-1-j.val))
          (fun j : Fin (min (memory q) q) => probedSecant m A B g (q-1-j.val))
          (methodRun m A B g q).gradient (m.direction (methodRun m A B g q)) (A q) (B q)
          hγ hη (by have hm := Nat.min_le_right (memory q) q; omega) hhalf hsmall hsize
          ((hA q hqN).trans hεη) hy
        rw [← probedGated_phase_array] at hnew
        exact hnew
      · exact hprev i (by omega)
  have hχ := hprefix N le_rfl
  exact ⟨hχ,fun i hi => probed_canonical_pair_error base hb m A B g i (hA i hi) (hB i hi) (hχ i hi)⟩

end
end krylov.Correction
