import krylov.Correction.GatedUniformRecording
import krylov.Correction.GatedPhaseGrowth

/-!
Article: main_krylov, thm:UCg, actual uniform finite-prefix growth.
Use: Control all genuine physical recorded steps and dual gradients uniformly,
with one radius chosen from the horizon and spectral-gate threshold.
Source: proved real gated-RFC recording induction and phase growth,
exact primal/dual phase covariance and elementary finite induction.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- A dimension-and-gate constant controlling genuine finite phase growth.
Use: Propagate a small actual intermediate gradient through the remaining real gated-RFC cycle.
Article: main_krylov, thm:UCg, actual finite-prefix growth.
-/
def gatedGrowthConstant (N : ℕ) (γ : ℝ) : ℝ := 10+2*(10*(N : ℝ)/γ)

/-- The true gated correction phase has uniform physical-movement and dual-gradient bounds in the original positive reference metric.
Use: Propagate a small actual intermediate gradient through the remaining real gated-RFC cycle.
Article: main_krylov, thm:UCg, actual finite-prefix growth.
Proof: Apply the proved actual phase growth to its genuine canonical fields, then use exact phase and real operator-action covariance.
-/
theorem gatedArrayPhase_canonical_growth (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (S Y : Fin p → EuclideanSpace ℝ (Fin n)) (g d : EuclideanSpace ℝ (Fin n))
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {N : ℕ} {γ η : ℝ} (hγ : 0<γ) (hsize : p+1≤N) (hhalf : η≤1/2)
    (hA : ‖canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤η)
    (hB : ‖canonicalOperator base B-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤η)
    (hy : ∀ j, ‖dualWindow base Y j-primalWindow base S j‖≤η*‖primalWindow base S j‖) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    ‖R (gatedArrayPhase γ S Y g d (A d) B).movement‖≤gatedGrowthConstant N γ*‖J g‖ ∧
      ‖J (gatedArrayPhase γ S Y g d (A d) B).gradient‖≤gatedGrowthConstant N γ*‖J g‖ := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  have hc := gatedArrayPhase_canonical base hb γ S Y g d (A d) B
  have hg := gatedArrayPhase_growth (primalWindow base S) (dualWindow base Y) (J g) (R d)
    (canonicalOperator base A) (canonicalOperator base B) hγ hsize hhalf hA hB hy
  rw [canonicalOperator_primal base hb,hc.1,hc.2] at hg
  exact hg

/-- Every actual finite gated-RFC run has uniform one-step gradient and recorded-step bounds, and the resulting explicit finite-horizon gradient amplification.
Use: Propagate a small actual intermediate gradient through the remaining real gated-RFC cycle.
Article: main_krylov, thm:UCg, actual finite-prefix growth.
Proof: The genuine correction/secant induction supplies every actual stored-pair error. Its true current spectral-gated phase has the proved physical growth bound. Exact search bounds the real line displacement, and induction on the actual returned gradients gives the finite power bound, including zero gradients and skipped branches.
-/
theorem gated_uniform_prefix_growth (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
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
    (∀ i<N, ‖J (probedGradient m A B g (i+1))‖≤gatedGrowthConstant N γ*‖J (probedGradient m A B g i)‖ ∧
      ‖R (probedStep m A B g i)‖≤(2+gatedGrowthConstant N γ)*‖J (probedGradient m A B g i)‖) ∧
    ∀ i≤N, ‖J (probedGradient m A B g i)‖≤(gatedGrowthConstant N γ)^i*‖J g‖ := by
  let m := gatedMethod memory γ (E := EuclideanSpace ℝ (Fin n))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let C := gatedGrowthConstant N γ
  let η := (1+2*gatedCorrectionConstant N γ)*ε
  have hC : 0≤C := by dsimp only [C,gatedGrowthConstant]; positivity
  have hK := gatedCorrectionConstant_nonneg N γ
  have hεη : ε≤η := by dsimp only [η]; nlinarith
  have hrecorded := gated_uniform_recorded_bounds base hb memory γ hγ A B g N hε hA hB hhalf hsmall hsize
  have hstep i (hi : i<N) : ‖J (probedGradient m A B g (i+1))‖≤C*‖J (probedGradient m A B g i)‖ ∧
      ‖R (probedStep m A B g i)‖≤(2+C)*‖J (probedGradient m A B g i)‖ := by
    have hy (j : Fin (min (memory i) i)) :
        ‖dualWindow base (fun j : Fin (min (memory i) i) => probedSecant m A B g (i-1-j.val)) j-
          primalWindow base (fun j : Fin (min (memory i) i) => probedStep m A B g (i-1-j.val)) j‖≤
            η*‖primalWindow base (fun j : Fin (min (memory i) i) => probedStep m A B g (i-1-j.val)) j‖ := by
      have hj := j.isLt
      exact hrecorded.2 _ (by omega)
    have hp := gatedArrayPhase_canonical_growth (N := N) base hb
      (fun j : Fin (min (memory i) i) => probedStep m A B g (i-1-j.val))
      (fun j : Fin (min (memory i) i) => probedSecant m A B g (i-1-j.val))
      (methodRun m A B g i).gradient (m.direction (methodRun m A B g i)) (A i) (B i)
      hγ (by have hm := Nat.min_le_right (memory i) i; omega) hhalf
      ((hA i hi).trans hεη) ((hB i hi).trans hεη) hy
    rw [← probedGated_phase_array] at hp
    refine ⟨hp.2,?_⟩
    have hl := actual_line_norm_bound (canonicalOperator base (A i))
      (J (probedGradient m A B g i)) (R (m.direction (methodRun m A B g i)))
      ((hA i hi).trans hεη) hhalf
    rw [canonicalOperator_primal base hb,canonical_lineLength base hb] at hl
    have ht := norm_add_le (R (lineLength (probedGradient m A B g i)
      (m.direction (methodRun m A B g i)) (A i (m.direction (methodRun m A B g i))) •
        m.direction (methodRun m A B g i))) (R (probedPhase m A B g i).movement)
    rw [map_smul] at ht
    have hm : ‖R (probedPhase m A B g i).movement‖≤C*‖J (probedGradient m A B g i)‖ := hp.1
    have ht' := ht.trans (add_le_add hl hm)
    have hfinal : ‖R (lineLength (probedGradient m A B g i)
      (m.direction (methodRun m A B g i)) (A i (m.direction (methodRun m A B g i))) •
        m.direction (methodRun m A B g i)+(probedPhase m A B g i).movement)‖≤(2+C)*‖J (probedGradient m A B g i)‖ := by
      rw [map_add,map_smul]
      exact ht'.trans_eq (by ring)
    exact hfinal
  refine ⟨hstep,?_⟩
  intro i hi
  induction i with
  | zero => simp only [probedGradient,methodRun,History.gradient,pow_zero,one_mul,le_refl]
  | succ i ih =>
    have hiN : i<N := by omega
    have ht := (hstep i hiN).1.trans (mul_le_mul_of_nonneg_left (ih hiN.le) hC)
    exact ht.trans_eq (by rw [pow_succ]; ring)

/-- One positive radius depending only on horizon and gate threshold satisfies every smallness condition in the actual recording and growth inductions.
Use: Propagate a small actual intermediate gradient through the remaining real gated-RFC cycle.
Article: main_krylov, thm:UCg, actual finite-prefix growth.
Proof: Choose a common positive scalar allowance for the half-radius, model lower endpoint and dimension bound; divide it by the genuine dimension-times-correction coefficient.
-/
theorem gated_recording_radius (N : ℕ) (γ : ℝ) (hγ : 0<γ) :
    ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0≤ε → ε≤ε₀ →
      (1+2*gatedCorrectionConstant N γ)*ε≤1/2 ∧
      (N : ℝ)*((1+2*gatedCorrectionConstant N γ)*ε)≤γ/4 ∧
      (N : ℝ)*((1+2*gatedCorrectionConstant N γ)*ε)≤1 := by
  let q := 1+2*gatedCorrectionConstant N γ
  let b : ℝ := min (1/2) (min (γ/4) 1)
  have hK := gatedCorrectionConstant_nonneg N γ
  have hq : 0<q := by dsimp only [q]; linarith
  have hb : 0<b := lt_min (by norm_num) (lt_min (by positivity) zero_lt_one)
  have hden : 0<((N : ℝ)+1)*q := by positivity
  refine ⟨b/(((N : ℝ)+1)*q),div_pos hb hden,?_⟩
  intro ε hε he
  have he' := (le_div_iff₀ hden).mp he
  have hη : 0≤q*ε := mul_nonneg hq.le hε
  have hNη : 0≤(N : ℝ)*(q*ε) := mul_nonneg (Nat.cast_nonneg N) hη
  have hηb : q*ε≤b := by nlinarith
  have hNηb : (N : ℝ)*(q*ε)≤b := by nlinarith
  exact ⟨hηb.trans (min_le_left _ _),hNηb.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hNηb.trans ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- A finite one-step norm growth bound propagates between any two real indices in its proved horizon.
Use: Propagate a small actual intermediate gradient through the remaining real gated-RFC cycle.
Article: main_krylov, thm:UCg, actual finite-prefix growth.
Proof: Induct from the actual earlier index; multiply by the genuine nonnegative one-step constant and preserve the true exponent difference.
-/
theorem finite_norm_growth_between {F : Type*} [NormedAddCommGroup F]
    (v : ℕ → F) {C : ℝ} (hC : 0≤C) (N : ℕ)
    (hnext : ∀ i<N, ‖v (i+1)‖≤C*‖v i‖) (i j : ℕ) (hij : i≤j) (hj : j≤N) :
    ‖v j‖≤C^(j-i)*‖v i‖ := by
  induction j,hij using Nat.le_induction with
  | base => simp only [Nat.sub_self,pow_zero,one_mul,le_refl]
  | succ j hij ih =>
    have hjN : j<N := by omega
    have ht := (hnext j hjN).trans (mul_le_mul_of_nonneg_left (ih hjN.le) hC)
    have hsub : j+1-i=(j-i)+1 := by omega
    exact ht.trans_eq (by rw [hsub,pow_succ]; ring)

end
end krylov.Correction
