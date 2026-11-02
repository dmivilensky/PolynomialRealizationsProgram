import bezout.Gains.Variation
import bezout.Analysis.Relative
import bezout.Risk.Minimax

/-!
Article: bezout, Theorem 4.1, dimension-uniform operator and local relative gains.
Use: gains quantify all actual finite-dimensional executions. The local
gain uses the epsilon--neighborhood definition of the upper limit of the
worst normalized error as the positive error scale tends to zero.
Proof: physical first variation, spectral polynomial bounds, temporal
Cauchy--Schwarz and the dimension-uniform quadratic remainder.
-/

namespace bezout.Gains
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ}

/-- A uniform operator-norm first-variation bound. With `symmetric=true`
only symmetric Hessian perturbations are allowed; the budget is unchanged. -/
def OperatorBound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (symmetric : Bool) (C : ℝ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E), Analysis.Admissible I H →
    ∀ D : Fin N → E →ₗ[ℝ] E,
      (symmetric = true → ∀ s, (D s).IsSymmetric) →
      (∑ s, ‖(D s).toContinuousLinearMap‖ ^ 2 ≤ 1) →
      ∀ initial : E, ‖initial‖ ≤ 1 → ‖h.firstVariation H D initial‖ ≤ C

/-- The dimension-uniform temporal operator-norm gain, as the least universal bound. -/
def operatorGain (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (symmetric : Bool := false) : ℝ := sInf {C : ℝ | OperatorBound h I symmetric C}

/-- An asymptotic relative-error bound, with the supremum over dimensions
and all actual error streams taken before choosing the small-scale limit.
The initial radius is normalized to one by linear homogeneity. -/
def LocalRelativeBound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ t0 : ℝ, 0 < t0 ∧
    ∀ t : ℝ, 0 < t → t < t0 →
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (H : E →ₗ[ℝ] E), Analysis.Admissible I H →
      ∀ (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise)
        (δ : Fin N → ℝ), ‖initial‖ ≤ 1 →
        Analysis.RelativeErrors h H initial noise u t δ →
        ‖u.output - (aeval H h.terminal) initial‖ ≤ t * (C + ε)

/-- Local relative gain of the actual queries, in the standard epsilon definition
of the upper limit of the dimension-uniform worst normalized error. -/
def localRelativeGain (h : bezout.History N) (I : chebyshev1.SpectralInterval) : ℝ :=
  sInf {C : ℝ | LocalRelativeBound h I C}

/-- Uniform factor bounds control arbitrary operator-norm perturbations. -/
theorem operatorBound_of_product_bounds (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (P Q : Fin N → ℝ)
    (hP : Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s)
    (symmetric : Bool) :
    OperatorBound h I symmetric (Analysis.energyNorm (fun s => P s * Q s)) := by
  intro E _ _ _ H hH D _ hD initial hi
  have hnom (s : Fin N) : ‖(aeval H (h.query s)) initial‖ ≤ Q s :=
    (Analysis.polynomial_action_bound I H hH _ _ (hQ s) (hq s) initial).trans
      (by simpa using mul_le_mul_of_nonneg_left hi (hQ s))
  unfold bezout.History.firstVariation
  calc
    _ ≤ ∑ s, (P s * Q s) * ‖(D s).toContinuousLinearMap‖ := by
      apply Analysis.norm_sum_le_energy
      intro s
      calc
        _ ≤ P s * ‖D s ((aeval H (h.query s)) initial)‖ :=
          Analysis.polynomial_action_bound I H hH _ _ (hP.1 s) (hP.2 s) _
        _ ≤ P s * (‖(D s).toContinuousLinearMap‖ * Q s) :=
          mul_le_mul_of_nonneg_left
            (((D s).toContinuousLinearMap.le_opNorm _).trans
              (mul_le_mul_of_nonneg_left (hnom s) (norm_nonneg _))) (hP.1 s)
        _ = _ := by ring
    _ ≤ _ := by
      have he : ∑ s, ‖(D s).toContinuousLinearMap‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa using hD
      simpa only [mul_one] using Analysis.sum_mul_le_of_energy
        (a := fun s => P s * Q s) zero_le_one he

/-- Uniform factor bounds control the actual-query local relative gain.
The allowed scale is chosen before the dimension and oracle-error stream. -/
theorem localRelativeBound_of_product_bounds (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (P Q : Fin N → ℝ)
    (hP : Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s) :
    LocalRelativeBound h I (Analysis.energyNorm (fun s => P s * Q s)) := by
  let C := Analysis.energyNorm (fun s => P s * Analysis.deviationMajorant h I.L 1 s)
  have hC : 0 ≤ C := Analysis.energyNorm_nonneg _
  intro ε hε
  refine ⟨min 1 (ε / (C + 1)), lt_min zero_lt_one (div_pos hε (by positivity)), ?_⟩
  intro t ht htt E _ _ _ H hH initial noise u δ hi hw
  have ht1 : t ≤ 1 := (htt.trans_le (min_le_left _ _)).le
  have hte : t * (C + 1) < ε :=
    (lt_div_iff₀ (by positivity : 0 < C + 1)).mp (htt.trans_le (min_le_right _ _))
  have hu := Analysis.relative_response_bound h I H hH initial noise u
    1 t 1 zero_le_one ht.le ht1 hi δ hw P Q hP hQ hq
  simp only [mul_one] at hu
  have hre : t ^ 2 * C ≤ t * ε := by nlinarith
  exact hu.trans (by change t * _ + t ^ 2 * C ≤ _; nlinarith)

/-- All operator bounds are nonnegative, as witnessed by the zero initial state. -/
theorem operatorBound_nonneg (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (symmetric : Bool) (C : ℝ) (hb : OperatorBound h I symmetric C) : 0 ≤ C := by
  have hu := hb ℝ (bezout.History.scalarOperator I.mu)
    (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) (fun _ => 0)
    (fun _ _ => LinearMap.IsSymmetric.zero) (by simp) 0 (by simp)
  simpa [bezout.History.firstVariation, bezout.History.variationNoise] using hu

/-- Every asymptotic bound is nonnegative, including at zero oracle errors. -/
theorem localRelativeBound_nonneg (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (C : ℝ) (hb : LocalRelativeBound h I C) : 0 ≤ C := by
  by_contra hc
  have hc : C < 0 := lt_of_not_ge hc
  obtain ⟨t0, ht0, ht⟩ := hb (-C / 2) (by linarith)
  let u := h.run (bezout.History.scalarOperator I.mu) 0 (fun _ => 0)
  have hu := ht (t0 / 2) (by linarith) (by linarith) ℝ
    (bezout.History.scalarOperator I.mu)
    (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) 0 (fun _ => 0) u
    (fun _ => 0) (by simp) ⟨by simp, by simp, by simp⟩
  have hn : ‖u.output - (aeval (bezout.History.scalarOperator I.mu) h.terminal) 0‖ = 0 := by
    rw [h.nominal_output]
    simp
  rw [hn] at hu
  nlinarith

/-- Every finite history has a finite product-bound certificate. -/
theorem exists_product_bounds (h : bezout.History N) (I : chebyshev1.SpectralInterval) :
    ∃ P Q : Fin N → ℝ, Risk.ResponseBounds h I P ∧ (∀ s, 0 ≤ Q s) ∧
      ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s := by
  obtain ⟨P, hP⟩ := Risk.exists_responseBounds h I
  choose Q hQ hq using fun s : Fin N => Analysis.exists_polynomial_bound I (h.query s)
  exact ⟨P, Q, hP, hQ, hq⟩

/-- Both operator-gain comparison sets are nonempty. -/
theorem operatorBounds_nonempty (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (symmetric : Bool) : {C : ℝ | OperatorBound h I symmetric C}.Nonempty := by
  obtain ⟨P, Q, hP, hQ, hq⟩ := exists_product_bounds h I
  exact ⟨_, operatorBound_of_product_bounds h I P Q hP hQ hq symmetric⟩

/-- The local-relative comparison set is nonempty. -/
theorem localRelativeBounds_nonempty (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) : {C : ℝ | LocalRelativeBound h I C}.Nonempty := by
  obtain ⟨P, Q, hP, hQ, hq⟩ := exists_product_bounds h I
  exact ⟨_, localRelativeBound_of_product_bounds h I P Q hP hQ hq⟩

/-- Product bounds imply the operator gain bound for either perturbation class. -/
theorem operatorGain_le_product_energy (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (P Q : Fin N → ℝ)
    (hP : Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s) (symmetric : Bool) :
    operatorGain h I symmetric ≤ Analysis.energyNorm (fun s => P s * Q s) :=
  csInf_le ⟨0, fun C hb => operatorBound_nonneg h I symmetric C hb⟩
    (operatorBound_of_product_bounds h I P Q hP hQ hq symmetric)

/-- Product bounds imply the local relative gain bound. -/
theorem localRelativeGain_le_product_energy (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (P Q : Fin N → ℝ)
    (hP : Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s) :
    localRelativeGain h I ≤ Analysis.energyNorm (fun s => P s * Q s) :=
  csInf_le ⟨0, fun C hb => localRelativeBound_nonneg h I C hb⟩
    (localRelativeBound_of_product_bounds h I P Q hP hQ hq)

end
end bezout.Gains
