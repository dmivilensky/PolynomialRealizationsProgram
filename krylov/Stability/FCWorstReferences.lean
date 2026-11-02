import krylov.Stability.UniformResponseScale
import krylov.Stability.SupremumAsymptotics
import krylov.Variation.FCLocalRemainder
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Use: define actual full-active physical references, real defined-budget FC
scenarios and their true normalized terminal gradient ratios, and bound their
genuine suprema by the actual reference-coefficient supremum plus a uniform quadratic term.
Source: completed genuine scale-free FC quadratic response, true CG error
monotonicity, actual sharp spectral response and the least-upper-bound property.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset Filter Set Topology krylov.Methods krylov.Reference krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- A genuine positive full-active physical quadratic reference with its true spectral condition interval.
Use: A genuine positive full-active physical quadratic reference with its true spectral condition interval.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: All reference quantities are computed by the actual CG definitions. -/
structure FCReference (n : ℕ) (μ κ : ℝ) where
  /-- The actual physical quadratic reference matrix. -/
  base : Matrix (Fin n) (Fin n) ℝ
  /-- The genuine positive-definiteness proof of that actual matrix. -/
  positive : base.PosDef
  /-- The actual physical initial gradient. -/
  gradient : EuclideanSpace ℝ (Fin n)
  /-- The actual reference is initially unsolved. -/
  nonzero : gradient≠0
  /-- The true active CG spectral count equals the physical dimension. -/
  full : referenceAtomCount base positive gradient=n
  /-- The genuine measured eigenvalues lie in the prescribed positive condition interval. -/
  interval : ∀ i, μ≤positive.1.eigenvalues i ∧ positive.1.eigenvalues i≤μ*κ

variable {n : ℕ} {μ κ : ℝ}

/-- The actual canonical initial-error norm of the genuine physical reference.
Use: The actual canonical initial-error norm of the genuine physical reference.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Use the true positive inverse-root error of its real initial gradient. -/
def FCReference.initialNorm (R : FCReference n μ κ) : ℝ := ‖cgCanonicalError R.base R.gradient 0‖

/-- The true normalized spectral response coefficient of the actual reference and finite budget profile.
Use: The true normalized spectral response coefficient of the actual reference and finite budget profile.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Sum the actual remaining CG error norms and divide by the genuine initial canonical error. -/
def FCReference.coefficient (R : FCReference n μ κ) (ω : ℕ → ℝ) : ℝ :=
  (∑ l∈range n, ω l*‖cgCanonicalError R.base R.gradient (l+1)‖)/R.initialNorm

/-- Every actual full-reference initial canonical error factor is strictly positive.
Use: Every actual full-reference initial canonical error factor is strictly positive.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: The genuine inverse root cannot annihilate the actual nonzero gradient. -/
theorem FCReference.initialNorm_pos (R : FCReference n μ κ) : 0<R.initialNorm :=
  norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero R.base R.positive R.gradient R.nonzero)

/-- Every actual reference coefficient lies between zero and the true total budget.
Use: Every actual reference coefficient lies between zero and the true total budget.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: True CG error monotonicity bounds each actual later error by its own genuine initial norm; cancel that positive factor. -/
theorem FCReference.coefficient_bounds (R : FCReference n μ κ) (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) :
    0≤R.coefficient ω ∧ R.coefficient ω≤∑ l∈range n, ω l := by
  -- Keep the actual reference initial norm in each true tail comparison until the final division.
  constructor
  · exact div_nonneg (sum_nonneg fun l hl => mul_nonneg (hω l (mem_range.mp hl)) (norm_nonneg _)) R.initialNorm_pos.le
  · apply (div_le_iff₀ R.initialNorm_pos).mpr
    rw [sum_mul]
    exact sum_le_sum fun l hl => mul_le_mul_of_nonneg_left
      (cgError_antitone R.base R.positive R.gradient (Nat.zero_le (l+1))) (hω l (mem_range.mp hl))

/-- The set of genuine normalized actual-reference coefficients, including zero for an empty reference class.
Use: The set of genuine normalized actual-reference coefficients, including zero for an empty reference class.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Its members come from actual physical CG references. -/
def fcCoefficientSet (n : ℕ) (μ κ : ℝ) (ω : ℕ → ℝ) : Set ℝ :=
  insert 0 (Set.range fun R : FCReference n μ κ => R.coefficient ω)

/-- The true worst-reference spectral coefficient supremum.
Use: The true worst-reference spectral coefficient supremum.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Take the actual least upper bound of the genuine reference coefficient set. -/
def fcWorstCoefficient (n : ℕ) (μ κ : ℝ) (ω : ℕ → ℝ) : ℝ := sSup (fcCoefficientSet n μ κ ω)

/-- The actual reference-coefficient set is bounded by the true total budget.
Use: The actual reference-coefficient set is bounded by the true total budget.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Use the proved individual coefficient bound and the explicit zero convention. -/
theorem fcCoefficientSet_bounded (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) :
    BddAbove (fcCoefficientSet n μ κ ω) := by
  refine ⟨∑ l∈range n, ω l,?_⟩
  intro v hv
  rcases hv with rfl|⟨R,rfl⟩
  · exact sum_nonneg fun l hl => hω l (mem_range.mp hl)
  · exact (R.coefficient_bounds ω hω).2

/-- The true worst-reference spectral coefficient is nonnegative.
Use: The true worst-reference spectral coefficient is nonnegative.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Zero belongs to its genuinely bounded coefficient set. -/
theorem fcWorstCoefficient_nonneg (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) :
    0≤fcWorstCoefficient n μ κ ω :=
  le_csSup (fcCoefficientSet_bounded ω hω) (Set.mem_insert 0 _)

/-- An actual symmetric canonical-increment FC scenario with its genuine component budgets and real solve/search domains.
Use: An actual symmetric canonical-increment FC scenario with its genuine component budgets and real solve/search domains.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: The actual history and physical query executor determine every domain condition. -/
structure FCScenario (R : FCReference n μ κ) (ω : ℕ → ℝ) (t : ℝ) where
  /-- The actual canonical increment matrices used by the real path. -/
  increments : ℕ → Matrix (Fin n) (Fin n) ℝ
  /-- Every true physical canonical increment is symmetric. -/
  symmetric : ∀ l, (increments l).IsSymm
  /-- Each genuine spectral increment norm obeys its actual component budget. -/
  budget : ∀ l<n, ‖increments l‖≤t*ω l
  /-- Every actual executed FC coefficient inverse is genuinely defined. -/
  solve : ∀ i<n, IsUnit (crossGram
    (windowImages (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath R.base increments 1) R.gradient i)))
    (windowSteps (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath R.base increments 1) R.gradient i)))).det
  /-- Every real executed exact-search curvature is nonzero. -/
  curvature : ∀ i<n, inner ℝ (fcDirection fullMemory (canonicalFCPath R.base increments 1) R.gradient i)
    (canonicalFCPath R.base increments 1 i (fcDirection fullMemory (canonicalFCPath R.base increments 1) R.gradient i))≠0

/-- The genuine terminal canonical gradient ratio of the actual defined FC scenario.
Use: The genuine terminal canonical gradient ratio of the actual defined FC scenario.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Normalize its true executed gradient by the actual initial canonical error. -/
def FCScenario.ratio {R : FCReference n μ κ} {ω : ℕ → ℝ} {t : ℝ} (S : FCScenario R ω t) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot R.base)⁻¹
    (fcGradient fullMemory (canonicalFCPath R.base S.increments 1) R.gradient n)‖/R.initialNorm

/-- Every actual defined FC scenario satisfies the true sharp reference upper coefficient plus the global uniform quadratic error.
Use: Every actual defined FC scenario satisfies the true sharp reference upper coefficient plus the global uniform quadratic error.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Bound the real total increment budget, apply the genuine scale-free quadratic response theorem and actual spectral response bound, and divide by the true positive initial error. -/
theorem FCScenario.ratio_le {R : FCReference n μ κ} {ω : ℕ → ℝ} {t : ℝ} (S : FCScenario R ω t)
    (hμ : 0<μ) (hκ : 1≤κ) (hsmall : 8*((n : ℝ)+1)*(t*(∑ l∈range n, ω l))≤1) :
    S.ratio≤t*R.coefficient ω+fcResponseConstant n κ*t^2*(∑ l∈range n, ω l)^2 := by
  -- All budget and remainder quantities below belong to this actual defined physical FC scenario.
  let W := ∑ l∈range n, ‖S.increments l‖
  have hW : 0≤W := sum_nonneg fun _ _ => norm_nonneg _
  have hWle : W≤t*(∑ l∈range n, ω l) := by
    rw [mul_sum]
    exact sum_le_sum fun l hl => S.budget l (mem_range.mp hl)
  have hsmallW : 8*((n : ℝ)+1)*W≤1 :=
    (mul_le_mul_of_nonneg_left hWle (by positivity)).trans hsmall
  have hrem := fullFC_uniform_quadratic_response_scale R.base R.positive S.increments S.symmetric
    R.gradient hμ hκ R.interval R.full S.solve S.curvature hsmallW
  have hF := spectral_response_le R.base R.gradient (range n) S.increments (fun l => t*ω l)
    (fun l hl => S.budget l (mem_range.mp hl))
  have hsq : W^2≤(t*(∑ l∈range n, ω l))^2 := sq_le_sq₀ hW (hW.trans hWle) |>.mpr hWle
  have hC := fcResponseConstant_nonneg (n := n) (le_trans (by norm_num) hκ)
  have hrem' := hrem.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC) R.initialNorm_pos.le)
  have htri := norm_le_norm_sub_add
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot R.base)⁻¹
      (fcGradient fullMemory (canonicalFCPath R.base S.increments 1) R.gradient n))
    (fullCycleResponse R.base R.gradient (range n) S.increments)
  apply (div_le_iff₀ R.initialNorm_pos).mpr
  have hf' : (∑ l∈range n, (t*ω l)*‖cgCanonicalError R.base R.gradient (l+1)‖)=
      t*(∑ l∈range n, ω l*‖cgCanonicalError R.base R.gradient (l+1)‖) := by
    rw [mul_sum];exact sum_congr rfl fun _ _ => by ring
  rw [hf'] at hF
  have hcoef : R.coefficient ω*R.initialNorm=∑ l∈range n, ω l*‖cgCanonicalError R.base R.gradient (l+1)‖ :=
    div_mul_cancel₀ _ R.initialNorm_pos.ne'
  change _≤fcResponseConstant n κ*(t*(∑ l∈range n, ω l))^2*R.initialNorm at hrem'
  rw [← hcoef] at hF
  nlinarith

/-- The true feasible normalized FC terminal ratios over all genuine references and defined budget scenarios.
Use: The true feasible normalized FC terminal ratios over all genuine references and defined budget scenarios.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Include the actual zero value convention for an empty reference class. -/
def fcValueSet (n : ℕ) (μ κ : ℝ) (ω : ℕ → ℝ) (t : ℝ) : Set ℝ :=
  insert 0 (Set.range fun q : (Σ R : FCReference n μ κ, FCScenario R ω t) => q.2.ratio)

/-- The actual worst-reference and worst-scenario FC terminal gradient ratio.
Use: The actual worst-reference and worst-scenario FC terminal gradient ratio.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Take the true least upper bound of the genuine feasible normalized ratios. -/
def fcWorstRatio (n : ℕ) (μ κ : ℝ) (ω : ℕ → ℝ) (t : ℝ) : ℝ :=
  sSup (fcValueSet n μ κ ω t)

/-- All actual feasible FC ratios have the printed worst-reference linear plus uniform quadratic upper bound.
Use: All actual feasible FC ratios have the printed worst-reference linear plus uniform quadratic upper bound.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Bound each genuine reference coefficient by its true coefficient supremum and use the actual scenario estimate. -/
theorem fcValueSet_upper (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) (hμ : 0<μ) (hκ : 1≤κ)
    {t : ℝ} (ht : 0≤t) (hsmall : 8*((n : ℝ)+1)*(t*(∑ l∈range n, ω l))≤1) :
    ∀ v∈fcValueSet n μ κ ω t,
      v≤t*fcWorstCoefficient n μ κ ω+fcResponseConstant n κ*t^2*(∑ l∈range n, ω l)^2 := by
  intro v hv
  rcases hv with rfl|⟨⟨R,S⟩,rfl⟩
  · exact add_nonneg (mul_nonneg ht (fcWorstCoefficient_nonneg ω hω))
      (by have := fcResponseConstant_nonneg (n := n) (le_trans (by norm_num) hκ);positivity)
  · have hcoef : R.coefficient ω≤fcWorstCoefficient n μ κ ω :=
      le_csSup (fcCoefficientSet_bounded ω hω) (Set.mem_insert_of_mem _ (Set.mem_range_self R))
    exact (S.ratio_le hμ hκ hsmall).trans (add_le_add (mul_le_mul_of_nonneg_left hcoef ht) le_rfl)

/-- The genuine small-budget defined FC feasible-ratio set is bounded above.
Use: The genuine small-budget defined FC feasible-ratio set is bounded above.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: Use the actual uniform spectral-plus-quadratic upper bound. -/
theorem fcValueSet_bounded (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) (hμ : 0<μ) (hκ : 1≤κ)
    {t : ℝ} (ht : 0≤t) (hsmall : 8*((n : ℝ)+1)*(t*(∑ l∈range n, ω l))≤1) :
    BddAbove (fcValueSet n μ κ ω t) := ⟨_,fcValueSet_upper ω hω hμ hκ ht hsmall⟩

/-- The actual worst-reference FC terminal ratio has the printed uniform quadratic upper estimate.
Use: The actual worst-reference FC terminal ratio has the printed uniform quadratic upper estimate.
Article: main_krylov, thm:A, genuine worst-reference FC upper estimates.
Proof: The true feasible set contains zero and every actual member has the proved genuine upper bound. -/
theorem fcWorstRatio_upper (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) (hμ : 0<μ) (hκ : 1≤κ)
    {t : ℝ} (ht : 0≤t) (hsmall : 8*((n : ℝ)+1)*(t*(∑ l∈range n, ω l))≤1) :
    fcWorstRatio n μ κ ω t≤t*fcWorstCoefficient n μ κ ω+
      fcResponseConstant n κ*t^2*(∑ l∈range n, ω l)^2 :=
  csSup_le ⟨0,Set.mem_insert 0 _⟩ (fcValueSet_upper ω hω hμ hκ ht hsmall)

end
end krylov.Stability
