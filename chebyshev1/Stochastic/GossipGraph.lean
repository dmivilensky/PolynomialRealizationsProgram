import chebyshev1.Stochastic.Gossip
import chebyshev1.Spectral.OperatorNorm
import chebyshev1.TwoTerm.VariableHessian

/-!
The edge-incidence Laplacian model, exact preservation of the average, and the
edge-dropout covariance after an arbitrary deterministic linear response.
-/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {d e Ω : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The signed incidence vector of an edge, including a zero vector for a loop. -/
def incidence (u v : d) : d → ℝ := Pi.single u 1 - Pi.single v 1

theorem incidence_sum (u v : d) : ∑ i, incidence u v i = 0 := by
  simp [incidence, Finset.sum_sub_distrib]

/-- A weighted incidence Laplacian. No orientation choice affects the matrix. -/
def edgeLaplacian (w : e → ℝ) (b : e → d → ℝ) : Matrix d d ℝ :=
  ∑ a, w a • Matrix.vecMulVec (b a) (b a)

omit [DecidableEq d] [DecidableEq e] in
theorem edgeLaplacian_mulVec (w : e → ℝ) (b : e → d → ℝ) (v : d → ℝ) :
    (edgeLaplacian w b).mulVec v = ∑ a, (w a * dotProduct (b a) v) • b a := by
  simp [edgeLaplacian, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    smul_smul]

omit [DecidableEq d] [DecidableEq e] in
/-- Every edge realization has a zero-sum gradient, so a fixed-point two-term method preserves averages. -/
theorem edgeLaplacian_mulVec_sum (w : e → ℝ) (b : e → d → ℝ)
    (hb : ∀ a, ∑ i, b a i = 0) (v : d → ℝ) :
    ∑ i, (edgeLaplacian w b).mulVec v i = 0 := by
  rw [edgeLaplacian_mulVec]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, hb]

/-- Independently active edges have their weights divided by the activation probability. -/
def dropoutLaplacian (p : ℝ) (A : e → Set Ω) (w : e → ℝ)
    (b : e → d → ℝ) (ω : Ω) : Matrix d d ℝ :=
  edgeLaplacian (fun a => ((A a).indicator (1 : Ω → ℝ) ω / (1-p)) * w a) b

/-- Oracle error about the full Laplacian, in Euclidean coordinates. -/
def gossipOracleNoise (p : ℝ) (A : e → Set Ω) (w : e → ℝ)
    (b : e → d → ℝ) (v : d → ℝ) (ω : Ω) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 ((dropoutLaplacian p A w b ω - edgeLaplacian w b).mulVec v)

omit [MeasurableSpace Ω] [DecidableEq d] [DecidableEq e] in
theorem gossipOracleNoise_eq (p : ℝ) (A : e → Set Ω) (w : e → ℝ)
    (b : e → d → ℝ) (v : d → ℝ) (ω : Ω) :
    gossipOracleNoise p A w b v ω =
      ∑ a, dropoutNoise p (A a) ω •
        ((w a * dotProduct (b a) v) • WithLp.toLp 2 (b a)) := by
  simp only [gossipOracleNoise, Matrix.sub_mulVec, dropoutLaplacian,
    edgeLaplacian_mulVec, ← Finset.sum_sub_distrib, WithLp.toLp_sum, WithLp.toLp_sub,
    WithLp.toLp_smul, dropoutNoise, smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  module

omit [DecidableEq d] in
/-- The covariance formula after any deterministic tail or test operator. -/
theorem gossipOracleNoise_secondMoment (p : ℝ) (hp : p < 1) (A : e → Set Ω)
    (hA : ∀ a, MeasurableSet (A a)) (hind : iIndepSet A μ)
    (hprob : ∀ a, μ.real (A a) = 1-p) (w : e → ℝ) (b : e → d → ℝ)
    (v : d → ℝ) (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    (∫ ω, ‖T (gossipOracleNoise p A w b v ω)‖ ^ 2 ∂μ) =
      p/(1-p) * ∑ a, (w a)^2 * (dotProduct (b a) v)^2 * ‖T (WithLp.toLp 2 (b a))‖^2 := by
  simp_rw [gossipOracleNoise_eq, map_sum, map_smul]
  rw [dropout_sum_secondMoment p hp A hA hind hprob]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]

end
end chebyshev1.Stochastic

namespace chebyshev1.TwoTerm
noncomputable section
open scoped BigOperators
variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- Average preservation for every realized sequence of incidence Laplacians. -/
theorem variableError_sum_invariant (S : chebyshev1.TwoTerm) (H : ℕ → Matrix d d ℝ)
    (hzero : ∀ s v, ∑ i, (H s).mulVec v i = 0)
    (hfixed : ∀ s, 0 < s → S.a s + S.b s = 1) (e0 : d → ℝ) (t : ℕ) :
    ∑ i, S.variableError H e0 t i = ∑ i, e0 i := by
  induction t using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [variableError, Finset.sum_sub_distrib, ← Finset.mul_sum, hzero]
  | more t ih0 ih1 =>
    simp only [variableError, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hzero,
      mul_zero, sub_zero, ih0, ih1]
    rw [← add_mul, hfixed (t+1) (by omega), one_mul]

end
end chebyshev1.TwoTerm
