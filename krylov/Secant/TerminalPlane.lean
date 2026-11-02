import krylov.LinearAlgebra.PlanarWitness
import krylov.LinearAlgebra.BlockCompletion
import krylov.LinearAlgebra.MatrixEquiv
import krylov.LinearAlgebra.InformationRadius
import Mathlib.Algebra.BigOperators.Intervals

/-!
Article: main_krylov, lem:terminal-fibre, actual two-dimensional operator construction.
Use: construct the actual segment sequence, hidden final diagonal and common
last probe; apply the proved information radius to the actual final matrices.
Source: exact finite telescoping, the proved actual planar matrix action and
the earlier two-scenario Hilbert-space lower bound.
-/

namespace krylov.Secant
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- The actual planar segment sequence with the accumulated terminal h-diagonal cancelled in its base.
Use: all operators are concrete matrices and all prescribed perturbations are their actual differences.
Article: main_krylov, lem:terminal-fibre, Â₀ and the increments Ê_l. -/
def terminalSegments (e h : EuclideanSpace ℝ (Fin n)) (x y z : ℕ → ℝ) (N k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  1+planarMatrix e h (∑ l ∈ Finset.range k, y l) (∑ l ∈ Finset.range k, x l)
    ((∑ l ∈ Finset.range k, z l)-(∑ l ∈ Finset.range N, z l))

/-- The actual planar segment sequence starts at the prescribed hidden base.
Use: base uncertainty annihilates the first canonical reference step.
Article: main_krylov, lem:terminal-fibre, Â₀=I−zhhᵀ.
Proof: the three actual empty prefix sums are zero. -/
theorem terminalSegments_zero (e h : EuclideanSpace ℝ (Fin n)) (x y z : ℕ → ℝ) (N : ℕ) :
    terminalSegments e h x y z N 0=1-(∑ l ∈ Finset.range N, z l) •
      vecMulVec (WithLp.ofLp h) (WithLp.ofLp h) := by
  simp only [terminalSegments, Finset.sum_range_zero, planarMatrix, zero_smul,
    zero_add, neg_smul, sub_eq_add_neg]

/-- Every actual difference is exactly the prescribed symmetric planar increment.
Use: the data-fibre construction satisfies its true operator-sequence model.
Article: main_krylov, lem:terminal-fibre, Ê_l=x_l(ehᵀ+heᵀ)+y_leeᵀ+z_lhhᵀ.
Proof: telescope the actual prefix sums and distribute the actual outer-product scalar coefficients. -/
theorem terminalSegments_increment (e h : EuclideanSpace ℝ (Fin n))
    (x y z : ℕ → ℝ) (N k : ℕ) :
    terminalSegments e h x y z N (k+1)-terminalSegments e h x y z N k=
      planarMatrix e h (y k) (x k) (z k) := by
  simp only [terminalSegments, Finset.sum_range_succ, planarMatrix, add_smul, sub_smul]
  module

/-- The actual normalized terminal probe is independent of both hidden diagonal allocations.
Use: the final observation reveals only the accumulated cross coefficient x.
Article: main_krylov, lem:terminal-fibre, last probe h+xe.
Proof: the actual h-diagonal prefix cancels its actual base coefficient;
the true planar action uses the actual unit/orthogonal pairings. -/
theorem terminalSegments_last_probe (e h : EuclideanSpace ℝ (Fin n))
    (hh : ‖h‖=1) (heh : inner ℝ e h=0) (x y z : ℕ → ℝ) (N : ℕ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (terminalSegments e h x y z N N) h=
      h+(∑ l ∈ Finset.range N, x l) • e := by
  simp only [terminalSegments, sub_self, map_add, map_one, _root_.add_apply,
    one_apply_eq_self, planarMatrix_action, heh, real_inner_self_eq_norm_sq, hh,
    one_pow, mul_zero, zero_add, mul_one, zero_smul, add_zero]

/-- Every actual middle direction orthogonal to the two-dimensional plane has exactly the reference probe.
Use: the planar perturbations remain invisible throughout the middle reference probes.
Article: main_krylov, lem:terminal-fibre, middle-direction annihilation.
Proof: both actual planar action pairings vanish. -/
theorem terminalSegments_middle_probe (e h v : EuclideanSpace ℝ (Fin n))
    (hev : inner ℝ e v=0) (hhv : inner ℝ h v=0)
    (x y z : ℕ → ℝ) (N k : ℕ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (terminalSegments e h x y z N k) v=v := by
  simp only [terminalSegments, map_add, map_one, _root_.add_apply, one_apply_eq_self,
    planarMatrix_action, hev, hhv, mul_zero, add_zero, zero_smul]

/-- The actual first reference probe is unchanged by the actual hidden base.
Use: initializes the transcript-indistinguishability induction at the genuine first direction.
Article: main_krylov, lem:terminal-fibre, base change annihilates e.
Proof: the hidden base acts only in the actual orthogonal h direction. -/
theorem terminalSegments_first_probe (e h : EuclideanSpace ℝ (Fin n))
    (heh : inner ℝ e h=0) (x y z : ℕ → ℝ) (N : ℕ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (terminalSegments e h x y z N 0) e=e := by
  have hh := real_inner_comm e h |>.trans heh
  simp only [terminalSegments, Finset.sum_range_zero, map_add, map_one, _root_.add_apply,
    one_apply_eq_self, planarMatrix_action, hh, zero_mul, mul_zero, zero_smul, add_zero]

/-- The true final output operator has exactly the common cross model plus its hidden e-diagonal.
Use: the final output uncertainty is independent of the common terminal probe.
Article: main_krylov, lem:terminal-fibre, B̂=M+beeᵀ.
Proof: the actual terminal h-diagonal has cancelled, and the final e-diagonal
adds to the actual accumulated y coefficient. -/
theorem terminalSegments_output (e h : EuclideanSpace ℝ (Fin n)) (x y z : ℕ → ℝ)
    (N : ℕ) (ζ : ℝ) :
    terminalSegments e h x y z N N+ζ • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)=
      (1+planarMatrix e h 0 (∑ l ∈ Finset.range N, x l) 0)+
        ((∑ l ∈ Finset.range N, y l)+ζ) • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) := by
  simp only [terminalSegments, sub_self, planarMatrix, zero_smul, add_zero, zero_add, add_smul]
  abel

/-- The actual common terminal cross model is positive definite whenever |x|<1.
Use: the actual centre solve and the true two-scenario inverse have a justified domain.
Article: main_krylov, lem:terminal-fibre, M invertible.
Proof: the proved genuine planar unit-norm witness bounds its cross block;
the strict shifted-positive theorem then applies to the actual scaled increment. -/
theorem terminal_cross_posDef (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) {x : ℝ} (hx : |x|<1) :
    (1+planarMatrix e h 0 x 0).PosDef := by
  have hc : chebyshev1.opNorm (planarMatrix e h 0 1 0)≤1 := by
    simpa only [neg_zero] using planar_spectral_norm_le e h he hh heh 0 1 (by norm_num)
  have heq : planarMatrix e h 0 x 0=x • planarMatrix e h 0 1 0 := by
    simp only [planarMatrix, zero_smul, one_smul, zero_add, add_zero]
  have hn : chebyshev1.opNorm (planarMatrix e h 0 x 0)<1 := by
    rw [heq, chebyshev1.opNorm_smul]
    exact (mul_le_mul_of_nonneg_left hc (abs_nonneg _)).trans_lt (by simpa only [mul_one] using hx)
  simpa only [one_smul] using (strict_shifted_posDef _ (planarMatrix_isSymm e h 0 x 0) hn).2

end
end krylov.Secant
