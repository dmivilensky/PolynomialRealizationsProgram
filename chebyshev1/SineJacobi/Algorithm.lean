import chebyshev1.SineJacobi.Gain

/-!
Article: chebyshev1, Algorithm 2.
Terminal exactness for the independently defined iterates of Algorithm 2.
Result: `chebyshev1.SineJacobi.quadraticError_exact` supplies the stated article conclusion.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Polynomial
variable (I : SpectralInterval)

/--
Algorithm 2's initial gradient step.

Exact identity `((data N).method I).a 0 = 1 ∧ ((data N).method I).b 0 = 0 ∧ ((data N).method
I).gamma 0 = 2/(I.L+I.mu)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Algorithm 2.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem method_initial (N : ℕ) :
    ((data N).method I).a 0 = 1 ∧ ((data N).method I).b 0 = 0 ∧
      ((data N).method I).gamma 0 = 2/(I.L+I.mu) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have heta : I.eta ≠ 0 := ne_of_gt (lt_trans zero_lt_one I.eta_gt_one)
  simp only [JacobiData.method, JacobiData.den_zero, JacobiData.den_one, data_b,
    data_aSq_zero, Nat.zero_add, sub_zero, zero_mul, zero_div, neg_zero, mul_one]
  constructor
  · field_simp
  · constructor
    · trivial
    · unfold SpectralInterval.eta
      field_simp [ne_of_gt I.delta_pos]

/--
Algorithm 2's explicit coefficients at each used later step.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Algorithm 2.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.data_aSq` with the arguments
shown in the proof.
-/
theorem method_coefficients (N s : ℕ) (hs : 0 < s) (hsN : s < N) :
    ((data N).method I).a s = I.eta*(data N).den I s/(data N).den I (s+1) ∧
    ((data N).method I).b s = -couplingSq N s*(data N).den I (s-1)/(data N).den I (s+1) ∧
    ((data N).method I).gamma s = 2*(data N).den I s/(I.delta*(data N).den I (s+1)) := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.data_aSq` with the arguments shown
  -- in the proof.
  simp only [JacobiData.method, data_b, sub_zero, data_aSq N s hs hsN]
  constructor
  · ring
  · constructor <;> ring

/--
Terminal exactness for the independently defined iterates of Algorithm 2.

Exact identity `((data N).method I).quadraticError H e0 N = (aeval H (I.residual N)).mulVec
e0`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Algorithm 2.

Proof: Use the identities/estimates `chebyshev1.JacobiData.terminal_exact`,
`chebyshev1.SineJacobi.admissible`, `chebyshev1.SineJacobi.terminal` with the arguments
shown in the proof.
-/
theorem quadraticError_exact {d : Type*} [Fintype d] [DecidableEq d]
    (N : ℕ) (hN : 0 < N) (H : Matrix d d ℝ) (e0 : d → ℝ) :
    ((data N).method I).quadraticError H e0 N = (aeval H (I.residual N)).mulVec e0 :=
  (data N).terminal_exact I (admissible I N hN)
    (by positivity : (2/(2:ℝ)^N) ≠ 0) (terminal N hN) H e0
end
end chebyshev1.SineJacobi
