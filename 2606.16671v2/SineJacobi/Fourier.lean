import «2606.16671v2».SineJacobi.RogersPolynomial

/-!
Article: 2606.16671v2, Lemma E.2.
E.2's finite Fourier identity is derived from the explicit sine recurrence.
Use: `«2606.16671v2».SineJacobi.leading_fourier` feeds
`«2606.16671v2».SineJacobi.normalized_fourier` (The endpoint-normalized nonnegative cosine expansion
in E.2).
Proof chain: `«2606.16671v2».SineJacobi.endpoint_global_bound` — 2606.16671v2, Theorem E.3;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Polynomial Real
open scoped BigOperators

/--
Defines `cosineTransform` of type `ℝ[X] →ₗ[ℝ] ℝ` by `Polynomial.lsum (fun k => { toFun := fun a
=> a*cos (((n:ℝ)-2*(k:ℝ))*theta) map_add' := fun _ _ => by ring map_smul' := fun _ _ => by simp
[mul_assoc] })`.

Use: `«2606.16671v2».SineJacobi.cosineTransform_X` uses this definition to establish exact
identity `cosineTransform n theta X = cos (((n:ℝ)-2)*theta)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.leading_endpoint_max`.
-/
def cosineTransform (n : ℤ) (theta : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun k =>
    { toFun := fun a => a*cos (((n:ℝ)-2*(k:ℝ))*theta)
      map_add' := fun _ _ => by ring
      map_smul' := fun _ _ => by simp [mul_assoc] })

/--
Exact identity `cosineTransform n theta (monomial k a) = a*cos (((n:ℝ)-2*(k:ℝ))*theta)`.

Use: `«2606.16671v2».SineJacobi.cosineTransform_C` rewrites with this identity to establish
exact identity `cosineTransform n theta (C a) = a*cos ((n:ℝ)*theta)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.leading_endpoint_max`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem cosineTransform_monomial (n : ℤ) (theta a : ℝ) (k : ℕ) :
    cosineTransform n theta (monomial k a) = a*cos (((n:ℝ)-2*(k:ℝ))*theta) := by simp [cosineTransform, lsum_apply, sum_monomial_index]

/--
Exact identity `cosineTransform n theta (C a) = a*cos ((n:ℝ)*theta)`.

Use: `«2606.16671v2».SineJacobi.cosineTransform_one` rewrites with this identity to establish
exact identity `cosineTransform n theta 1 = cos ((n:ℝ)*theta)`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.cosineTransform_monomial` with
the arguments shown in the proof.
-/
@[simp] theorem cosineTransform_C (n : ℤ) (theta a : ℝ) :
    cosineTransform n theta (C a) = a*cos ((n:ℝ)*theta) := by
  rw [← monomial_zero_left, cosineTransform_monomial]
  simp

/--
Exact identity `cosineTransform n theta 1 = cos ((n:ℝ)*theta)`.

Use: `«2606.16671v2».SineJacobi.leading_cosineTransform` rewrites with this identity to
establish exact identity `(2:ℝ)^s*((data N).leading s).eval (cos theta) = cosineTransform (s:ℤ)
theta (rogers N s)`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.cosineTransform_C` with the
arguments shown in the proof.
-/
@[simp] theorem cosineTransform_one (n : ℤ) (theta : ℝ) :
    cosineTransform n theta 1 = cos ((n:ℝ)*theta) := by
  change cosineTransform n theta (C 1) = _
  rw [cosineTransform_C]
  simp

/--
Exact identity `cosineTransform n theta X = cos (((n:ℝ)-2)*theta)`.

Use: `«2606.16671v2».SineJacobi.leading_cosineTransform` rewrites with this identity to
establish exact identity `(2:ℝ)^s*((data N).leading s).eval (cos theta) = cosineTransform (s:ℤ)
theta (rogers N s)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.leading_endpoint_max`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem cosineTransform_X (n : ℤ) (theta : ℝ) :
    cosineTransform n theta X = cos (((n:ℝ)-2)*theta) := by
  change cosineTransform n theta (monomial 1 1) = _
  simp

/--
Exact identity `cosineTransform n theta (X*p) = cosineTransform (n-2) theta p`.

Use: `«2606.16671v2».SineJacobi.cosineTransform_recurrence` rewrites with this identity to
establish exact identity `cosineTransform (n+1) theta ((1+X)*p-C c*X*q) = 2*cos
theta*cosineTransform n theta p-c*cosineTransform (n-1) theta q`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Induct on `p`; the recursive step uses the previous-stage assertion.
-/
theorem cosineTransform_X_mul (n : ℤ) (theta : ℝ) (p : ℝ[X]) :
    cosineTransform n theta (X*p) = cosineTransform (n-2) theta p := by
  -- Induct on `p`; the recursive step uses the previous-stage assertion.
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
  | monomial k a =>
    rw [X_mul_monomial, cosineTransform_monomial, cosineTransform_monomial]
    congr 2
    push_cast
    ring

/--
Exact identity `cosineTransform (n+1) theta p + cosineTransform (n-1) theta p = 2*cos
theta*cosineTransform n theta p`.

Use: `«2606.16671v2».SineJacobi.cosineTransform_recurrence` rewrites with this identity to
establish exact identity `cosineTransform (n+1) theta ((1+X)*p-C c*X*q) = 2*cos
theta*cosineTransform n theta p-c*cosineTransform (n-1) theta q`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Induct on `p`; the recursive step uses the previous-stage assertion.
-/
theorem cosineTransform_modes (n : ℤ) (theta : ℝ) (p : ℝ[X]) :
    cosineTransform (n+1) theta p + cosineTransform (n-1) theta p =
      2*cos theta*cosineTransform n theta p := by
  -- Induct on `p`; the recursive step uses the previous-stage assertion.
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add]; rw [mul_add]; linarith
  | monomial k a =>
    simp only [cosineTransform_monomial, Int.cast_add, Int.cast_sub, Int.cast_one]
    rw [show ((n:ℝ)+1-2*(k:ℝ))*theta = ((n:ℝ)-2*(k:ℝ))*theta+theta by ring,
      show ((n:ℝ)-1-2*(k:ℝ))*theta = ((n:ℝ)-2*(k:ℝ))*theta-theta by ring,
      cos_add, cos_sub]
    ring

/--
Exact identity `cosineTransform (n+1) theta ((1+X)*p-C c*X*q) = 2*cos theta*cosineTransform n
theta p-c*cosineTransform (n-1) theta q`.

Use: `«2606.16671v2».SineJacobi.leading_cosineTransform` rewrites with this identity to
establish exact identity `(2:ℝ)^s*((data N).leading s).eval (cos theta) = cosineTransform (s:ℤ)
theta (rogers N s)`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.cosineTransform_X_mul`,
`«2606.16671v2».SineJacobi.cosineTransform_modes` with the arguments shown in the proof.
-/
theorem cosineTransform_recurrence (n : ℤ) (theta c : ℝ) (p q : ℝ[X]) :
    cosineTransform (n+1) theta ((1+X)*p-C c*X*q) =
      2*cos theta*cosineTransform n theta p-c*cosineTransform (n-1) theta q := by
  rw [add_mul, one_mul, mul_assoc, ← smul_eq_C_mul, map_sub, map_add, map_smul,
    cosineTransform_X_mul, cosineTransform_X_mul]
  rw [show n+1-2 = n-1 by omega, cosineTransform_modes]
  rfl

/--
E.2's finite Fourier identity is derived from the explicit sine recurrence.

Exact identity `(2:ℝ)^s*((data N).leading s).eval (cos theta) = cosineTransform (s:ℤ) theta
(rogers N s)`.

Use: `«2606.16671v2».SineJacobi.leading_fourier` rewrites with this identity to establish exact
identity `(2:ℝ)^s*((data N).leading s).eval (cos theta) = ∑ k ∈ Finset.range (s+1), coefficient
N s k*cos (((s:ℝ)-2*(k:ℝ))*theta)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.leading_endpoint_max`.

Proof: Induct on `s`; the recursive step uses the previous-stage assertion.
-/
theorem leading_cosineTransform (N s : ℕ) (hs : s < N) (theta : ℝ) :
    (2:ℝ)^s*((data N).leading s).eval (cos theta) = cosineTransform (s:ℤ) theta (rogers N s) := by
  -- Induct on `s`; the recursive step uses the previous-stage assertion.
  induction s using Nat.twoStepInduction with
  | zero => simp [JacobiData.leading, JacobiData.block, rogers_zero N (by omega)]
  | one =>
    simp only [JacobiData.leading_one, data_b, C_0, sub_zero, eval_X, pow_one,
      rogers_one N hs, map_add, cosineTransform_one, cosineTransform_X]
    norm_num
    ring
  | more s ih0 ih1 =>
    have hs0 : s < N := by omega
    have hs1 : s+1 < N := by omega
    rw [show s+2 = (s+1)+1 by omega, rogers_recurrence N (s+1) hs (by omega)]
    rw [show ((s+1+1:ℕ):ℤ) = ((s+1:ℕ):ℤ)+1 by omega, cosineTransform_recurrence]
    rw [← ih1 hs1, show ((s+1:ℕ):ℤ)-1 = (s:ℤ) by omega, Nat.add_sub_cancel, ← ih0 hs0]
    have hr : (data N).leading (s+2) = X*(data N).leading (s+1) -
        C (couplingSq N (s+1))*(data N).leading s := by
      simp only [JacobiData.leading, JacobiData.block, data_b, C_0, sub_zero, Nat.zero_add]
      rw [data_aSq N (s+1) (by omega) hs1]
    rw [show s+1+1 = s+2 by omega, hr]
    simp only [eval_sub, eval_mul, eval_X, eval_C, pow_succ]
    ring

/--
Exact identity `(2:ℝ)^s*((data N).leading s).eval (cos theta) = ∑ k ∈ Finset.range (s+1),
coefficient N s k*cos (((s:ℝ)-2*(k:ℝ))*theta)`.

Use: `«2606.16671v2».SineJacobi.endpoint_sum` uses this identity to establish the identity
`endpoint N s = ∑ k ∈ Finset.range (s+1), coefficient N s k`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.leading_endpoint_max`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem leading_fourier (N s : ℕ) (hs : s < N) (theta : ℝ) :
    (2:ℝ)^s*((data N).leading s).eval (cos theta) =
      ∑ k ∈ Finset.range (s+1), coefficient N s k*cos (((s:ℝ)-2*(k:ℝ))*theta) := by
  rw [leading_cosineTransform N s hs, rogers, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [C_mul_X_pow_eq_monomial, cosineTransform_monomial, Int.cast_natCast]

end
end «2606.16671v2».SineJacobi
