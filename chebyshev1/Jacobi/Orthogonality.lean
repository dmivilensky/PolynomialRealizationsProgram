import chebyshev1.Jacobi.InverseUniqueness
import chebyshev1.Spectral.Weights

/-!
Article: chebyshev1, Lemma E.2.
Discrete orthogonality of the monic leading polynomials for the first spectral measure.
Use: `chebyshev1.JacobiData.leading_orthogonality` feeds
`chebyshev1.SineJacobi.leading_orthogonality` (E.2's monic orthogonality, derived from the
explicit chain and its actual spectral weights).
Proof chain: `chebyshev1.SineJacobi.leading_orthogonality` — chebyshev1, Lemma E.2;
Root-of-unity Rogers recurrence, Fourier coefficients and orthogonality.
-/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData)

/--
Coordinate vector at a site; it is zero beyond the finite horizon.

Use: `chebyshev1.JacobiData.leading_aeval_site` uses this definition to establish exact
identity `aeval (J.matrix 0 N) (J.leading s) *ᵥ site N 0 = J.linkProduct s • site N s`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.leading_orthogonality`.
-/
def site (N s : ℕ) : Fin N → ℝ := fun i => if i.val = s then 1 else 0

/--
Defines `linkProduct` of type `ℝ` by `∏ t ∈ Finset.range s, Real.sqrt (J.aSq (t+1))`.

Use: `chebyshev1.JacobiData.leading_aeval_site` uses this definition to establish exact
identity `aeval (J.matrix 0 N) (J.leading s) *ᵥ site N 0 = J.linkProduct s • site N s`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.leading_orthogonality`.
-/
def linkProduct (s : ℕ) : ℝ := ∏ t ∈ Finset.range s, Real.sqrt (J.aSq (t+1))

/--
Exact identity `J.linkProduct 0 = 1`.

Use: `chebyshev1.JacobiData.leading_aeval_site` rewrites with this identity to establish
exact identity `aeval (J.matrix 0 N) (J.leading s) *ᵥ site N 0 = J.linkProduct s • site N s`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.leading_orthogonality`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem linkProduct_zero : J.linkProduct 0 = 1 := by simp [linkProduct]
/--
Exact identity `J.linkProduct (s+1) = J.linkProduct s * Real.sqrt (J.aSq (s+1))`.

Use: `chebyshev1.JacobiData.leading_aeval_site` rewrites with this identity to establish
exact identity `aeval (J.matrix 0 N) (J.leading s) *ᵥ site N 0 = J.linkProduct s • site N s`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.leading_orthogonality`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
@[simp] theorem linkProduct_succ (s : ℕ) :
    J.linkProduct (s+1) = J.linkProduct s * Real.sqrt (J.aSq (s+1)) := Finset.prod_range_succ _ _

/--
Exact identity `site N s = Pi.single (⟨s,hs⟩ : Fin N) 1`.

Use: `chebyshev1.JacobiData.leading_orthogonality` rewrites with this identity to establish
the precise assertion is `let B`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.leading_orthogonality`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem site_eq_single (N s : ℕ) (hs : s < N) :
    site N s = Pi.single (⟨s,hs⟩ : Fin N) 1 := by
  funext i
  simp [site, Pi.single_apply, Fin.ext_iff, eq_comm]

/--
Exact identity `J.matrix 0 N *ᵥ site N 0 = J.b 0 • site N 0 + Real.sqrt (J.aSq 1) • site N 1`.

Use: `chebyshev1.JacobiData.leading_aeval_site` rewrites with this identity to establish
exact identity `aeval (J.matrix 0 N) (J.leading s) *ᵥ site N 0 = J.linkProduct s • site N s`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.leading_orthogonality`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem matrix_site_zero (N : ℕ) (hN : 0 < N) :
    J.matrix 0 N *ᵥ site N 0 = J.b 0 • site N 0 + Real.sqrt (J.aSq 1) • site N 1 := by
  conv_lhs => rw [site_eq_single N 0 hN, Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply, J.matrix_apply]
  simp only [Nat.zero_add, Fin.ext_iff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, site]
  split_ifs <;> simp only [mul_one, mul_zero, add_zero, zero_add]
  all_goals first | contradiction | omega | congr 2

/--
Exact identity `J.matrix 0 N *ᵥ site N (s+1) = Real.sqrt (J.aSq (s+1)) • site N s + J.b (s+1) •
site N (s+1) + Real.sqrt (J.aSq (s+2)) • site N (s+2)`.

Use: `chebyshev1.JacobiData.leading_aeval_site` rewrites with this identity to establish
exact identity `aeval (J.matrix 0 N) (J.leading s) *ᵥ site N 0 = J.linkProduct s • site N s`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.leading_orthogonality`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem matrix_site_succ (N s : ℕ) (hs : s+1 < N) :
    J.matrix 0 N *ᵥ site N (s+1) = Real.sqrt (J.aSq (s+1)) • site N s +
      J.b (s+1) • site N (s+1) + Real.sqrt (J.aSq (s+2)) • site N (s+2) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  conv_lhs => rw [site_eq_single N (s+1) hs, Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply, J.matrix_apply]
  simp only [Nat.zero_add, Fin.ext_iff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, site]
  split_ifs <;> simp only [mul_one, mul_zero, add_zero, zero_add]
  all_goals first | omega | congr 2

/--
The leading continuants reproduce the coordinate basis under the Jacobi functional calculus.

Exact identity `aeval (J.matrix 0 N) (J.leading s) *ᵥ site N 0 = J.linkProduct s • site N s`.

Use: `chebyshev1.JacobiData.leading_orthogonality` uses this identity to establish the
precise assertion is `let B`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.leading_orthogonality`.

Proof: Induct on `s`; the recursive step uses the previous-stage assertion. Prove equality of
functions by evaluating both sides at an arbitrary argument.
-/
theorem leading_aeval_site (N s : ℕ) (hN : 0 < N) (hs : s < N)
    (hsq : ∀ t, 0 ≤ J.aSq t) :
    aeval (J.matrix 0 N) (J.leading s) *ᵥ site N 0 = J.linkProduct s • site N s := by
  -- Induct on `s`; the recursive step uses the previous-stage assertion.
  induction s using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [leading_one, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, J.matrix_site_zero N hN]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, linkProduct_succ,
      linkProduct_zero, one_mul]
    ring
  | more s h0 h1 =>
    rw [J.leading_add_two]
    simp only [map_sub, map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h1 (by omega), h0 (by omega), Matrix.mulVec_smul, J.matrix_site_succ N s (by omega)]
    have hp : J.linkProduct (s+1)*Real.sqrt (J.aSq (s+1)) = J.linkProduct s*J.aSq (s+1) := by
      rw [linkProduct_succ, mul_assoc, ← pow_two, Real.sq_sqrt (hsq _)]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [linkProduct_succ (J := J) (s+1)]
    linear_combination hp*site N s i


/--
Discrete orthogonality of the monic leading polynomials for the first spectral measure.

The precise assertion is `let B`.

Use: `chebyshev1.SineJacobi.leading_orthogonality` uses this assertion to establish exact
identity `∑ j : Fin N, sineWeight N j*((data N).leading s).eval (node N j)* ((data N).leading
t).eval (node N j) = if s = t then ((data N).linkProduct s)^2 else 0`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.leading_orthogonality`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem leading_orthogonality (N s t : ℕ) (hN : 0 < N) (hs : s < N) (ht : t < N)
    (hsq : ∀ u, 0 ≤ J.aSq u) :
    let B := SpectralBasis.ofHermitian (J.matrix 0 N) (J.matrix_isHermitian 0 N)
    ∑ j : Fin N, B.weight (⟨0,hN⟩ : Fin N) j *
      (J.leading s).eval (B.eigenvalues j)*(J.leading t).eval (B.eigenvalues j) =
        if s = t then (J.linkProduct s)^2 else 0 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let M := J.matrix 0 N
  let B := SpectralBasis.ofHermitian M (J.matrix_isHermitian 0 N)
  let first : Fin N := ⟨0,hN⟩
  have hcol (u : ℕ) (hu : u < N) (i : Fin N) :
      (aeval M (J.leading u)) i first = J.linkProduct u*site N u i := by
    have hh := J.leading_aeval_site N u hN hu hsq
    rw [site_eq_single N 0 hN, Matrix.mulVec_single_one] at hh
    exact congrArg (fun v => v i) hh
  have hm := SpectralBasis.moment (J.leading s*J.leading t) (J.matrix_isHermitian 0 N) first
  have hsite : (∑ i : Fin N, site N s i*site N t i) = if s = t then 1 else 0 := by
    rw [site_eq_single N s hs]
    change (Pi.single (⟨s,hs⟩ : Fin N) 1) ⬝ᵥ site N t = _
    rw [single_dotProduct]
    simp [site]
  change (∑ j : Fin N, B.weight first j*(J.leading s).eval (B.eigenvalues j)*
    (J.leading t).eval (B.eigenvalues j)) = if s = t then (J.linkProduct s)^2 else 0
  calc
    _ = ∑ j : Fin N, B.weight first j * ((J.leading s*J.leading t).eval (B.eigenvalues j)) := by
      simp only [eval_mul, mul_assoc]
    _ = (aeval M (J.leading s*J.leading t)) first first := hm.symm
    _ = ∑ i : Fin N, (aeval M (J.leading s)) i first*(aeval M (J.leading t)) i first := by
      rw [map_mul, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i first)
        (SpectralBasis.aeval_transpose (J.leading s) (J.matrix_isHermitian 0 N))
      simp only [Matrix.transpose_apply] at he
      rw [he]
    _ = J.linkProduct s*J.linkProduct t*(∑ i : Fin N, site N s i*site N t i) := by
      simp_rw [hcol s hs, hcol t ht]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hsite]; split_ifs with he; subst t; ring; ring

end
end chebyshev1.JacobiData
