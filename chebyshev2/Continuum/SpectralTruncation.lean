import chebyshev2.Continuum.SpectralFunctional
import chebyshev2.Continuum.SpectralPerturbation

/-!
Article: chebyshev2, Proposition 3.
Spectral Truncation.
Use: `chebyshev2.Continuum.logDeterminant_traceBound` feeds
`chebyshev2.Continuum.rankOne_logDeterminant` (The Fredholm matrix determinant lemma for the
already defined spectral logarithm of the actual compact operator).
Proof chain: `chebyshev2.Comparison.Profile.signed_determinant_comparison` — chebyshev2,
Theorem 3.4; Signed determinant and square-trace comparisons.
Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory. The needed
form is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open Real Filter
open scoped InnerProductSpace BigOperators Classical Topology
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {T : E →L[ℝ] E} (D : PositiveSpectralData T)

/--
Defines `spectralTruncation` of type `E →L[ℝ] E` by `∑ i ∈ F, D.eig i •
InnerProductSpace.rankOne ℝ (D.basis i) (D.basis i)`.

Use: `chebyshev2.Continuum.spectralTruncation_basis` rewrites with this definition to
establish exact identity `spectralTruncation D F (D.basis j) = (if j ∈ F then D.eig j else 0) •
D.basis j`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.
-/
def spectralTruncation (F : Finset D.Index) : E →L[ℝ] E :=
  ∑ i ∈ F, D.eig i • InnerProductSpace.rankOne ℝ (D.basis i) (D.basis i)

omit [CompleteSpace E] in
/--
Exact identity `spectralTruncation D F (D.basis j) = (if j ∈ F then D.eig j else 0) • D.basis
j`.

Use: `chebyshev2.Continuum.spectralTruncation_error` rewrites with this identity to
establish membership in the specified domain/enclosure: `TraceBound (T-spectralTruncation D F)
((∑' i, D.eig i)-∑ i ∈ F, D.eig i)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Separate `i=j` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem spectralTruncation_basis (F : Finset D.Index) (j : D.Index) :
    spectralTruncation D F (D.basis j) = (if j ∈ F then D.eig j else 0) • D.basis j := by
  -- Separate `i=j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  simp only [spectralTruncation,sum_apply,smul_apply,InnerProductSpace.rankOne_apply]
  have he (i : D.Index) : D.eig i • (inner ℝ (D.basis i) (D.basis j) • D.basis i) =
      if i=j then D.eig j • D.basis j else 0 := by
    by_cases hij : i=j
    · subst i
      simp [D.basis.orthonormal.norm_eq_one]
    · simp [D.basis.orthonormal.inner_eq_zero hij,hij]
  simp only [he]
  by_cases hj : j ∈ F <;> simp [hj]

/--
Constructs `truncationSpectralData` of type `PositiveSpectralData (spectralTruncation D F)` by
the displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `chebyshev2.Continuum.spectralTruncation_logDeterminant` uses this definition to
establish exact identity `logDeterminant (truncationSpectralData D F).eigenvalue s = ∑ i ∈ F,
log (1+s/2*D.eig i)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.
-/
def truncationSpectralData (F : Finset D.Index) : PositiveSpectralData (spectralTruncation D F) where
  Index := D.Index
  basis := D.basis
  eig i := if i ∈ F then D.eig i else 0
  equation := spectralTruncation_basis D F
  nonneg i := by split_ifs <;> first | exact D.nonneg i | exact le_rfl
  summable := summable_of_ne_finset_zero (s := F) (by intro i hi; simp [hi])

omit [CompleteSpace E] in
/--
Compactness of the displayed operator: `IsCompactOperator (spectralTruncation D F)`.

Use: `chebyshev2.Continuum.rankOne_logDeterminant` uses this assertion to establish exact
identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log (1+s/2*u*inner ℝ
v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `chebyshev2.Continuum.rankOne_isCompact` with the
arguments shown in the proof.
-/
theorem spectralTruncation_compact (F : Finset D.Index) : IsCompactOperator (spectralTruncation D F) :=
  (compactOperator (RingHom.id ℝ) E E).sum_mem
    (fun i _ => (rankOne_isCompact (D.basis i) (D.basis i)).smul (D.eig i))

omit [CompleteSpace E] in
/--
The precise assertion is `(spectralTruncation D F).IsPositive`.

Use: `chebyshev2.Continuum.rankOne_logDeterminant` uses this assertion to establish exact
identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log (1+s/2*u*inner ℝ
v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem spectralTruncation_positive (F : Finset D.Index) : (spectralTruncation D F).IsPositive := by
  apply ContinuousLinearMap.isPositive_sum
  intro i _
  exact (InnerProductSpace.isPositive_rankOne_self (D.basis i)).smul_of_nonneg (D.nonneg i)

/--
Membership in the specified domain/enclosure: `TraceBound (T-spectralTruncation D F) ((∑' i,
D.eig i)-∑ i ∈ F, D.eig i)`.

Use: `chebyshev2.Continuum.rankOne_logDeterminant` uses this assertion to establish exact
identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log (1+s/2*u*inner ℝ
v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem spectralTruncation_error (F : Finset D.Index) :
    TraceBound (T-spectralTruncation D F) ((∑' i, D.eig i)-∑ i ∈ F, D.eig i) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let c : D.Index → ℝ := fun i => if i ∈ F then D.eig i else 0
  -- Prove the summability hc needed for the later infinite-sum manipulations.
  have hc : Summable c := summable_of_ne_finset_zero (s := F) (by intro i hi; simp [c,hi])
  have he (i : D.Index) : (T-spectralTruncation D F) (D.basis i) =
      (D.eig i-c i) • D.basis i := by
    rw [sub_apply,D.equation,spectralTruncation_basis,sub_smul]
  have hn (i : D.Index) : 0 ≤ D.eig i-c i := by
    dsimp [c]
    split_ifs
    · simp
    · simpa only [sub_zero] using D.nonneg i
  -- Prove the summability hs needed for the later infinite-sum manipulations.
  have hs : Summable (fun i => |D.eig i-c i|) := by
    simpa only [abs_of_nonneg (hn _)] using D.summable.sub hc
  have h := eigenbasis_traceBound D.basis _ he hs
  have hsum : (∑' i, c i) = ∑ i ∈ F, D.eig i := by
    exact (tsum_eq_sum (s := F) (by intro i hi; simp [c,hi])).trans
      (Finset.sum_congr rfl (fun i hi => by simp [c,hi]))
  simpa only [abs_of_nonneg (hn _), D.summable.tsum_sub hc, hsum] using h

/--
Exact identity `logDeterminant (truncationSpectralData D F).eigenvalue s = ∑ i ∈ F, log
(1+s/2*D.eig i)`.

Use: `chebyshev2.Continuum.rankOne_logDeterminant` rewrites with this identity to establish
exact identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log
(1+s/2*u*inner ℝ v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity))
v))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem spectralTruncation_logDeterminant (F : Finset D.Index) {s : ℝ} (hs : 0 ≤ s) :
    logDeterminant (truncationSpectralData D F).eigenvalue s =
      ∑ i ∈ F, log (1+s/2*D.eig i) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [PositiveSpectralData.logDeterminant_eq _ hs]
  change (∑' i, log (1+s/2*(if i ∈ F then D.eig i else 0))) = _
  have he (i : D.Index) : log (1+s/2*(if i ∈ F then D.eig i else 0)) =
      if i ∈ F then log (1+s/2*D.eig i) else 0 := by split_ifs <;> simp
  simp only [he]
  exact (tsum_eq_sum (s := F) (by intro i hi; simp [hi])).trans
    (Finset.sum_congr rfl (fun i hi => by simp [hi]))

/--
The stated quantitative bound `|logDeterminant DA.eigenvalue s-logDeterminant DB.eigenvalue s|
≤ s/2*C`.

Use: `chebyshev2.Continuum.rankOne_logDeterminant` uses this bound to establish exact
identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log (1+s/2*u*inner ℝ
v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `chebyshev2.Continuum.logDeterminant_distance`,
`chebyshev2.Continuum.PositiveSpectralData.eigenvalue_summable`,
`chebyshev2.Continuum.PositiveSpectralData.eigenvalue_nonneg` with the arguments shown in
the proof.
-/
theorem logDeterminant_traceBound {A B : E →L[ℝ] E}
    (hcA : IsCompactOperator A) (hcB : IsCompactOperator B) (hpA : A.IsPositive) (hpB : B.IsPositive)
    (DA : PositiveSpectralData A) (DB : PositiveSpectralData B) {C s : ℝ}
    (hC : TraceBound (A-B) C) (hs : 0 ≤ s) :
    |logDeterminant DA.eigenvalue s-logDeterminant DB.eigenvalue s| ≤ s/2*C :=
  (logDeterminant_distance DA.eigenvalue_summable DB.eigenvalue_summable
    DA.eigenvalue_nonneg DB.eigenvalue_nonneg hs).trans
      (mul_le_mul_of_nonneg_left (eigenvalue_l1_le_traceBound hcA hcB hpA hpB DA DB hC)
        (by positivity))

end
end chebyshev2.Continuum
