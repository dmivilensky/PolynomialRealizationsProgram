import «2610.05164v2».Continuum.DiagonalOperator
import «2610.05164v2».Continuum.SpectralTrace

/-!
Article: 2610.05164v2, Theorem 2.4.
The nuclear-norm statement (39), including the infinite-norm case.
Result: `«2610.05164v2».Continuum.eigenvalue_l1_le_nuclearNorm` supplies the stated article
conclusion.
Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory. The needed
form is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Real
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Lemma 4(iv), in the finite-frame formulation of the nuclear bound. Positive and negative parts
are constructed from an actual compact eigenbasis.

The stated quantitative bound `(∑' n, |DA.eigenvalue n - DB.eigenvalue n|) ≤ C`.

Use: `«2610.05164v2».Continuum.eigenvalue_l1_le_nuclearNorm` uses this bound to establish the
stated quantitative bound `ENNReal.ofReal (∑' n, |DA.eigenvalue n-DB.eigenvalue n|) ≤
nuclearNorm (A-B)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Diagonalize A-B and construct its positive and negative parts P and Q from the same
compact eigenbasis. The common positive upper operator U=B+P=A+Q dominates both A and B, so
eigenvalue monotonicity bounds each absolute eigenvalue difference by the two gaps to U.
Summing these gaps and using the two trace identities leaves exactly the sum of absolute
eigenvalues of A-B, which the finite-frame trace bound controls.
-/
theorem eigenvalue_l1_le_traceBound {A B : E →L[ℝ] E}
    (hcA : IsCompactOperator A) (hcB : IsCompactOperator B) (hpA : A.IsPositive) (hpB : B.IsPositive)
    (DA : PositiveSpectralData A) (DB : PositiveSpectralData B) {C : ℝ} (hD : TraceBound (A-B) C) :
    (∑' n, |DA.eigenvalue n - DB.eigenvalue n|) ≤ C := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  obtain ⟨ι,b,eig,he⟩ := exists_compact_eigenbasis (A-B) (hcA.sub hcB) (hpA.isSymmetric.sub hpB.isSymmetric)
  obtain ⟨hsabs,hsbound⟩ := eigenbasis_abs_summable b he hD
  -- Separate positive and negative eigenvalues in one common eigenbasis; this constructs the
  -- operator positive/negative parts rather than postulating them.
  let p : ι → ℝ := fun i => max (eig i) 0
  let q : ι → ℝ := fun i => max (-eig i) 0
  have hp (i : ι) : 0 ≤ p i := le_max_right _ _
  have hq (i : ι) : 0 ≤ q i := le_max_right _ _
  -- Prove the summability hsp needed for the later infinite-sum manipulations.
  have hsp : Summable p := hsabs.of_nonneg_of_le hp (fun i => max_le (le_abs_self _) (abs_nonneg _))
  -- Prove the summability hsq needed for the later infinite-sum manipulations.
  have hsq : Summable q := hsabs.of_nonneg_of_le hq (fun i => max_le (neg_le_abs _) (abs_nonneg _))
  -- Prove the summability hspabs needed for the later infinite-sum manipulations.
  have hspabs : Summable (fun i => |p i|) := by simpa only [abs_of_nonneg (hp _)] using hsp
  -- Prove the summability hsqabs needed for the later infinite-sum manipulations.
  have hsqabs : Summable (fun i => |q i|) := by simpa only [abs_of_nonneg (hq _)] using hsq
  let P := diagonalOperator b p
  let Q := diagonalOperator b q
  have hPQ (i : ι) : p i-q i = eig i := by
    dsimp [p,q]
    rcases le_total 0 (eig i) with h | h
    · simp [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
    · simp [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]
  have hsum (i : ι) : p i+q i = |eig i| := by
    dsimp [p,q]
    rcases le_total 0 (eig i) with h | h
    · simp [max_eq_left h,max_eq_right (neg_nonpos.mpr h),abs_of_nonneg h]
    · simp [max_eq_right h,max_eq_left (neg_nonneg.mpr h),abs_of_nonpos h]
  -- Summability of the rank-one expansions identifies A-B with P-Q in operator norm.
  have hd : A-B = P-Q := by
    have ht := eigenbasis_operator_series b (A-B) he hsabs
    have ht' := (diagonalOperator_summable b hspabs).hasSum.sub (diagonalOperator_summable b hsqabs).hasSum
    have hf (i : ι) : p i • InnerProductSpace.rankOne ℝ (b i) (b i) -
        q i • InnerProductSpace.rankOne ℝ (b i) (b i) = eig i • InnerProductSpace.rankOne ℝ (b i) (b i) := by
      rw [← sub_smul,hPQ]
    have ht'' : HasSum (fun i => eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) (P-Q) := by
      simp only [hf] at ht'
      exact ht'
    exact ht.unique ht''
  have hPpos := diagonalOperator_positive b hspabs hp
  have hQpos := diagonalOperator_positive b hsqabs hq
  have hPcompact := diagonalOperator_isCompact b hspabs
  let DP : PositiveSpectralData P := ⟨ι,b,p,diagonalOperator_basis b hspabs,hp,hsp⟩
  let DQ : PositiveSpectralData Q := ⟨ι,b,q,diagonalOperator_basis b hsqabs,hq,hsq⟩
  -- Use a common upper operator so the min-max eigenvalue comparison applies to both spectra
  -- with the same index ordering.
  let U := B+P
  have hUeq : U = A+Q := by
    change B+P = A+Q
    calc
      B+P = B+(P-Q)+Q := by abel
      _ = B+(A-B)+Q := by rw [← hd]
      _ = A+Q := by abel
  have hUpos : U.IsPositive := hpB.add hPpos
  have hUcompact : IsCompactOperator U := hcB.add hPcompact
  have hBbound := eigenbasis_traceBound DB.basis B DB.equation
    (by simpa only [abs_of_nonneg (DB.nonneg _)] using DB.summable)
  have hPbound := diagonalOperator_traceBound b hspabs
  have hUtrace : IsTraceClass U := (hBbound.add hPbound).isTraceClass
  let DU := positiveSpectralData U hUcompact hUpos hUtrace
  have hAU (n : ℕ) : DA.eigenvalue n ≤ DU.eigenvalue n := by
    apply eigenvalue_mono DA DU
    intro x
    rw [hUeq]
    change inner ℝ x (A x) ≤ inner ℝ x (A x + Q x)
    rw [inner_add_right]
    have h := hQpos.re_inner_nonneg_right x
    change 0 ≤ inner ℝ x (Q x) at h
    linarith
  have hBU (n : ℕ) : DB.eigenvalue n ≤ DU.eigenvalue n := by
    apply eigenvalue_mono DB DU
    intro x
    change inner ℝ x (B x) ≤ inner ℝ x (B x + P x)
    rw [inner_add_right]
    have h := hPpos.re_inner_nonneg_right x
    change 0 ≤ inner ℝ x (P x) at h
    linarith
  -- Compute tr(U) in the B+P decomposition. The analogous A+Q identity will cancel the unknown
  -- common upper trace.
  have hUB : (∑' n, DU.eigenvalue n) = (∑' n, DB.eigenvalue n) + ∑' i, p i := by
    have h := (DB.hasSum_trace_eigenvalues b).add (DP.hasSum_trace b)
    have hh : HasSum (fun i => inner ℝ (b i) (U (b i)))
        ((∑' n, DB.eigenvalue n) + ∑' i, p i) := by
      simpa only [U,add_apply,inner_add_right,DP] using h
    exact (DU.hasSum_trace_eigenvalues b).unique hh
  have hUA : (∑' n, DU.eigenvalue n) = (∑' n, DA.eigenvalue n) + ∑' i, q i := by
    have h := (DA.hasSum_trace_eigenvalues b).add (DQ.hasSum_trace b)
    have hh : HasSum (fun i => inner ℝ (b i) (U (b i)))
        ((∑' n, DA.eigenvalue n) + ∑' i, q i) := by
      rw [hUeq]
      simpa only [add_apply,inner_add_right,DQ] using h
    exact (DU.hasSum_trace_eigenvalues b).unique hh
  -- Prove the summability habs needed for the later infinite-sum manipulations.
  have habs : Summable (fun n => |DA.eigenvalue n - DB.eigenvalue n|) :=
    summable_abs_iff.mpr (DA.eigenvalue_summable.sub DB.eigenvalue_summable)
  have hright := (DU.eigenvalue_summable.sub DA.eigenvalue_summable).add
    (DU.eigenvalue_summable.sub DB.eigenvalue_summable)
  -- Bound each absolute spectral difference by its two nonnegative gaps to U.
  have hpoint (n : ℕ) : |DA.eigenvalue n - DB.eigenvalue n| ≤
      (DU.eigenvalue n-DA.eigenvalue n)+(DU.eigenvalue n-DB.eigenvalue n) := by
    apply abs_le.mpr
    constructor <;> linarith [hAU n,hBU n]
  have hle := habs.tsum_le_tsum hpoint hright
  -- Summing the gaps cancels tr(A), tr(B) and tr(U), leaving tr(P)+tr(Q), the absolute
  -- spectral sum of A-B.
  have hr : (∑' n, ((DU.eigenvalue n-DA.eigenvalue n)+(DU.eigenvalue n-DB.eigenvalue n))) =
      ∑' i, |eig i| := by
    rw [Summable.tsum_add, Summable.tsum_sub, Summable.tsum_sub]
    · have hh : (∑' i, |eig i|) = (∑' i, p i)+(∑' i, q i) := by
        rw [← hsp.tsum_add hsq]
        exact tsum_congr (fun i => (hsum i).symm)
      rw [hh]
      linarith
    all_goals first | exact DU.eigenvalue_summable | exact DA.eigenvalue_summable |
      exact DB.eigenvalue_summable | exact DU.eigenvalue_summable.sub DA.eigenvalue_summable |
      exact DU.eigenvalue_summable.sub DB.eigenvalue_summable
  exact (hle.trans_eq hr).trans hsbound


/--
The nuclear-norm statement (39), including the infinite-norm case.

The stated quantitative bound `ENNReal.ofReal (∑' n, |DA.eigenvalue n-DB.eigenvalue n|) ≤
nuclearNorm (A-B)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 2.4.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Separate `nuclearNorm (A-B) = ⊤` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem eigenvalue_l1_le_nuclearNorm {A B : E →L[ℝ] E}
    (hcA : IsCompactOperator A) (hcB : IsCompactOperator B) (hpA : A.IsPositive) (hpB : B.IsPositive)
    (DA : PositiveSpectralData A) (DB : PositiveSpectralData B) :
    ENNReal.ofReal (∑' n, |DA.eigenvalue n-DB.eigenvalue n|) ≤ nuclearNorm (A-B) := by
  -- Separate `nuclearNorm (A-B) = ⊤` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  by_cases h : nuclearNorm (A-B) = ⊤
  · rw [h]
    exact le_top
  · have hb : TraceBound (A-B) (nuclearNorm (A-B)).toReal := by
      apply traceBound_of_nuclearNorm_le ENNReal.toReal_nonneg
      rw [ENNReal.ofReal_toReal h]
    have hle := eigenvalue_l1_le_traceBound hcA hcB hpA hpB DA DB hb
    rw [← ENNReal.ofReal_toReal h]
    exact ENNReal.ofReal_le_ofReal hle

end
end «2610.05164v2».Continuum
