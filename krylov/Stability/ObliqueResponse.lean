import krylov.Stability.UniformFlags
import Mathlib.Algebra.BigOperators.Intervals

/-!
Article: main_krylov, thm:A, exact genuine oblique-flag response reconstruction.
Use: reconstruct a real residual from any true nonsingular direction basis
and its actual chronological defect equations, without requiring nonzero line steps.
Source: exact transported finite flags, actual inverse-transpose coordinates
and the proved standard triangular finite-sum interchange.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true Euclidean pairing with a genuine matrix column is its actual transpose coordinate.
Use: transfer real direction pairings to genuine finite reconstruction coordinates.
Article: main_krylov, thm:A.
Proof: expand the actual real Euclidean inner product and matrix-vector contraction. -/
theorem column_inner_eq_coordinate (T : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (WithLp.toLp 2 (fun a => T a i)) v=(Tᵀ *ᵥ WithLp.ofLp v) i := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,Matrix.mulVec,Matrix.transpose_apply,dotProduct_comm]

/-- Every genuine transported old flag selects exactly the actual prefix columns of its true basis.
Use: oblique response coordinates require only actual basis nonsingularity, not orthogonality.
Article: main_krylov, thm:A.
Proof: cancel the genuine basis inverse in the actual transported-flag product. -/
theorem transportedFlag_column_mul (T : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit T.det) (l : ℕ) :
    transportedFlag T l*T=T*prefixProjection n l := by
  rw [transportedFlag,Matrix.mul_assoc,Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hu,Matrix.mul_one]

/-- Pairing a true basis column with the actual transposed oblique flag selects precisely the old-column indices.
Use: exact real staircase reconstruction remains valid with a zero last line displacement.
Article: main_krylov, thm:A.
Proof: transpose the genuine flag-column identity and apply the true
coordinate formula; the actual prefix diagonal selects the stated indices. -/
theorem column_inner_transportedFlag (T : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit T.det)
    (l : ℕ) (i : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (WithLp.toLp 2 (fun a => T a i))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (transportedFlag T l)ᵀ v)=
      if i.val≤l then inner ℝ (WithLp.toLp 2 (fun a => T a i)) v else 0 := by
  have he : Tᵀ*(transportedFlag T l)ᵀ=prefixProjection n l*Tᵀ := by
    rw [← Matrix.transpose_mul,transportedFlag_column_mul T hu l,Matrix.transpose_mul,
      (prefixProjection_isSymm n l).eq]
  rw [column_inner_eq_coordinate,column_inner_eq_coordinate]
  change (Tᵀ *ᵥ ((transportedFlag T l)ᵀ *ᵥ WithLp.ofLp v)) i=_
  rw [Matrix.mulVec_mulVec,he,← Matrix.mulVec_mulVec]
  simp only [prefixProjection,Matrix.mulVec_diagonal]
  split_ifs <;> simp

/-- Actual pairings with the columns of a genuinely nonsingular real basis determine the physical vector uniquely.
Use: reconstruct the actual terminal residual from a direction staircase rather than assume its response formula.
Article: main_krylov, thm:A.
Proof: the real pairings give equality after the true transpose basis
action; cancel its actual inverse and use the genuine Euclidean coordinate equivalence. -/
theorem column_inner_ext (T : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit T.det)
    (v w : EuclideanSpace ℝ (Fin n))
    (he : ∀ i, inner ℝ (WithLp.toLp 2 (fun a => T a i)) v=inner ℝ (WithLp.toLp 2 (fun a => T a i)) w) : v=w := by
  have hc : Tᵀ *ᵥ WithLp.ofLp v=Tᵀ *ᵥ WithLp.ofLp w := by
    funext i
    simpa only [column_inner_eq_coordinate] using he i
  have hh := congrArg (fun u => Tᵀ⁻¹ *ᵥ u) hc
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (by simpa only [Matrix.det_transpose] using hu),Matrix.one_mulVec,Matrix.one_mulVec] at hh
  exact WithLp.ofLp_injective 2 hh

/-- The genuine transposed-oblique-flag response of the supplied actual basis and true remaining step tails.
Use: reconstructs the true terminal residual before replacing actual directions or steps by the CG reference.
Article: main_krylov, thm:A, ΣΠ_lᵀE_lρ_l. -/
def obliqueResponse (T : Matrix (Fin n) (Fin n) ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (s : ℕ → EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∑ l∈range n, Matrix.toEuclideanCLM (𝕜 := ℝ) (transportedFlag T l)ᵀ
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (∑ j∈Ico (l+1) n, s j))

/-- The genuine oblique flag/tail sum has exactly the real chronological staircase coordinates in its actual basis.
Use: identify the true residual response before taking a uniform remainder or any derivative.
Article: main_krylov, thm:A.
Proof: true transposed oblique flags select the actual old indices;
expand each real remaining-step tail and interchange the genuine triangular
finite sums. The empty newest tail is handled exactly. -/
theorem obliqueResponse_coordinates (T : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit T.det)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (s : ℕ → EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    inner ℝ (WithLp.toLp 2 (fun a => T a i)) (obliqueResponse T E s)=
      ∑ j∈Ico (i.val+1) n, inner ℝ (WithLp.toLp 2 (fun a => T a i))
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ l∈Ico i.val j, E l) (s j)) := by
  -- The exact old-index selection is applied before exchanging the true chronological sums.
  unfold obliqueResponse
  rw [inner_sum]
  simp_rw [column_inner_transportedFlag T hu]
  rw [← sum_filter]
  have hset : (range n).filter (fun l => i.val≤l)=Ico i.val n := by
    ext l
    simp only [mem_filter,mem_range,mem_Ico]
    tauto
  rw [hset]
  calc
    _ = ∑ l∈Ico i.val n, ∑ j∈Ico (l+1) n, inner ℝ (WithLp.toLp 2 (fun a => T a i))
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (s j)) := by
      apply sum_congr rfl
      intro l _
      rw [map_sum,inner_sum]
    _ = ∑ j∈Ico i.val n, ∑ l∈Ico i.val j, inner ℝ (WithLp.toLp 2 (fun a => T a i))
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (s j)) := sum_Ico_Ico_comm' i.val n _
    _ = _ := by
      rw [sum_eq_sum_Ico_succ_bot i.isLt]
      simp only [Ico_self,sum_empty,zero_add]
      apply sum_congr rfl
      intro j _
      rw [map_sum,_root_.sum_apply,inner_sum]

/-- Any actual vector with the genuine chronological staircase pairings equals the true oblique flag/tail response.
Use: the actual FC direction staircase will supply these real coordinates, including a zero last line displacement.
Article: main_krylov, thm:A.
Proof: the proved true response coordinate identity and genuine nonsingular
column-pairing uniqueness identify the actual vector. -/
theorem obliqueResponse_unique (T : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit T.det)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (s : ℕ → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n))
    (hrows : ∀ i : Fin n, inner ℝ (WithLp.toLp 2 (fun a => T a i)) g=
      ∑ j∈Ico (i.val+1) n, inner ℝ (WithLp.toLp 2 (fun a => T a i))
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ l∈Ico i.val j, E l) (s j))) :
    g=obliqueResponse T E s := by
  apply column_inner_ext T hu
  intro i
  rw [hrows i,obliqueResponse_coordinates T hu]

end
end krylov.Stability
