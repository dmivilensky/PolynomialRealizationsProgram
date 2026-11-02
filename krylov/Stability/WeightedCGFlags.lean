import krylov.Stability.UniformFlagBounds
import krylov.Stability.ReferenceWeights
import krylov.LinearAlgebra.RankOneNorm

/-!
Article: main_krylov, eq:weighted-flag-bound, actual CG weighted oblique flags.
Use: discharge every individual weighted column comparison from the genuine
CG energy profile, retaining dimension and conditioning constants only.
Source: actual CG nonstagnation ratios, proved weighted rank-one changes,
true finite-column Gram matrices and the exact uniform oblique-flag bound.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The true finite column Gram product is the genuine physical Euclidean inner-product Gram matrix.
Use: actual normalized-vector angle bounds control the actual matrix Gram norm.
Article: main_krylov, eq:weighted-flags.
Proof: each true Gram entry is its finite real row contraction, exactly the Euclidean inner product of its actual columns. -/
theorem transpose_mul_columnGram (T : Matrix (Fin n) (Fin p) ℝ) :
    Tᵀ*T=crossGram (fun j => WithLp.toLp 2 (fun i => T i j))
      (fun j => WithLp.toLp 2 (fun i => T i j)) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,crossGram,EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The genuine spectral norm of an actual real rank-one matrix difference equals its actual Hilbert-space operator norm.
Use: the proved weighted CG rank-one estimate transfers to the true matrix flag norm.
Article: main_krylov, eq:weighted-flag-bound.
Proof: the genuine Euclidean matrix/operator identification preserves subtraction and the two actual rank-one actions. -/
theorem rankOne_matrix_difference_norm (u v : EuclideanSpace ℝ (Fin n)) :
    ‖vecMulVec (WithLp.ofLp u) (WithLp.ofLp u)-vecMulVec (WithLp.ofLp v) (WithLp.ofLp v)‖=
      ‖InnerProductSpace.rankOne ℝ u u-InnerProductSpace.rankOne ℝ v v‖ := by
  rw [Matrix.cstar_norm_def,map_sub,toEuclideanCLM_rankOne,toEuclideanCLM_rankOne]

/-- True CG later errors weight actual normalized oblique-flag changes with constants independent of every individual reference step length.
Use: supplies the printed uniform weighted-flag mechanism from actual CG geometry, rather than an assumed reference ratio or a smallest-energy bound.
Article: main_krylov, eq:weighted-flag-bound, actual weighted flag comparison.
Proof: actual normalized-column angles control the real Gram matrix and its
genuine inverse. For each old column, true CG nonstagnation and its real
step error give the proved weighted rank-one bound. Apply the actual weighted
oblique-flag theorem and then the true spectral Gram deviation. -/
theorem cg_weighted_oblique_flag (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {mu upper : ℝ} (hm : 0<mu) (hmu : mu≤upper)
    (hspec : ∀ i, mu≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤upper)
    (x : Fin n → EuclideanSpace ℝ (Fin n)) (hx : ∀ i, x i≠0) (l : ℕ)
    (hl : l<referenceAtomCount base hb g) {η ε : ℝ} (hη : 0≤η) (hε : 0≤ε)
    (hangle : ∀ i j, i≠j → |inner ℝ (NormedSpace.normalize (x i)) (NormedSpace.normalize (x j))|≤η)
    (hsmall : (n : ℝ)*η≤(1/2 : ℝ))
    (hstep : ∀ j : Fin n, j.val≤l → ‖x j-canonicalCGStep base g j.val‖≤ε) :
    let T : Matrix (Fin n) (Fin n) ℝ := fun i j => (NormedSpace.normalize (x j)) i
    let Q : Matrix (Fin n) (Fin n) ℝ := fun i j => (canonicalCGUnitStep base g j.val) i
    ‖cgCanonicalError base g (l+1)‖*‖transportedFlag T l-Q*prefixProjection n l*Qᵀ‖≤
      3*‖cgCanonicalError base g (l+1)‖*(n : ℝ)*η+4*(n : ℝ)*Real.sqrt (upper/mu)*ε := by
  -- Each column keeps the genuine later CG error as its own weight before the finite sum is bounded.
  let T : Matrix (Fin n) (Fin n) ℝ := fun i j => (NormedSpace.normalize (x j)) i
  let Q : Matrix (Fin n) (Fin n) ℝ := fun i j => (canonicalCGUnitStep base g j.val) i
  have hG : ‖Tᵀ*T-1‖≤(n : ℝ)*η := by
    rw [transpose_mul_columnGram]
    exact unitGram_deviation (fun j => NormedSpace.normalize (x j))
      (fun j => NormedSpace.norm_normalize (hx j)) hη hangle
  have hcols : ∀ j∈Finset.univ.filter (fun j : Fin n => j.val≤l),
      ‖cgCanonicalError base g (l+1)‖*
      ‖vecMulVec (fun i => T i j) (fun i => T i j)-vecMulVec (fun i => Q i j) (fun i => Q i j)‖≤
        4*Real.sqrt (upper/mu)*ε := by
    intro j hj
    have hjl := (Finset.mem_filter.mp hj).2
    have hw := cg_weighted_rankOne base hb g hm hmu hspec (hjl.trans_lt hl)
      (show j.val≤l+1 by omega) (x j) (hx j) ε (hstep j hjl)
    change ‖cgCanonicalError base g (l+1)‖*
      ‖vecMulVec (WithLp.ofLp (NormedSpace.normalize (x j))) (WithLp.ofLp (NormedSpace.normalize (x j)))-
        vecMulVec (WithLp.ofLp (canonicalCGUnitStep base g j.val)) (WithLp.ofLp (canonicalCGUnitStep base g j.val))‖≤_
    rw [rankOne_matrix_difference_norm]
    exact hw
  have ht := transportedFlag_weighted_bound T Q l (hG.trans hsmall) (norm_nonneg _)
    (by positivity : 0≤4*Real.sqrt (upper/mu)*ε) hcols
  exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left hG (mul_nonneg (by norm_num : (0 : ℝ)≤3) (norm_nonneg (cgCanonicalError base g (l+1))))])

end
end krylov.Stability
