import jacobi.Comparison.CholeskyGramResidual
import jacobi.Comparison.PrincipalCoercivity
import jacobi.Comparison.CholeskySystem
import jacobi.Comparison.GramEntryBounds

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
The original actual Cholesky coefficients have their full uniform
two-edge continuum limit. The true GL quadrature, alternating cross-edge
cancellation, original Gram approximation and genuine growing-section
inverse bound are all proved, with no residual or coercivity premise.
Use: choleskyError_equation and cholesky_uniform_limit identify the genuine target/support transformation in the finite eigenvector limit.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Finite
open scoped Topology

/-- The literal matrix-size-scaled error of the original actual Cholesky
coefficient relative to the actual two source transformation kernels.
Use: choleskyError_equation and cholesky_uniform_limit identify the
genuine target/support transformation in the finite eigenvector limit.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def choleskyError (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ)
    (i:Fin (n+1)) (j:Fin i.val) : ℝ :=
  ((n:ℝ)+1)*rowCoefficient a b ha hb n i j-
    twoEdgeTransformation a b ha hb n i (Gram.before i j)

/-- The actual original Cholesky error row solves exactly the true
preceding Gram equation with the original complete GL residual.
Use: cholesky_uniform_limit applies the genuine uniform inverse bound
to this actual coefficient error, rather than an abstract candidate row.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: subtract the genuine two-edge source residual from the actual
original Cholesky row equation multiplied by its true matrix size.
Distribute only finite sums and the original scalar normalization. -/
theorem choleskyError_equation (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i:Fin (n+1)) (j:Fin i.val) :
    choleskyError a b ha hb n i j+
      (∑k:Fin i.val, choleskyError a b ha hb n i k*
        gramPerturbation a b ha hb n (Gram.before i k) (Gram.before i j))=
      -choleskyResidual a b ha hb n i (Gram.before i j) := by
  -- Subtract the genuine candidate residual from the actual coefficient equation at scale N.
  have hh := rowCoefficient_perturbation_system a b ha hb n i j
  unfold choleskyError choleskyResidual
  simp_rw [sub_mul,Finset.sum_sub_distrib]
  have hs : (∑k:Fin i.val, (((n:ℝ)+1)*rowCoefficient a b ha hb n i k)*
      gramPerturbation a b ha hb n (Gram.before i k) (Gram.before i j)) =
      ((n:ℝ)+1)*(∑k:Fin i.val, rowCoefficient a b ha hb n i k*
        gramPerturbation a b ha hb n (Gram.before i k) (Gram.before i j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs]
  linear_combination ((n:ℝ)+1)*hh

/-- The genuine original matrix-size-scaled Cholesky coefficients
converge uniformly to the two actual source transformation kernels on
the whole original physical half triangle.
Use: the true finite target polynomial and eigenvector limits insert
this complete actual transformation into the original Schur formula.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the complete original GL residual is uniformly small. Every
genuine growing preceding Gram block has the proved uniform positive
gap, and every original perturbation entry is O(1/N). The established
finite coercive maximum-norm inverse estimate therefore makes the
actual error row uniformly small, with constants independent of row
and preceding-block size. Its equation is proved for the actual rows. -/
theorem cholesky_uniform_limit (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, ∀ i:Fin (n+1), 2*i.val≤n+1 →
      ∀ j:Fin i.val,
      |((n:ℝ)+1)*rowCoefficient a b ha hb n i j-
        twoEdgeTransformation a b ha hb n i (Gram.before i j)|<ε := by
  -- Use the same actual principal gap for every row, including growing and empty preceding blocks.
  classical
  obtain ⟨κ,hκ,NG,hgap⟩ := principalGram_uniform_coercive a b ha hb
  obtain ⟨C,hC,hentry⟩ := gramPerturbation_entry_bound ha hb
  obtain ⟨NE,hE⟩ := eventually_atTop.mp hentry
  let L : ℝ := 1+C/κ
  have hL : 0<L := by dsimp [L]; positivity
  intro ε hε
  let η : ℝ := ε/(2*L)
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨NR,hR⟩ := choleskyResidual_uniform a b ha hb η hη
  refine ⟨max (max NG NE) NR,fun n hn i hi j => ?_⟩
  let E : Fin i.val→Fin i.val→ℝ := fun k l =>
    gramPerturbation a b ha hb n (Gram.before i k) (Gram.before i l)
  have hbefore (k:Fin i.val) : 2*(Gram.before i k).val≤n+1 := by
    have hk := k.isLt
    change 2*k.val≤n+1
    omega
  have hblock (k l:Fin i.val) : targetGram a b ha hb n (Gram.before i k) (Gram.before i l)=
      (if k=l then (1:ℝ) else 0)+E k l := by
    have he : (Gram.before i k=Gram.before i l)↔k=l :=
      ⟨fun h => Fin.ext (congrArg (fun r:Fin (n+1) => r.val) h),fun h => congrArg _ h⟩
    dsimp only [E,gramPerturbation]
    simp only [Matrix.sub_apply,Matrix.one_apply,he]
    ring
  -- Identify the identity perturbation with the exact original preceding Gram block.
  have hA : ∀v:Fin i.val→ℝ, κ*(∑k, (v k)^2)≤
      ∑k,∑l, ((if k=l then (1:ℝ) else 0)+E k l)*v k*v l := by
    intro v
    simp_rw [← hblock]
    exact hgap n (by omega) i hi v
  -- Uniform maximum-norm stability turns the proved actual residual into coefficient convergence.
  have hbound := coercive_row_sup E hκ hC.le (by positivity : (0:ℝ)<(n:ℝ)+1)
    (show (Fintype.card (Fin i.val):ℝ)≤(n:ℝ)+1 from by
      simp only [Fintype.card_fin]
      exact_mod_cast i.isLt.le) hA
    (fun k l => hE n (by omega) (Gram.before i k) (Gram.before i l) (hbefore k) (hbefore l))
    (choleskyError a b ha hb n i)
    (fun k => -choleskyResidual a b ha hb n i (Gram.before i k))
    (fun k => choleskyError_equation a b ha hb n i k) hη.le
    (fun k => by rw [abs_neg]; exact (hR n (by omega) i (Gram.before i k) hi (hbefore k)).le)
  have he : (1+C/κ)*η=ε/2 := by dsimp [η,L]; field_simp
  exact (hbound j).trans_lt (by rw [he]; linarith)

end
end jacobi.Comparison
