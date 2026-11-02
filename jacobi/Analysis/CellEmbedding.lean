import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
Article: jacobi, Theorem 2.1.
Finite vectors are embedded into genuine L2 as constants on disjoint
measurable cells. The norm identity is exact, including unused space
outside the cells. This supplies the bridge between continuum coercivity
and the finite Gram sections; no sampled positivity is assumed.
Source: mathlib's L2 inner product of measurable indicator functions.
Use: cellEmbedding_inner and cellEmbedding_norm_sq transfer finite coefficient identities to the genuine continuum quadratic forms.
-/
namespace jacobi.Analysis
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} (S : ι → Set X) (hs : ∀ i, MeasurableSet (S i))
    (hf : ∀ i, μ (S i) ≠ ⊤)

/-- The actual finite step function, as an L2 equivalence class.
Use: cellEmbedding_inner and cellEmbedding_norm_sq transfer finite
coefficient identities to the genuine continuum quadratic forms.
Article: jacobi, Theorem 2.1.
-/
def cellEmbedding (v : ι → ℝ) : Lp ℝ 2 μ :=
  ∑ i, indicatorConstLp 2 (hs i) (hf i) (v i)

/-- The embedding has the expected actual step-function representative
almost everywhere.
Use: physical support and kernel-integral identities for the finite
vectors are proved on this representative and then passed to L2.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: combine the community finite-sum and indicator representative
identities over the finite family of cells. -/
theorem cellEmbedding_ae (v : ι → ℝ) :
    ⇑(cellEmbedding S hs hf v) =ᵐ[μ]
      fun x => ∑ i, (S i).indicator (fun _ => v i) x := by
  classical
  refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
  have hh : ∀ᵐ x ∂μ, ∀ i, indicatorConstLp 2 (hs i) (hf i) (v i) x =
      (S i).indicator (fun _ => v i) x :=
    ae_all_iff.mpr (fun i => indicatorConstLp_coeFn)
  filter_upwards [hh] with x hx
  exact Finset.sum_congr rfl (fun i _ => hx i)

/-- The genuine embedded L2 vector vanishes outside every set containing
all its cells.
Use: the Gram coercivity bridge applies the actual half-supported GL
quadratic lower bound to these finite step functions.
Article: jacobi, Theorem 2.1.
Proof: outside the containing set each indicator is zero. -/
theorem cellEmbedding_supported (T : Set X) (hST : ∀ i, S i ⊆ T) (v : ι → ℝ) :
    ∀ᵐ x ∂μ, x ∉ T → cellEmbedding S hs hf v x = 0 := by
  filter_upwards [cellEmbedding_ae S hs hf v] with x hx
  intro hxt
  rw [hx]
  apply Finset.sum_eq_zero
  intro i _
  exact Set.indicator_of_notMem (fun h => hxt (hST i h)) _

/-- Finite step functions decompose exactly into the scalar multiples
of their unit cell indicators.
Use: continuum quadratic forms of the paired vectors expand into
finite matrices of actual cell integrals in the Gram positivity proof.
Article: jacobi, Theorem 2.1.
Proof: the scalar indicator identities hold almost everywhere; L2
extensionality and the finite sum give the asserted genuine equality. -/
theorem cellEmbedding_sum_smul (v : ι → ℝ) :
    cellEmbedding S hs hf v =
      ∑ i, v i • indicatorConstLp 2 (hs i) (hf i) (1:ℝ) := by
  -- Reduce each scalar cell indicator to its genuine almost-everywhere representative.
  classical
  apply Finset.sum_congr rfl
  intro i _
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p:=2) (hs:=hs i) (hμs:=hf i) (c:=v i),
    indicatorConstLp_coeFn (p:=2) (hs:=hs i) (hμs:=hf i) (c:=(1:ℝ)),
    Lp.coeFn_smul (v i) (indicatorConstLp 2 (hs i) (hf i) (1:ℝ))] with x hx h1 hc
  rw [hx,hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [h1]
  by_cases hm : x∈S i <;> simp [hm]

/-- The exact inner product of two finite cell embeddings, before any
disjointness or equal-width assumption.
Use: cellEmbedding_norm_sq obtains the physical squared norm from the
true cell measures, rather than from an informal mesh normalization.
Article: jacobi, Theorem 2.1.
Source: mathlib, L2.inner_indicatorConstLp_indicatorConstLp.
Proof: expand both finite sums using bilinearity and evaluate each
indicator inner product by the measure of the actual intersection. -/
theorem cellEmbedding_inner (v w : ι → ℝ) :
    inner ℝ (cellEmbedding S hs hf v) (cellEmbedding S hs hf w) =
      ∑ i, ∑ j, μ.real (S i ∩ S j) * (v i * w j) := by
  simp only [cellEmbedding, sum_inner, inner_sum,
    L2.inner_indicatorConstLp_indicatorConstLp, smul_eq_mul]
  rw [Finset.sum_comm]
  simp [mul_comm]

/-- Disjoint cells of one common measure give the exact Euclidean
squared norm multiplied by the cell width.
Use: the uniform Gram coercivity argument scales both paired continuum
forms by their actual common Lebesgue mesh width; Theorem 2.1 uses the same
identity to normalize finite eigenvector embeddings.
Article: jacobi, Theorem 2.1.
Proof: all off-diagonal cell intersections are empty. Only the actual
diagonal measures survive the preceding exact inner-product identity. -/
theorem cellEmbedding_norm_sq (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    {h : ℝ} (hm : ∀ i, μ.real (S i) = h) (v : ι → ℝ) :
    ‖cellEmbedding S hs hf v‖^2 = h * ∑ i, (v i)^2 := by
  -- Disjointness removes every off-diagonal cell intersection from the actual inner product.
  classical
  rw [← real_inner_self_eq_norm_sq, cellEmbedding_inner]
  have hrow (i : ι) :
      (∑ j, μ.real (S i ∩ S j) * (v i * v j)) = h * (v i)^2 := by
    rw [Finset.sum_eq_single i]
    · simp [hm, pow_two]
    · intro j _ hji
      rw [Set.disjoint_iff_inter_eq_empty.mp (hd (Ne.symm hji))]
      simp
    · simp
  simp_rw [hrow]
  exact (Finset.mul_sum _ _ _).symm

end
end jacobi.Analysis
