import krylov.Reference.CGGeometry
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
Article: main_krylov, def:methods, alg:fc and lem:consistent.
Use: construct the actual data-only conjugacy solve and prove its uniqueness,
span restriction and exact correction equations for arbitrary finite windows.
Source: the block conjugacy projector of Schnabel83 and VlcekLuksan19;
positive operator Gram matrices are proved directly from the actual vectors.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Form a physical window displacement from its actual coefficient vector.
Use: correction and direction policies can act only in the stored observed span.
Article: main_krylov, def:classes(M), U_k w_k. -/
def combine (s : ι → E) (c : ι → ℝ) : E := ∑ i, c i • s i

/-- Pair the actual physical vector with each stored observation.
Use: all finite model right-hand sides depend only on available data.
Article: main_krylov, def:methods, Sᵀg and Yᵀg. -/
def coordinates (s : ι → E) (v : E) : ι → ℝ := fun i => inner ℝ (s i) v

/-- The actual cross Gram matrix of two observed vector families.
Use: the FC coefficient matrix is YᵀS, including incompatible secant pairs.
Article: main_krylov, s2:eq:fcdir, YᵀS. -/
def crossGram (y s : ι → E) : Matrix ι ι ℝ := fun i j => inner ℝ (y i) (s j)

/-- Observed coordinates of a window combination are the actual cross Gram matrix action.
Use: reduces physical conjugacy and correction equations to their finite coefficient solves.
Article: main_krylov, def:methods, block coefficient equations.
Proof: expand the finite sum and use linearity of the real inner product. -/
theorem coordinates_combine (y s : ι → E) (c : ι → ℝ) :
    coordinates y (combine s c)=crossGram y s *ᵥ c := by
  ext i
  simp only [coordinates, combine, crossGram, inner_sum, real_inner_smul_right, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Every actual window combination belongs to the span of its stored vectors.
Use: verifies the article's observed-span information restriction for concrete solves.
Article: main_krylov, def:classes, linear span of observed vectors.
Proof: every summand is a scalar multiple of a generator of the stored span. -/
theorem combine_mem_span (s : ι → E) (c : ι → ℝ) : combine s c∈Submodule.span ℝ (Set.range s) :=
  Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- The physical quadratic form of an actual operator Gram matrix equals the original operator energy.
Use: positivity and invertibility of quadratic model solves follow from actual vector independence.
Article: main_krylov, lem:consistent, positive reference Gram matrix.
Proof: expand both actual linear combinations and collect their finite inner-product sums. -/
theorem operatorGram_form (Q : E →L[ℝ] E) (s : ι → E) (c : ι → ℝ) :
    c ⬝ᵥ (crossGram (fun i => Q (s i)) s *ᵥ c)=inner ℝ (Q (combine s c)) (combine s c) := by
  simp only [crossGram, combine, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, dotProduct, Matrix.mulVec, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual Gram matrix of independent vectors through a symmetric positive operator is positive definite.
Use: proves all quadratic secant-model denominators before any inverse is used.
Article: main_krylov, lem:consistent, SᵀAS positive definite.
Proof: a nonzero coefficient vector gives a nonzero physical combination;
the actual positive operator energy equals its coefficient quadratic form. -/
theorem operatorGram_posDef (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) {s : ι → E} (hs : LinearIndependent ℝ s) :
    (crossGram (fun i => Q (s i)) s).PosDef := by
  -- Positivity is tested on the actual physical vector produced by the coefficient vector.
  have hsym : (crossGram (fun i => Q (s i)) s).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    have he := hQ (s i) (s j)
    change inner ℝ (Q (s i)) (s j)=inner ℝ (s i) (Q (s j)) at he
    simpa only [crossGram, star_trivial] using (he.trans (real_inner_comm _ _)).symm
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro c hc
  have hv : combine s c≠0 := by
    intro hz
    have hzero := Fintype.linearIndependent_iff.mp hs c hz
    exact hc (funext hzero)
  rw [star_trivial, operatorGram_form, real_inner_comm]
  exact hpos _ hv

variable [DecidableEq ι]

/-- The actual data-only FC conjugacy coefficients.
Use: the unknown segment operator is absent from the decision rule.
Article: main_krylov, s2:eq:fcdir, β=(YᵀS)⁻¹Yᵀg. -/
def conjugacyCoefficients (s y : ι → E) (g : E) : ι → ℝ :=
  (crossGram y s)⁻¹ *ᵥ coordinates y g

/-- The actual FC direction computed from the stored secant data.
Use: FC and both corrected realizations share this exact observed-data solve.
Article: main_krylov, s2:eq:fcdir, d=−g+Sβ. -/
def conjugacyDirection (s y : ι → E) (g : E) : E :=
  -g+combine s (conjugacyCoefficients s y g)

/-- The computed FC direction annihilates every stored image whenever its actual model solve is nonsingular.
Use: full conjugacy is derived from the implemented inverse, also for nonconjugate pairs.
Article: main_krylov, def:methods, Yᵀd=0.
Proof: expand its observed coordinates and cancel the actual coefficient matrix against its nonsingular inverse. -/
theorem conjugacyDirection_conjugate (s y : ι → E) (g : E)
    (hC : IsUnit (crossGram y s).det) : coordinates y (conjugacyDirection s y g)=0 := by
  ext i
  have he := congrFun (coordinates_combine y s (conjugacyCoefficients s y g)) i
  rw [conjugacyCoefficients, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC, Matrix.one_mulVec] at he
  change inner ℝ (y i) (-g+combine s (conjugacyCoefficients s y g))=0
  rw [inner_add_right, inner_neg_right, show inner ℝ (y i) (combine s (conjugacyCoefficients s y g))=
    inner ℝ (y i) g from he]
  exact neg_add_cancel _

/-- The actual conjugacy solve recovers any candidate with the same stored-span displacement and zero stored-image pairings.
Use: one uniqueness theorem proves the concrete quadratic consistency for every retained CG window.
Article: main_krylov, lem:consistent, the unique block conjugacy direction.
Proof: write the candidate as −g+Sc; its zero observed coordinates solve the
same nonsingular finite linear system, so the computed coefficient vector is c. -/
theorem conjugacyDirection_unique (s y : ι → E) (g d : E)
    (hC : IsUnit (crossGram y s).det) (hd : d+g∈Submodule.span ℝ (Set.range s))
    (ho : coordinates y d=0) : conjugacyDirection s y g=d := by
  -- Only the candidate's data-visible displacement is used; no unknown operator action enters the solve.
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hd
  have hphys : d= -g+combine s c := by
    change combine s c=d+g at hc
    rw [hc]
    abel
  have hsystem : crossGram y s *ᵥ c=coordinates y g := by
    rw [← coordinates_combine]
    ext i
    have hz := congrFun ho i
    change inner ℝ (y i) d=0 at hz
    change inner ℝ (y i) (combine s c)=inner ℝ (y i) g
    rw [show combine s c=d+g from hc, inner_add_right, hz, zero_add]
  have hcoeff : conjugacyCoefficients s y g=c := by
    rw [conjugacyCoefficients, ← hsystem, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hC, Matrix.one_mulVec]
  rw [conjugacyDirection, hcoeff]
  exact hphys.symm

/-- The actual correction coefficients for a supplied observed model matrix.
Use: RFC and XRFC corrections remain combinations of stored or probed vectors.
Article: main_krylov, alg:fc, w=−H⁻¹Uᵀg. -/
def modelCoefficients (s : ι → E) (H : Matrix ι ι ℝ) (g : E) : ι → ℝ :=
  -(H⁻¹ *ᵥ coordinates s g)

/-- A model correction vanishes whenever its actual projected residual vanishes.
Use: quadratic RFC consistency covers every finite number of repeated corrections.
Article: main_krylov, lem:consistent, all corrections zero.
Proof: a linear inverse applied to the zero right-hand side returns the zero coefficient vector. -/
theorem modelCoefficients_zero (s : ι → E) (H : Matrix ι ι ℝ) (g : E)
    (hg : coordinates s g=0) : modelCoefficients s H g=0 := by
  rw [modelCoefficients, hg, Matrix.mulVec_zero, neg_zero]

end
end krylov.Methods
