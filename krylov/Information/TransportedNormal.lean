import krylov.Correction.FullReconstruction
import krylov.LinearAlgebra.NormalizedRankOne
import krylov.Stability.WeightedNormalization
import krylov.Stability.AnalyticMatrix

/-!
Article: main_krylov, thm:C2(c), the actual moving observed-hyperplane normal.
Use: derive the genuine first-order normal displacement from the actual
nonsingular query basis, without imposing a supplied direction estimate.
Source: exact inverse-transpose transport, true analytic matrix inverse
and the existing weighted zero-safe normalization inequality.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Reference krylov.Secant
  krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine inverse-transpose transported normal of the actual query basis relative to its true reference basis.
Use: it is exactly the reference first CG unit step at the reference and annihilates the actual observed later query columns.
Article: main_krylov, thm:C2(c), v₀ before unit normalization. -/
def transportedNormal (C C₀ : Matrix (Fin n) (Fin n) ℝ)
    (e : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  cgOperator (Cᵀ⁻¹*C₀ᵀ) e

/-- The true moving unit normal obtained from the actual inverse-transpose query-basis transport.
Use: zero-safe normalization makes the data-only rule total even on impossible degenerate inputs.
Article: main_krylov, thm:C2(c), normalized actual unobserved direction v₀. -/
def transportedUnitNormal (C C₀ : Matrix (Fin n) (Fin n) ℝ)
    (e : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  NormedSpace.normalize (transportedNormal C C₀ e)

/-- The actual transported normal is exactly the intended reference direction at its genuine nonsingular reference basis.
Use: a positive first-order neighborhood is based at the real CG normal, with no sign choice or guessed scale.
Article: main_krylov, thm:C2(c), v₀(0)=ŝ₀.
Proof: the genuine inverse transpose cancels the true reference transpose. -/
theorem transportedNormal_reference (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUnit C.det)
    (e : EuclideanSpace ℝ (Fin n)) : transportedNormal C C e=e := by
  have ht : IsUnit Cᵀ.det := by simpa only [det_transpose] using hC
  simp only [transportedNormal,nonsing_inv_mul _ ht,cgOperator,map_one,one_apply_eq_self]

/-- True unit-reference normalization has a global twice-distance bound, including the zero-vector input.
Use: transfer the actual analytic transported-normal estimate without assuming any differentiability of a normalized direction selector.
Article: main_krylov, thm:C2(c), ‖normalize(w)−e‖≤2‖w−e‖.
Proof: the existing weighted normalization theorem handles every nonzero
input at reference scale one. A zero input has distances one and two,
so the same original inequality holds directly in the degenerate case.
-/
theorem unit_reference_normalization_bound (w e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) :
    ‖NormedSpace.normalize w-e‖≤2*‖w-e‖ := by
  by_cases hw : w=0
  · simp only [hw,NormedSpace.normalize_zero_eq_zero,zero_sub,norm_neg,he]
    norm_num
  · simpa only [one_mul,one_smul] using normalization_weighted w e hw he 1 (by norm_num)

/-- True Euclidean matrix actions transpose exactly when moved across the real inner product.
Use: identify the actual moving hyperplane normal from the original observed query columns.
Article: main_krylov, thm:C2(c), exact dual query pairing.
Proof: reuse the existing real rectangular transpose pairing on the actual Euclidean coordinates. -/
theorem matrix_action_transpose_pairing (C : Matrix (Fin n) (Fin n) ℝ)
    (u v : EuclideanSpace ℝ (Fin n)) : inner ℝ (cgOperator C u) v=inner ℝ u (cgOperator Cᵀ v) := by
  simpa only [cgOperator,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,Matrix.ofLp_toEuclideanCLM,dotProduct_comm] using
    transpose_pairing C (WithLp.ofLp u) (WithLp.ofLp v)

/-- The genuinely transported normal preserves precisely the original reference covector pairings on every actual query combination.
Use: the actual later query columns are perpendicular whenever their true reference columns are.
Article: main_krylov, thm:C2(c), Cᵀw=C₀ᵀŝ₀.
Proof: move the actual basis across the real pairing, cancel its genuine
invertible transpose and move the true reference basis back. No normalized
query frame or supplied subspace identity is assumed.
-/
theorem transportedNormal_pairing (C C₀ : Matrix (Fin n) (Fin n) ℝ) (hC : IsUnit C.det)
    (e u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (cgOperator C u) (transportedNormal C C₀ e)=inner ℝ (cgOperator C₀ u) e := by
  -- Only the actual current query-basis inverse is needed for the exact physical pairing.
  have ht : IsUnit Cᵀ.det := by simpa only [det_transpose] using hC
  rw [matrix_action_transpose_pairing]
  have hc : cgOperator Cᵀ (transportedNormal C C₀ e)=cgOperator C₀ᵀ e := by
    simp only [transportedNormal,cgOperator,← mul_apply_eq_comp,← map_mul,← Matrix.mul_assoc,
      mul_nonsing_inv _ ht,Matrix.one_mul]
  rw [hc,← matrix_action_transpose_pairing]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine transported normal is analytic wherever the actual query-basis reference determinant is nonzero.
Use: derive the moving-normal error directly from true finite query data and real inverse domains.
Article: main_krylov, thm:C2(c), primitive actual normal regularity.
Proof: transpose preserves real analytic matrix entries; the proved genuine
spectral matrix inverse is analytic at its actual nonzero determinant.
The fixed reference transpose and fixed vector preserve this regularity.
-/
theorem transportedNormal_analyticAt (C : X → Matrix (Fin n) (Fin n) ℝ) (x : X)
    (hC : ∀ i j, AnalyticAt ℝ (fun y => C y i j) x) (hu : IsUnit (C x).det)
    (C₀ : Matrix (Fin n) (Fin n) ℝ) (e : EuclideanSpace ℝ (Fin n)) :
    AnalyticAt ℝ (fun y => transportedNormal (C y) C₀ e) x := by
  -- Justify the genuine inverse before transporting its actual fixed reference covector.
  have hi : AnalyticAt ℝ (fun y => (C y)ᵀ⁻¹) x :=
    analytic_spectral_matrix_inv (fun y => (C y)ᵀ) x (fun i j => hC j i)
      (by simpa only [det_transpose] using isUnit_iff_ne_zero.mp hu)
  let L := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
  have hop : AnalyticAt ℝ (fun y => cgOperator ((C y)ᵀ⁻¹*C₀ᵀ)) x :=
    (L.analyticAt _).comp (hi.mul analyticAt_const)
  exact analytic_operator_apply hop analyticAt_const

/-- The actual moving unit normal has a genuine first-order reference displacement, with all regularity and inverse-domain premises supplied by the actual query basis.
Use: close the geometric loss in the true original-budget midpoint coefficient at cubic order.
Article: main_krylov, thm:C2(c), v₀=ŝ₀+O(ω).
Proof: the genuine transported normal is analytic and equals the true unit
reference direction at zero. Its actual first-order difference estimate
passes through the global twice-distance normalization inequality. No
smoothness of the final consistency-midpoint selector is required.
-/
theorem transportedUnitNormal_order (C : X → Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, AnalyticAt ℝ (fun y => C y i j) 0) (hu : IsUnit (C 0).det)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) :
    (fun y => transportedUnitNormal (C y) (C 0) e-e) =O[𝓝 (0 : X)] (fun y => ‖y‖) := by
  -- The actual analytic reference transport supplies the first-order difference before unit normalization.
  have ha := transportedNormal_analyticAt C 0 hC hu (C 0) e
  have ho : (fun y => transportedNormal (C y) (C 0) e-e) =O[𝓝 (0 : X)] (fun y => ‖y‖) := by
    simpa only [transportedNormal_reference (C 0) hu e] using
      analytic_reference_order (fun y => transportedNormal (C y) (C 0) e) ha
  have hn : (fun y => transportedUnitNormal (C y) (C 0) e-e) =O[𝓝 (0 : X)]
      (fun y => transportedNormal (C y) (C 0) e-e) :=
    isBigO_iff.mpr ⟨2,Eventually.of_forall fun y => by
      simpa only [transportedUnitNormal,norm_norm] using
        unit_reference_normalization_bound (transportedNormal (C y) (C 0) e) e he⟩
  exact hn.trans ho


/-- The actual moving normal is nonzero, its actual query basis is invertible and its normalized vector is unit on one genuine reference neighborhood.
Use: the informed source algorithm's observed hyperplane has its true local inverse and normalization domains derived from actual basis data.
Article: main_krylov, thm:C2(c), genuine local well-definedness of v₀.
Proof: the actual basis determinant and transported normal are continuous
at the genuine nonsingular reference. Their nonzero true reference values
persist on a common neighborhood; zero-safe normalization is then truly unit.
-/
theorem transportedUnitNormal_domains (C : X → Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, AnalyticAt ℝ (fun y => C y i j) 0) (hu : IsUnit (C 0).det)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) :
    ∀ᶠ y in 𝓝 (0 : X), IsUnit (C y).det ∧ transportedNormal (C y) (C 0) e≠0 ∧
      ‖transportedUnitNormal (C y) (C 0) e‖=1 := by
  -- Both genuine reference nonzero values precede the actual normalization and matrix inverse.
  have hm := analytic_spectral_matrix C 0 hC
  have hdet := (continuous_id.matrix_det.continuousAt.comp hm.continuousAt).eventually_ne
    (isUnit_iff_ne_zero.mp hu)
  have ha := transportedNormal_analyticAt C 0 hC hu (C 0) e
  have he0 : transportedNormal (C 0) (C 0) e≠0 := by
    rw [transportedNormal_reference (C 0) hu e]
    exact norm_ne_zero_iff.mp (by rw [he]; norm_num)
  have hn := ha.continuousAt.eventually_ne he0
  filter_upwards [hdet,hn] with y hyd hyn
  exact ⟨isUnit_iff_ne_zero.mpr hyd,hyn,NormedSpace.norm_normalize hyn⟩

end
end krylov.Information
