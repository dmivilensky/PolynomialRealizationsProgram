import krylov.Information.PlanarLowerFibre
import krylov.Stability.ReferenceErrorRegularity

/-!
Article: main_krylov, thm:C, own-base normalization of explicit lower scenarios.
Use: derive the true base positivity and reference-error control uniformly
on the actual rank-one base family used by every budget profile.
Source: actual root congruence, genuine CG analyticity and the proved
first-order reference-error norm variation.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.LinearAlgebra krylov.Stability krylov.Correction
open scoped MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine physical rank-one base family containing both explicit unknown-base lower witnesses.
Use: one real base parameter covers every budget profile's two signed bases.
Article: main_krylov, thm:C, A₀^σ=A¹ᐟ²(I+δffᵀ)A¹ᐟ². -/
def rankBaseCurve (A : Matrix (Fin n) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n))
    (δ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  inverseFormMap (metricRoot A)⁻¹ (1+δ • vecMulVec (WithLp.ofLp f) (WithLp.ofLp f))

/-- The actual rank-one base curve starts at the original physical positive reference.
Use: apply true CG reference regularity at the intended base.
Article: main_krylov, thm:C, A₀(0)=A.
Proof: its genuine canonical rank-one term vanishes and the actual inverse
root coordinate map sends the identity exactly to A. -/
theorem rankBaseCurve_zero (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ (Fin n)) : rankBaseCurve A f 0=A := by
  simp only [rankBaseCurve,zero_smul,add_zero,inverseRootForm_one A hA]

/-- The actual rank-one physical base curve is analytic in its real coefficient.
Use: establish normalization regularity jointly for all signed budget witnesses.
Article: main_krylov, thm:C, true lower-base parameter regularity.
Proof: the actual canonical affine matrix curve is analytic, and the
fixed physical inverse-root form map is a continuous linear map. -/
theorem rankBaseCurve_analyticAt (A : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n)) (δ : ℝ) : AnalyticAt ℝ (rankBaseCurve A f) δ := by
  have hinner : AnalyticAt ℝ (fun t : ℝ => 1+t • vecMulVec (WithLp.ofLp f) (WithLp.ofLp f)) δ :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  exact ((inverseFormMap (metricRoot A)⁻¹).toContinuousLinearMap.analyticAt _).comp hinner

/-- Every actual rank-one lower base is positive on the full strict unit coefficient interval.
Use: the normalization is always taken in a genuine metric on the common lower-witness tube.
Article: main_krylov, thm:C, positivity of A₀^σ.
Proof: the genuine rank-one norm is one. Its scalar perturbation has norm
|δ|<1, so the actual shifted identity is positive; the invertible physical
root congruence preserves its strict positivity.
-/
theorem rankBaseCurve_posDef (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ (Fin n)) (hf : ‖f‖=1) {δ : ℝ} (hδ : |δ|<1) :
    (rankBaseCurve A f δ).PosDef := by
  -- Prove positivity of the true canonical rank-one base before physical transport.
  let P := vecMulVec (WithLp.ofLp f) (WithLp.ofLp f)
  have hP : P.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [P,vecMulVec_apply]
    ring
  have hnorm : chebyshev1.opNorm P=1 := by
    simpa only [P,WithLp.toLp_ofLp,hf,mul_one] using spectral_norm_rankOne (WithLp.ofLp f) (WithLp.ofLp f)
  have hsmall : chebyshev1.opNorm (δ • P)<1 := by
    simpa only [chebyshev1.opNorm_smul,hnorm,mul_one] using hδ
  have hG : (1+δ • P).PosDef := by
    simpa only [one_smul] using (strict_shifted_posDef _ (hP.smul δ) hsmall).2
  exact inverseForm_posDef _ _ (Matrix.isUnit_nonsing_inv_det _ (metricRoot_det_unit A hA)) hG

/-- The true active spectral count never exceeds the actual physical dimension.
Use: strict last-reference-error positivity on the perturbed lower bases derives the original full-atom condition.
Article: main_krylov, thm:C, preservation of genuine full reference nondegeneracy.
Proof: the actual spectral support is an image of a filtered subset of the
finite physical eigenvector basis, so its cardinality is at most n. -/
theorem referenceAtomCount_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) : referenceAtomCount A hA g≤n := by
  unfold referenceAtomCount activeSpectralValues
  exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n))

/-- One actual rank-one base tube preserves full reference activity and controls the true normalization for every lower-witness profile.
Use: both signed scenarios use their own genuine base metric and source φ, with constants chosen before all profiles.
Article: main_krylov, thm:C, uniform lower-family normalization transfer.
Proof: the actual rank-one curve is positive and analytic near the original
reference. Genuine CG error regularity gives a true first-order norm bound.
Choose one tube where that variation is less than half the positive actual
reference error. Its normalization stays positive and has the stated relative
Lipschitz bound. Nonzero true last CG residual and the finite spectral-cardinality
bound derive the original full-atom condition on every perturbed base.
-/
theorem rankBaseCurve_reference_control {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1)))
    (hcount : referenceAtomCount A hA g=N+1)
    (f : EuclideanSpace ℝ (Fin (N+1))) (hf : ‖f‖=1) :
    ∃ ε L : ℝ, 0<ε ∧ 0<L ∧ ∀ δ : ℝ, |δ|<ε →
      ∃ hB : (rankBaseCurve A f δ).PosDef,
        referenceAtomCount (rankBaseCurve A f δ) hB g=N+1 ∧
        0<‖cgCanonicalError (rankBaseCurve A f δ) g N‖ ∧
        ‖cgCanonicalError (rankBaseCurve A f δ) g N‖≤‖cgCanonicalError A g N‖*(1+L*|δ|) := by
  -- The true reference norm is strictly positive by the original active-atom premise.
  let a := ‖cgCanonicalError A g N‖
  have ha : 0<a := canonical_error_pos A hA _ (cg_nonstagnation A hA g N (by omega))
  have hpos : ∀ᶠ δ : ℝ in 𝓝 0, (rankBaseCurve A f δ).PosDef := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ)<1)] with δ hδ
    exact rankBaseCurve_posDef A hA f hf (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hδ)
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator (rankBaseCurve A f 0)) g i≠0 := by
    rw [rankBaseCurve_zero A hA f]
    exact cg_nonstagnation A hA g i (by omega)
  have horder : (fun δ : ℝ => ‖cgCanonicalError (rankBaseCurve A f δ) g N‖-a) =O[𝓝 0] (fun δ => ‖δ‖) := by
    simpa only [rankBaseCurve_zero A hA f] using
      referenceError_norm_order (rankBaseCurve A f) (fun _ => g) N (rankBaseCurve_analyticAt A f 0)
        hpos analyticAt_const hpre
  obtain ⟨C,hC,hbound⟩ := isBigO_iff'.mp horder
  obtain ⟨ε₀,hε₀,hεbound⟩ := Metric.eventually_nhds_iff.mp hbound
  let ε := min 1 (min ε₀ (a/(2*C)))
  let L := C/a
  have hε : 0<ε := lt_min (by norm_num) (lt_min hε₀ (div_pos ha (by positivity)))
  have hL : 0<L := div_pos hC ha
  refine ⟨ε,L,hε,hL,?_⟩
  intro δ hδ
  -- The same radius controls positivity, the actual error variation and its normalization.
  have hδ₁ : |δ|<1 := hδ.trans_le (min_le_left _ _)
  have hδ₀ : |δ|<ε₀ := hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδa : |δ|<a/(2*C) := hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hB := rankBaseCurve_posDef A hA f hf hδ₁
  have hb := hεbound (by simpa only [Real.dist_eq,sub_zero] using hδ₀)
  have hclose : |‖cgCanonicalError (rankBaseCurve A f δ) g N‖-a|≤C*|δ| := by
    simpa only [Real.norm_eq_abs,abs_abs] using hb
  have hsmall : C*|δ|<a/2 := by
    have ht := (lt_div_iff₀ (by positivity : (0 : ℝ)<2*C)).mp hδa
    linarith
  have hnorm : 0<‖cgCanonicalError (rankBaseCurve A f δ) g N‖ := by
    have hl := neg_abs_le (‖cgCanonicalError (rankBaseCurve A f δ) g N‖-a)
    linarith
  have hgrad : CG.gradient (cgOperator (rankBaseCurve A f δ)) g N≠0 := by
    intro hz
    have he : cgCanonicalError (rankBaseCurve A f δ) g N=0 := by
      simp only [cgCanonicalError,hz,map_zero]
    rw [he,norm_zero] at hnorm
    exact (lt_irrefl (0 : ℝ)) hnorm
  have hactive : N<referenceAtomCount (rankBaseCurve A f δ) hB g := by
    by_contra hc
    exact hgrad ((cg_stopping_iff _ hB g N).mpr (by omega))
  have hfull : referenceAtomCount (rankBaseCurve A f δ) hB g=N+1 := by
    have hle := referenceAtomCount_le _ hB g
    omega
  refine ⟨hB,hfull,hnorm,?_⟩
  calc
    _ ≤ a+C*|δ| := by have hu := le_abs_self (‖cgCanonicalError (rankBaseCurve A f δ) g N‖-a); linarith
    _ = a*(1+L*|δ|) := by dsimp only [L]; field_simp [ha.ne']

/-- The actual rank-one physical base displacement has exactly its scalar canonical budget.
Use: the already proved scenario radius controls the real parameter in the common normalization tube.
Article: main_krylov, thm:C, ‖A₀(δ)−A‖_A=|δ|.
Proof: linear inverse-root transport preserves the true base difference and
its genuine relative norm. At the identity, the actual unit rank-one form
has exact spectral norm one, so scaling gives |δ|.
-/
theorem rankBaseCurve_budget (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ (Fin n)) (hf : ‖f‖=1) (δ : ℝ) :
    relativeBudget A (rankBaseCurve A f δ-A)=|δ| := by
  -- Use genuine congruence invariance on the same physical displacement.
  let D := (metricRoot A)⁻¹
  let P := vecMulVec (WithLp.ofLp f) (WithLp.ofLp f)
  have hP : P.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [P,vecMulVec_apply]
    ring
  have hnorm : ‖P‖=1 := by
    simpa only [P,chebyshev1.opNorm,WithLp.toLp_ofLp,hf,mul_one] using
      spectral_norm_rankOne (WithLp.ofLp f) (WithLp.ofLp f)
  have hd : rankBaseCurve A f δ-A=inverseFormMap D (δ • P) := by
    simp only [D,P,rankBaseCurve,map_add,inverseRootForm_one A hA,add_sub_cancel_left]
  have hb := inverseForm_budget D 1 (δ • P)
    (Matrix.isUnit_nonsing_inv_det _ (metricRoot_det_unit A hA)) Matrix.PosDef.one (hP.smul δ)
  calc
    _ = relativeBudget A (inverseFormMap D (δ • P)) := congrArg (relativeBudget A) hd
    _ = relativeBudget 1 (δ • P) := by simpa only [D,inverseRootForm_one A hA] using hb
    _ = |δ| := by rw [relativeBudget_one,norm_smul,Real.norm_eq_abs,hnorm,mul_one]

end
end krylov.Information
