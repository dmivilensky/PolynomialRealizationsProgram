import krylov.Envelope.PositiveReferenceOperator
import krylov.Envelope.PolynomialDifferential
import krylov.Reference.PolynomialAction

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:DK, actual differentiated quadratic CG Galerkin identity.
Use: compute the genuine real polynomial first-variation pairing with
the actual final CG gradient by differentiating true nearby quadratic
Galerkin orthogonality, without assuming any sensitivity identity.
Source: DaleckiiKrein65 for standard polynomial sensitivity attribution;
actual ordered noncommutative power differentiation and true CG Krylov orthogonality.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Polynomial Matrix Filter Topology
open scoped BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Every actual reference polynomial vector with genuine degree below the true horizon belongs to the real Krylov flag.
Use: Every actual reference polynomial vector with genuine degree below the true horizon belongs to the real Krylov flag.
Article: main_krylov, apB:lem:DK, actual differentiated quadratic CG Galerkin identity.
Proof: Use its genuine polynomial degree-subspace witness in the actual polynomial action image. -/
theorem polynomialAction_mem_krylov (Q : E →L[ℝ] E) (g : E) (N : ℕ) (p : ℝ[X])
    (hdegree : p.natDegree<N) : (aeval Q p) g∈CG.krylovSpace Q g N := by
  have hp : p∈Polynomial.degreeLT ℝ N := Polynomial.mem_degreeLT.mpr
    (Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hdegree))
  exact ⟨p,hp,rfl⟩

omit [CompleteSpace E] in
/-- Actual positive active quadratic CG satisfies the genuine differentiated Galerkin polynomial sensitivity identity with its true ordered operator-polynomial first variation.
Use: Actual positive active quadratic CG satisfies the genuine differentiated Galerkin polynomial sensitivity identity with its true ordered operator-polynomial first variation.
Article: main_krylov, apB:lem:DK, actual differentiated quadratic CG Galerkin identity.
Proof: Differentiate the actual noncommutative polynomial path and genuine computed CG gradient. True nearby quadratic Galerkin orthogonality makes their actual real inner product identically zero on a genuine neighborhood, so its real derivative vanishes. -/
theorem staticCG_polynomial_variation (Q : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (g : E) (N : ℕ)
    (haQ : AnalyticAt ℝ Q 0) (hdQ : HasDerivAt Q D 0)
    (hQ : (Q 0).toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q 0 v))
    (hpre : ∀ i<N, CG.gradient (Q 0) g i≠0)
    (hgood : ∀ᶠ t in 𝓝 (0 : ℝ), (Q t).toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q t v)) ∧ ∀ i<N, CG.gradient (Q t) g i≠0)
    (p : ℝ[X]) (hdegree : p.natDegree<N) :
    inner ℝ ((polynomialFirstVariation p (Q 0) D) g) (CG.gradient (Q 0) g N)+
      inner ℝ ((aeval (Q 0) p) g) (deriv (fun t => CG.gradient (Q t) g N) 0)=0 := by
  -- Differentiate the actual polynomial operator before using the genuine nearby quadratic CG Galerkin identity.
  have hp := hasDerivAt_polynomial p Q D 0 hdQ
  have hv : HasDerivAt (fun t => (aeval (Q t) p) g) ((polynomialFirstVariation p (Q 0) D) g) 0 := by
    simpa only [map_zero,add_zero] using hp.clm_apply (hasDerivAt_const (0 : ℝ) g)
  have hG := (cg_prefix_analytic Q (fun _ => g) 0 haQ analyticAt_const hQ hpos N hpre).1.differentiableAt.hasDerivAt
  have hprod := hv.inner ℝ hG
  have heq : (fun t => inner ℝ ((aeval (Q t) p) g) (CG.gradient (Q t) g N))=ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [hgood] with t ht
    exact CG.gradient_orthogonal_krylov (Q t) ht.1 ht.2.1 g N ht.2.2 (polynomialAction_mem_krylov (Q t) g N p hdegree)
  rw [add_comm,← hprod.deriv,heq.deriv_eq]
  exact deriv_const (0 : ℝ) 0
end
end krylov.Envelope
