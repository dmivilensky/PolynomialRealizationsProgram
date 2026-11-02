import jacobi.Applications.StandardSlope
import jacobi.Finite.FlowPolynomialMinimum

/-!
Gaussian quadrature for the actual standard Jacobi spectral weights.
The first N shifted Jacobi polynomials have identical discrete spectral
and normalized continuous integrals. Their degree-graded span gives every
lower-degree test polynomial. Division by the degree-N orthogonal
polynomial then proves exactness through degree 2N-1.
Use: this identifies the standard realization's actual first-site
spectral probabilities with the normalized Gauss-Jacobi quadrature rule.
Article: jacobi, Section 5.5, before Theorem 5.4.
Article role: identification of the standard spectral probabilities with normalized Gauss-Jacobi
weights.
Source: classical Gaussian quadrature, exact through degree 2n-1; NIST DLMF Section 3.5.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Polynomial Set MeasureTheory jacobi.Finite jacobi.Applications jacobi.Reference
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual standard chain's positive spectral probabilities as a
discrete measure on its original descending Jacobi nodes.
Article: jacobi, Section 5.5, before Theorem 5.4.
Source: classical Gaussian quadrature, exact through degree 2n-1; NIST DLMF Section 3.5.
-/
def standardSpectralMeasure (a b : ℝ) (ha : -1<a) (hb : -1<b) (N : ℕ) : DiscreteMeasure (N+1) :=
  (nodes a b ha hb (N+1)).measure (spectralWeights (nodes a b ha hb (N+1))
    ⟨standardChain a b ha hb (N+1),standardChain_inFiber ha hb (N+1)⟩)

/-- Inverse spectral reconstruction recovers this exact standard matrix.
Article: jacobi, Section 5.5, before Theorem 5.4.
Source: classical Gaussian quadrature, exact through degree 2n-1; NIST DLMF Section 3.5.
-/
theorem standardSpectralMeasure_reconstructed {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ) :
    (standardSpectralMeasure a b ha hb N).reconstructed=standardChain a b ha hb (N+1) :=
  congrArg Subtype.val (reconstruct_spectralWeights (nodes a b ha hb (N+1))
    ⟨standardChain a b ha hb (N+1),standardChain_inFiber ha hb (N+1)⟩)

/-- The quadrature functional uses the actual spectral probabilities
and the corresponding shifted roots, rather than independently chosen weights.
Article: jacobi, Section 5.5, before Theorem 5.4.
Source: classical Gaussian quadrature, exact through degree 2n-1; NIST DLMF Section 3.5.
-/
def standardGaussMap (a b : ℝ) (ha : -1<a) (hb : -1<b) (N : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∑ k,(standardSpectralMeasure a b ha hb N).weight k*
    p.eval (shiftedRoots a b ha hb (N+1) k)
  map_add' p q := by simp [eval_add,mul_add,Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [eval_smul,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Every positive-degree Jacobi polynomial below the support size has
zero actual Gaussian sum; the constant polynomial has sum one.
Article: jacobi, Section 5.5, before Theorem 5.4.
Source: classical Gaussian quadrature, exact through degree 2n-1; NIST DLMF Section 3.5.
-/
theorem standardGaussMap_basis {a b : ℝ} (ha : -1<a) (hb : -1<b) {N j : ℕ} (hj : j < N+1) :
    standardGaussMap a b ha hb N (shiftedPolynomial a b j)=if j=0 then 1 else 0 := by
  let M := standardSpectralMeasure a b ha hb N
  by_cases hj0 : j=0
  · subst j
    simp only [standardGaussMap,LinearMap.coe_mk,AddHom.coe_mk,shiftedPolynomial_initial,eval_one,mul_one,ite_true]
    exact M.probability
  · rw [ite_eq_right hj0]
    have h := M.leading_orthogonal_lower ⟨j,hj⟩ (q := 1) (by simp; omega)
    rw [standardSpectralMeasure_reconstructed] at h
    have he (k : Fin (N+1)) : ((standardChain a b ha hb (N+1)).data.leading j).eval (M.node k)=
        standardNormalization a b j*(shiftedPolynomial a b j).eval (shiftedRoots a b ha hb (N+1) k) := by
      rw [standardChain_leading_eval ha hb (N+1) j hj.le]
      congr 2
      dsimp [M,standardSpectralMeasure,Nodes.measure,nodes]
      ring
    simp_rw [he,eval_one,mul_one] at h
    have he' : (∑ k,M.weight k*(standardNormalization a b j*
        (shiftedPolynomial a b j).eval (shiftedRoots a b ha hb (N+1) k)))=
        standardNormalization a b j*standardGaussMap a b ha hb N (shiftedPolynomial a b j) := by
      simp only [standardGaussMap,LinearMap.coe_mk,AddHom.coe_mk,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he'] at h
    exact (mul_eq_zero.mp h).resolve_left (standardNormalization_pos ha hb j).ne'

/-- The normalized continuous integral of each basis polynomial is the
same zero/one value. All weighted integrals were proved convergent earlier.
Article: jacobi, Section 5.5, before Theorem 5.4.
Source: classical Gaussian quadrature, exact through degree 2n-1; NIST DLMF Section 3.5.
-/
theorem standardGauss_continuous_basis {a b : ℝ} (ha : -1<a) (hb : -1<b) (j : ℕ) :
    (jacobiNorm a b 0)⁻¹*weightedIntegralMap a b ha hb 0 (shiftedPolynomial a b j)=
      if j=0 then 1 else 0 := by
  rw [weightedIntegralMap_pair]
  by_cases hj : j=0
  · subst j
    simp [(jacobiNorm_pos ha hb 0).ne']
  · simp [hj,Ne.symm hj]

/-- Gaussian and normalized continuous integration agree on every
polynomial of degree below the number of actual nodes.
Article: jacobi, Section 5.5, before Theorem 5.4.
Source: classical Gaussian quadrature, exact through degree 2n-1; NIST DLMF Section 3.5.
-/
theorem standardGauss_exact_low {a b : ℝ} (ha : -1<a) (hb : -1<b) {N : ℕ}
    {p : ℝ[X]} (hp : p.natDegree < N+1) :
    standardGaussMap a b ha hb N p=(jacobiNorm a b 0)⁻¹*weightedIntegralMap a b ha hb 0 p := by
  let F := standardGaussMap a b ha hb N-(jacobiNorm a b 0)⁻¹ • weightedIntegralMap a b ha hb 0
  let S := shiftedSequence a b ha hb
  have hspan : p∈Submodule.span ℝ (S '' Iio (N+1)) := by
    rw [S.span_degreeLT (fun j _ => isUnit_iff_ne_zero.mpr
      (leadingCoeff_ne_zero.mpr (shiftedPolynomial_ne_zero ha hb j)))]
    rw [Polynomial.mem_degreeLT]
    by_cases hp0 : p=0
    · rw [hp0,degree_zero]; exact WithBot.bot_lt_coe _
    · exact (natDegree_lt_iff_degree_lt hp0).mp hp
  have hker : Submodule.span ℝ (S '' Iio (N+1))≤LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    change standardGaussMap a b ha hb N (shiftedPolynomial a b j)-
      (jacobiNorm a b 0)⁻¹*weightedIntegralMap a b ha hb 0 (shiftedPolynomial a b j)=0
    rw [standardGaussMap_basis ha hb hj,standardGauss_continuous_basis,sub_self]
  exact sub_eq_zero.mp (hker hspan)

/-- The spectral Gaussian rule is exact through degree 2N+1 for its N+1
actual nodes. Monic polynomial division proves the full Gaussian order,
not merely interpolation at the support points.
Article: jacobi, Section 5.5, before Theorem 5.4.
Source: classical Gaussian quadrature, exact through degree 2n-1; NIST DLMF Section 3.5.
-/
theorem standardGauss_exact {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ)
    {p : ℝ[X]} (hp : p.natDegree < 2*(N+1)) :
    standardGaussMap a b ha hb N p=(jacobiNorm a b 0)⁻¹*weightedIntegralMap a b ha hb 0 p := by
  let P := shiftedPolynomial a b (N+1)
  have hP : P≠0 := shiftedPolynomial_ne_zero ha hb (N+1)
  have hc : P.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr hP
  let g := P*C P.leadingCoeff⁻¹
  have hgm : g.Monic := monic_mul_C_of_leadingCoeff_mul_eq_one (mul_inv_cancel₀ hc)
  have hgn : g.natDegree=N+1 := by
    dsimp only [g]
    rw [natDegree_mul_C (inv_ne_zero hc)]
    exact shiftedPolynomial_natDegree ha hb (N+1)
  let q := p /ₘ g
  let r := p %ₘ g
  have hq : q.natDegree < N+1 := by
    change (p /ₘ g).natDegree < N+1
    rw [natDegree_divByMonic p hgm,hgn]
    omega
  have hr : r.natDegree < N+1 := by
    by_cases hr0 : r=0
    · rw [hr0,natDegree_zero]
      omega
    · have h := natDegree_lt_natDegree hr0 (degree_modByMonic_lt p hgm)
      rwa [hgn] at h
  have hroot (k : Fin (N+1)) : P.eval (shiftedRoots a b ha hb (N+1) k)=0 :=
    (mem_roots hP).mp (shiftedRoots_properties ha hb k).1
  have hd : standardGaussMap a b ha hb N (g*q)=0 := by
    simp only [standardGaussMap,LinearMap.coe_mk,AddHom.coe_mk,eval_mul,g,hroot,
      zero_mul,mul_zero,Finset.sum_const_zero]
  have hi : weightedIntegralMap a b ha hb 0 (g*q)=0 := by
    have he : weightedIntegralMap a b ha hb 0 (g*q)=
        P.leadingCoeff⁻¹*weightedIntegralMap a b ha hb (N+1) q := by
      change (∫ t in (0:ℝ)..1,weight a b t*((shiftedPolynomial a b 0).eval t*(g*q).eval t))=
        P.leadingCoeff⁻¹*(∫ t in (0:ℝ)..1,weight a b t*((shiftedPolynomial a b (N+1)).eval t*q.eval t))
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [shiftedPolynomial_initial,eval_one,one_mul,eval_mul,eval_C,g]
      ring
    rw [he]
    have ho : weightedIntegralMap a b ha hb (N+1) q=0 :=
      shiftedPolynomial_orthogonal_lower ha hb hq
    rw [ho,mul_zero]
  let F := standardGaussMap a b ha hb N-(jacobiNorm a b 0)⁻¹ • weightedIntegralMap a b ha hb 0
  have hlow : F r=0 := sub_eq_zero.mpr (standardGauss_exact_low ha hb hr)
  have hhigh : F (g*q)=0 := by simp only [F,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,hd,hi,mul_zero,sub_self]
  have he := congrArg F (modByMonic_add_div p g)
  change F (r+g*q)=F p at he
  rw [map_add,hlow,hhigh,zero_add] at he
  exact sub_eq_zero.mp he.symm

end
end jacobi.Jacobi
