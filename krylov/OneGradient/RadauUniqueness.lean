import krylov.OneGradient.FiniteMomentUniqueness
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), uniqueness of the actual Radau endpoint rules.
Use: prove uniqueness among all genuine supported probability measures from
original moments and an actual prescribed endpoint node.
Source: classical nonnegative localizing polynomial and Lagrange interpolation;
all support and measure uniqueness conclusions are derived from real integrals.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial MeasureTheory jacobi.Finite krylov.LinearAlgebra krylov.Reference
open scoped BigOperators
variable {n : ℕ}

/-- A positive actual n+1-node rule containing a support endpoint is the unique
supported measure with its first 2n+1 moments.
Use: uniqueness is in the original full measure class, with no assumed finite support.
Article: main_krylov, s5:moment(b), principal endpoint representations.
Proof: the endpoint localizer times the squared actual cardinal polynomial
is nonnegative and has zero integral. Moment equality transfers its true zero
integral to the candidate measure, forcing support on the same actual nodes.
The reused cardinal-polynomial measure uniqueness then fixes every positive mass. -/
theorem radau_localizer_unique (M : DiscreteMeasure (n+1)) (j : Fin (n+1))
    (I : chebyshev1.SpectralInterval) (sigma : Measure ℝ) [IsProbabilityMeasure sigma]
    (hs : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (hm : ∀ k≤2*n+1,(∫ x,x^k ∂sigma)=discretePolynomialIntegral M (X^k))
    (R : ℝ[X]) (hdeg : R.natDegree≤1)
    (hpos : ∀ x∈Set.Icc I.mu I.L,0≤R.eval x)
    (hzero : ∀ x : ℝ,R.eval x=0 ↔ x=M.node j) :
    sigma=discreteAtomicMeasure M := by
  let p := spectralCardinalPolynomial M.node j
  let F := measurePolynomialIntegral sigma I hs
  let G := discretePolynomialIntegral M
  have hF (k : ℕ) (hk : k≤2*n+1) : F (X^k)=G (X^k) := by
    simpa only [F,measurePolynomialIntegral,LinearMap.coe_mk,AddHom.coe_mk,eval_pow,eval_X] using hm k hk
  have hpeq (q : ℝ[X]) (hq : q.natDegree≤2*n+1) : F q=G q :=
    polynomial_integrals_eq_of_moments F G _ hF q hq
  have hpdeg : p.natDegree=n := by
    simpa only [Nat.add_sub_cancel] using spectralCardinal_degree M.node j
  have hRdeg : (R*p^2).natDegree≤2*n+1 := by
    have hmul := Polynomial.natDegree_mul_le (p := R) (q := p^2)
    have hpow := Polynomial.natDegree_pow_le (p := p) (n := 2)
    omega
  have hGzero : G (R*p^2)=0 := by
    change (∑ i,M.weight i*(R*p^2).eval (M.node i))=0
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i=j
    · subst i
      rw [eval_mul,(hzero _).mpr rfl,zero_mul,mul_zero]
    · rw [eval_mul,eval_pow,spectralCardinal_other M.node j i hi]
      simp
  have hnonneg : 0≤ᵐ[sigma] (fun x => (R*p^2).eval x) := by
    filter_upwards [hs] with x hx
    rw [eval_mul,eval_pow]
    exact mul_nonneg (hpos x hx) (sq_nonneg _)
  have hae : (fun x => (R*p^2).eval x)=ᵐ[sigma] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg
      (polynomial_integrable_compact sigma I hs (R*p^2))).mp ((hpeq _ hRdeg).trans hGzero)
  have hnodes : ∀ᵐ x ∂sigma,x∈Finset.univ.image M.node := by
    filter_upwards [hae] with x hx
    change (R*p^2).eval x=0 at hx
    rw [eval_mul,eval_pow,mul_eq_zero] at hx
    rcases hx with hx|hx
    · exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,((hzero x).mp hx).symm⟩
    · have hp : p.eval x=0 := (sq_eq_zero_iff).mp hx
      change (spectralCardinalPolynomial M.node j).eval x=0 at hp
      rw [spectralCardinalPolynomial,eval_prod,Finset.prod_eq_zero_iff] at hp
      obtain ⟨i,_,hi⟩ := hp
      have he : x=M.node i := by simpa only [eval_sub,eval_X,eval_C,sub_eq_zero] using hi
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,he.symm⟩
  apply supported_atomic_unique M sigma hnodes
  intro q hq
  exact hpeq q (by omega)

/-- The actual lower-endpoint n+1-node Radau rule is uniquely determined among
all probability measures on the original interval by its first 2n+1 moments.
Use: lower principal representation uniqueness is a theorem about actual measures.
Article: main_krylov, s5:moment(b).
Proof: the actual linear localizer X-mu is nonnegative on the original support
and vanishes exactly at the prescribed actual endpoint node. -/
theorem lower_radau_unique (M : DiscreteMeasure (n+1)) (j : Fin (n+1))
    (I : chebyshev1.SpectralInterval) (hj : M.node j=I.mu)
    (sigma : Measure ℝ) [IsProbabilityMeasure sigma]
    (hs : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (hm : ∀ k≤2*n+1,(∫ x,x^k ∂sigma)=discretePolynomialIntegral M (X^k)) :
    sigma=discreteAtomicMeasure M := by
  apply radau_localizer_unique M j I sigma hs hm (X-C I.mu)
  · exact (natDegree_sub_le _ _).trans (by simp)
  · intro x hx
    simpa only [eval_sub,eval_X,eval_C] using sub_nonneg.mpr hx.1
  · intro x
    simp only [eval_sub,eval_X,eval_C,sub_eq_zero,hj]

/-- The actual upper-endpoint n+1-node Radau rule is uniquely determined among
all probability measures on the original interval by its first 2n+1 moments.
Use: upper principal representation uniqueness includes arbitrary non-atomic candidates.
Article: main_krylov, s5:moment(b).
Proof: use the genuine nonnegative localizer L-X with its sole actual endpoint root. -/
theorem upper_radau_unique (M : DiscreteMeasure (n+1)) (j : Fin (n+1))
    (I : chebyshev1.SpectralInterval) (hj : M.node j=I.L)
    (sigma : Measure ℝ) [IsProbabilityMeasure sigma]
    (hs : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (hm : ∀ k≤2*n+1,(∫ x,x^k ∂sigma)=discretePolynomialIntegral M (X^k)) :
    sigma=discreteAtomicMeasure M := by
  apply radau_localizer_unique M j I sigma hs hm (C I.L-X)
  · exact (natDegree_sub_le _ _).trans (by simp)
  · intro x hx
    simpa only [eval_sub,eval_X,eval_C] using sub_nonneg.mpr hx.2
  · intro x
    simp only [eval_sub,eval_X,eval_C,sub_eq_zero,hj,eq_comm]

/-- The actual endpoint rule uniqueness is invariant under the original
number-of-active-atoms identity.
Use: apply the genuine principal representation theorem to the actual physical
gradient measure without introducing an artificial relabelled measure.
Article: main_krylov, s5:moment(b).
Proof: transport the proved real atom count and apply the corresponding actual
lower or upper endpoint localizer uniqueness theorem. -/
theorem endpoint_radau_unique {N : ℕ} (M : DiscreteMeasure N) (hN : N=n+1)
    (I : chebyshev1.SpectralInterval)
    (hend : (∃ j,M.node j=I.mu) ∨ (∃ j,M.node j=I.L))
    (sigma : Measure ℝ) [IsProbabilityMeasure sigma]
    (hs : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (hm : ∀ k≤2*n+1,(∫ x,x^k ∂sigma)=discretePolynomialIntegral M (X^k)) :
    sigma=discreteAtomicMeasure M := by
  subst N
  rcases hend with ⟨j,hj⟩|⟨j,hj⟩
  · exact lower_radau_unique M j I hj sigma hs hm
  · exact upper_radau_unique M j I hj sigma hs hm

end
end krylov.OneGradient
