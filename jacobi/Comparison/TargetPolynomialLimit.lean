import jacobi.Comparison.EigenvectorRowApproximation
import jacobi.Comparison.CholeskyNormalization
import jacobi.GelfandLevitan.RealTransformationIntegral

/-!
Article: jacobi, Proposition C.3.
The genuine original target polynomials have their full transformed
edge limit along arbitrary cofinal moving physical half-chain indices.
The same actual u from Proposition C.2 is identified by its proved integral
formula, and the original Gamma amplitude is retained exactly.
Use: targetPolynomial_edge_limit and the positive target probability limit give the actual finite eigenvector limit with its true sign.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter Polynomial MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Support jacobi.Finite
open scoped Topology
attribute [local irreducible] transformationKernel realSolution

/-- The actual degree-normalized target polynomial at the original
fixed target edge, defined using its genuine Schur-normalized family.
Use: targetPolynomial_edge_limit and the positive target probability
limit give the actual finite eigenvector limit with its true sign.
Article: jacobi, Proposition C.3.
-/
def targetEdgeValue (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) (i:Fin (n+1)) : ℝ :=
  (n:ℝ)^(-gamma a)*(targetPolynomial a b ha hb n i).eval
    (cos (jacobi.Jacobi.finiteAngleAt a b ha hb (n+1) k))

/-- The actual normalized target value obeys the same exact genuine
Schur row formula as its unscaled original polynomial.
Use: targetPolynomial_edge_limit combines the three proved original
limits without an additional transformation identity assumption.
Article: jacobi, Proposition C.3.
Proof: evaluate the established actual polynomial identity and move
the original scalar degree power through its genuine finite row sum. -/
theorem targetEdgeValue_schur (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) (i:Fin (n+1)) :
    targetEdgeValue a b ha hb n k i=(sqrt (rowNormalization a b ha hb n i))⁻¹*
      (supportEdgeValue a b ha hb n k i+
        ∑j:Fin i.val,rowCoefficient a b ha hb n i j*supportEdgeValue a b ha hb n k (Gram.before i j)) := by
  -- The same original degree power multiplies every actual polynomial in the row.
  let x := cos (jacobi.Jacobi.finiteAngleAt a b ha hb (n+1) k)
  have hs : (∑j:Fin i.val,rowCoefficient a b ha hb n i j*supportEdgeValue a b ha hb n k (Gram.before i j))=
      (n:ℝ)^(-gamma a)*(∑j:Fin i.val,rowCoefficient a b ha hb n i j*
        (supportPolynomial a b ha hb n (Gram.before i j)).eval x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [supportEdgeValue,x]
    ring
  rw [hs]
  unfold targetEdgeValue supportEdgeValue
  rw [targetPolynomial_schur]
  simp only [Polynomial.eval_smul,smul_eq_mul,Polynomial.eval_add,Polynomial.eval_finsetSum]
  dsimp [x]
  ring

/-- The original reference edge value and genuine transformation
integral sum to the same actual transformed solution with the exact
original Gamma amplitude.
Use: targetPolynomial_edge_limit identifies its actual limiting function
with Proposition C.2's u rather than leaving an integral candidate.
Article: jacobi, Proposition C.3.
Proof: the established actual real transformation integral is multiplied
by the original amplitude. Move that constant through its true interval
integral and use scalar commutativity in the genuine kernel product. -/
theorem referenceEdgeProfile_transformed (a b:ℝ) (ha:-1<a) (k:ℕ) (t:HalfInterval) :
    referenceEdgeProfile a b ha k t+
      (∫s in (0:ℝ)..(t:ℝ),edgeTransformationProduct a b a ha ha k (t,halfParameterClamp s))=
      (topConstant a b*π^gamma a)*realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) t := by
  -- The positive original Gamma amplitude multiplies the same genuine transformation integral.
  rw [realTransformedSolution_integral,mul_add]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change transformationKernel a ha t (halfParameterClamp s)*
    ((topConstant a b*π^gamma a)*realSolution a (jacobi.Bessel.sigma a ha k) (halfParameterClamp s).val)=
    (topConstant a b*π^gamma a)*(transformationKernel a ha t (halfParameterClamp s)*
      realSolution a (jacobi.Bessel.sigma a ha k) (halfParameterClamp s).val)
  ring

/-- The true original target polynomial has its complete transformed
edge limit along every cofinal moving physical half-chain row.
Use: Appendix C.4 multiplies this actual limit by the
proved actual target probability scale; Theorems A and H use the
resulting genuine normalized eigenvectors.
Article: jacobi, Appendix C.4 (uniform eigenvector limits).
Proof: the genuine support edge value has its reference limit. The
actual Schur correction differs uniformly from the proved model-row
integral limit by a vanishing error. Its genuine positive normalization
tends to one. The established original real transformation formula
identifies their sum with the actual u of Proposition C.2. -/
theorem targetPolynomial_edge_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i:∀r:ℕ,Fin (ns r+1))
    (hi:∀ᶠr:ℕ in atTop,2*(i r).val≤ns r+1)
    {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/(ns r:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun r => targetEdgeValue a b ha hb (ns r) k (i r)) atTop
      (𝓝 ((topConstant a b*π^gamma a)*realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) ⟨t,ht⟩)) := by
  -- The actual finite row error vanishes before any limiting integral is substituted.
  have herr : Tendsto (fun r =>
      (∑j:Fin (i r).val,rowCoefficient a b ha hb (ns r) (i r) j*
        supportEdgeValue a b ha hb (ns r) k (Gram.before (i r) j))-
      eigenvectorModelRow a b ha hb (ns r) k (i r)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eigenvectorRow_uniform_approximation ha hb k ε hε
    filter_upwards [hns.eventually_ge_atTop N,hi] with r hr hir
    simpa only [Real.dist_eq,sub_zero] using hN (ns r) hr (i r) hir
  have hcorr := herr.add (eigenvectorModelRow_limit ha hb k ns hns i ht hit)
  simp only [sub_add_cancel,zero_add] at hcorr
  have hsupport := supportPolynomial_target_limit ha hb k ns hns i hi ht hit
  change Tendsto (fun r => supportEdgeValue a b ha hb (ns r) k (i r)) atTop
    (𝓝 (referenceEdgeProfile a b ha k ⟨t,ht⟩)) at hsupport
  have hnorm := rowNormalization_inverse_sqrt_tendsto ha hb ns hns i hi
  have hh := hnorm.mul (hsupport.add hcorr)
  rw [referenceEdgeProfile_transformed,one_mul] at hh
  simpa only [targetEdgeValue_schur] using hh

end
end jacobi.Comparison
