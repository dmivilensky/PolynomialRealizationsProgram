import jacobi.Counterexample.LaguerreAttainment
import jacobi.Laguerre.Matrix

/-!
Article: jacobi, Proposition 6.1.
The attaining chain's characteristic polynomial equals the printed
n!/H_n^n*L_n^(1/2)(H_n*(1-x)). Thus the finite minimum and its limit
hold on precisely the source polynomial fibre, with no identification
hypothesis. Every root of this original polynomial lies in (-1,1).
Use: laguerre_polynomial_minimum and laguerre_polynomial_minimum_limit quantify over exactly this original polynomial fibre.
-/
namespace jacobi.Counterexample
noncomputable section
open Polynomial Matrix Set Filter jacobi.Finite
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal source Laguerre counterexample polynomial in its original monic normalization.
Use: laguerre_polynomial_minimum and laguerre_polynomial_minimum_limit quantify over exactly this original polynomial fibre.
Article: jacobi, Proposition 6.1.
-/
def laguerrePolynomial (theta:ℝ) (N:ℕ) : Polynomial ℝ :=
  C ((N.factorial:ℝ)/(laguerreScale theta N)^N)*
    (jacobi.Laguerre.classical (1/2) N).comp (C (laguerreScale theta N)*(1-X))

/-- The actual attaining chain's entire characteristic polynomial is exactly the source's original classical Laguerre polynomial.
Use: all finite-fibre and minimum conclusions are transferred to the literal printed p_n^L, including its complete finite spectrum.
Article: jacobi, Proposition 6.1.
Proof: the exact affine characteristic identity and the actual
classical Laguerre determinant formula have signs (-1)^n twice.
They cancel to one, leaving precisely the printed n!/H_n^n factor. -/
theorem laguerreChain_charpoly {theta:ℝ} (ht:0 < theta) (N:ℕ) :
    (laguerreChain theta N).matrix.charpoly=laguerrePolynomial theta N := by
  -- Polynomial equality is checked at every real argument, retaining all finite degrees and leading coefficients.
  apply Polynomial.funext
  intro x
  rw [laguerreChain,constantDriftChain_charpoly (laguerreDiagonal (1/2)) laguerreLower
    (by norm_num : (0:ℝ)<(1/2)+1) (laguerreScale_pos ht N)
    (fun i _=>laguerreDiagonal_pos (by norm_num) i)
    (fun _ hi _=>laguerreLower_pos hi)
    (fun i _=>laguerre_factor_drift (by norm_num) i),
    jacobi.Laguerre.characteristic_classical (by norm_num : (-1:ℝ)<1/2)]
  simp only [laguerrePolynomial,eval_mul,eval_C,eval_comp,eval_sub,eval_one,eval_X]
  have hs:(-1:ℝ)^N*(-1:ℝ)^N=1 := by
    rw [← mul_pow,neg_one_mul,neg_neg,one_pow]
  rw [div_pow]
  have hc:(-1:ℝ)^N/(laguerreScale theta N)^N*((-1:ℝ)^N*(N.factorial:ℝ))=
      (N.factorial:ℝ)/(laguerreScale theta N)^N := by
    calc
      _ = ((-1:ℝ)^N*(-1:ℝ)^N)*(N.factorial:ℝ)/(laguerreScale theta N)^N := by ring
      _ = _ := by rw [hs,one_mul]
  rw [← mul_assoc,hc]

/-- Every real root of the literal source Laguerre counterexample polynomial is strictly inside (-1,1).
Use: the complete polynomial fibre in laguerre_polynomial_minimum is admissible for the original terminal-realization problem.
Article: jacobi, Proposition 6.1.
Proof: the original polynomial is exactly the genuine attaining
chain's characteristic polynomial, whose spectral window has already
been proved from the strict original Laguerre eigenvalue bound. -/
theorem laguerre_polynomial_root_interval {theta:ℝ} (ht:0 < theta) (htop:theta≤1/4)
    (N:ℕ) {x:ℝ} (hx:(laguerrePolynomial theta N).eval x=0) : x∈Ioo (-1:ℝ) 1 := by
  apply laguerre_counterexample_admissible ht htop N
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,laguerreChain_charpoly ht]
  exact hx

/-- The source's literal Laguerre polynomial fibre has its exact attained finite minimum.
Use: laguerre_polynomial_infimum and laguerre_polynomial_minimum_limit concern all original positive-coupling realizations of p_n^L.
Article: jacobi, Proposition 6.1.
Proof: replace the entire characteristic polynomial in the actual
complete-fibre attainment theorem by its proved exact source identity.
No candidate, spectrum or normalization premise remains unproved. -/
theorem laguerre_polynomial_minimum {theta:ℝ} (ht:0 < theta) {N:ℕ} (hN:0 < N) :
    InFiber (laguerreChain theta N) (laguerrePolynomial theta N) ∧
      (laguerreChain theta N).energy=(N:ℝ)*(laguerreScale theta N)^2/(3/2)^2 ∧
      ∀J:chebyshev2.Jacobi N,InFiber J (laguerrePolynomial theta N)→
        (N:ℝ)*(laguerreScale theta N)^2/(3/2)^2≤J.energy := by
  simpa only [laguerreChain_charpoly ht] using laguerre_counterexample_minimum ht hN

/-- The actual ordinary real infimum over the source's full Laguerre polynomial fibre equals its genuinely attained minimum.
Use: laguerre_polynomial_minimum_limit has exactly the printed real min/inf formulation, without a restricted competitor set or an extended-value convention.
Article: jacobi, Proposition 6.1.
Proof: every actual energy is nonnegative. The proved attaining
chain supplies a genuine member and the exact lower bound for every
competitor, giving both sides of the ordinary conditional infimum. -/
theorem laguerre_polynomial_infimum {theta:ℝ} (ht:0 < theta) {N:ℕ} (hN:0 < N) :
    sInf ((fun J:chebyshev2.Jacobi N=>J.energy) ''
      {J | InFiber J (laguerrePolynomial theta N)})=(laguerreChain theta N).energy := by
  -- The set is genuinely nonempty and bounded below before its real infimum is used.
  have hm:=laguerre_polynomial_minimum ht hN
  have hmem:(laguerreChain theta N).energy∈
      ((fun J:chebyshev2.Jacobi N=>J.energy) '' {J | InFiber J (laguerrePolynomial theta N)}) :=
    ⟨laguerreChain theta N,hm.1,rfl⟩
  apply le_antisymm
  · apply csInf_le ?_ hmem
    refine ⟨0,?_⟩
    rintro E ⟨J,_,rfl⟩
    exact Finset.sum_nonneg (fun i _=>sq_nonneg (J.green i i))
  · apply le_csInf ⟨_,hmem⟩
    rintro E ⟨J,hJ,rfl⟩
    rw [hm.2.1]
    exact hm.2.2 J hJ

/-- The full original Laguerre polynomial-fibre minima have exactly the printed asymptotic constant 1/(9*theta^2).
Use: this is the complete Laguerre energy-limit assertion in Proposition 6.1, paired with the separate original edge-spectrum limit.
Article: jacobi, Proposition 6.1.
Proof: each original real infimum is the proved attained original
chain energy. Substitute this identity in the actual cubic-scale
energy limit, with its original finite dimensions unchanged. -/
theorem laguerre_polynomial_minimum_limit {theta:ℝ} (ht:0 < theta) :
    Tendsto (fun n:ℕ=>
      sInf ((fun J:chebyshev2.Jacobi (n+1)=>J.energy) ''
        {J | InFiber J (laguerrePolynomial theta (n+1))})/((n:ℝ)+1)^3)
      atTop (𝓝 (1/(9*theta^2))) := by
  simp_rw [laguerre_polynomial_infimum ht (Nat.succ_pos _)]
  exact laguerre_minimum_limit ht

end
end jacobi.Counterexample
