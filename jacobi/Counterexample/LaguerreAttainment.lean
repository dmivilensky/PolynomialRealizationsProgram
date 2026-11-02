import jacobi.Counterexample.LaguerreSpectrum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Article: jacobi, Proposition 6.1.
The printed scale H_n makes every genuine finite attaining chain
admissible. Its exact full-fibre minimum has the printed limit
1/(9*theta^2). Polynomial identification and convergence of the whole
edge spectrum are separate assertions, not premises of these results.
Use: laguerre_counterexample_admissible and laguerre_minimum_limit use exactly the matrix family in Proposition 6.1.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix Set Filter jacobi.Finite
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The source's literal Laguerre affine scale.
Use: laguerre_counterexample_admissible and laguerre_minimum_limit use exactly the matrix family in Proposition 6.1.
Article: jacobi, Proposition 6.1.
-/
def laguerreScale (theta:ℝ) (N:ℕ) : ℝ := (2*(N:ℝ)+3/2)/(4*theta)

/-- The actual positive-coupling constant-diagonal attaining Laguerre chain at the source scale.
Use: laguerre_counterexample_minimum and laguerre_minimum_limit quantify over its complete characteristic-polynomial fibre.
Article: jacobi, Proposition 6.1.
-/
def laguerreChain (theta:ℝ) (N:ℕ) : chebyshev2.Jacobi N :=
  constantDriftChain (laguerreDiagonal (1/2)) laguerreLower N (laguerreScale theta N)

/-- The original scale is positive for every source dimension.
Use: the genuine finite optimizer and its actual resolvent never require an extra scale-sign hypothesis.
Article: jacobi, Proposition 6.1.
Proof: both the printed numerator and denominator are positive. -/
theorem laguerreScale_pos {theta:ℝ} (ht:0<theta) (N:ℕ) : 0<laguerreScale theta N := by
  unfold laguerreScale
  positivity

/-- Every genuine attaining Laguerre chain has its entire actual spectrum strictly inside (-1,1).
Use: the full-fibre minimum in laguerre_counterexample_minimum is attained by an admissible chain of the original problem.
Article: jacobi, Proposition 6.1.
Proof: the proved strict Laguerre bound is 4*n+3. The literal source
scale satisfies 4*n+3<=2*H_n. The already proved exact affine spectral
identity therefore places every original node strictly in (-1,1). -/
theorem laguerre_counterexample_admissible {theta:ℝ} (ht:0<theta) (htop:theta≤1/4)
    (N:ℕ) {x:ℝ} (hx:x∈spectrum ℝ (laguerreChain theta N).matrix) :
    x∈Ioo (-1:ℝ) 1 := by
  -- Both strict endpoint exclusions follow from the unchanged finite matrix, not its limiting spectrum.
  apply constantDriftChain_spectrum_interval (laguerreDiagonal (1/2)) laguerreLower
    (by norm_num : (0:ℝ)<(1/2)+1) (laguerreScale_pos ht N)
    (fun i _=>laguerreDiagonal_pos (by norm_num) i)
    (fun _ hi _=>laguerreLower_pos hi)
    (fun i _=>laguerre_factor_drift (by norm_num) i) ?_ hx
  intro y hy
  have hu := laguerre_spectrum_upper (by norm_num : (-1:ℝ)<1/2) hy
  have hH:4*(N:ℝ)+3≤2*laguerreScale theta N := by
    unfold laguerreScale
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0<4*theta)).mpr
    have hh := mul_le_mul_of_nonneg_left htop (by positivity : 0≤4*(4*(N:ℝ)+3))
    nlinarith
  linarith

/-- The printed Laguerre matrix family attains its exact minimum over the complete original finite isospectral fibre.
Use: laguerre_minimum_limit obtains the actual minimum limit, rather than an upper candidate estimate or a symmetry-restricted infimum.
Article: jacobi, Proposition 6.1.
Proof: the fully proved literal Laguerre factor theorem applies with
a=1/2 and the actual positive source scale. All factor and inverse
identities have already been established for the original finite matrices. -/
theorem laguerre_counterexample_minimum {theta:ℝ} (ht:0<theta) {N:ℕ} (hN:0<N) :
    InFiber (laguerreChain theta N) (laguerreChain theta N).matrix.charpoly ∧
      (laguerreChain theta N).energy=(N:ℝ)*(laguerreScale theta N)^2/(3/2)^2 ∧
      ∀J:chebyshev2.Jacobi N,
        InFiber J (laguerreChain theta N).matrix.charpoly→
          (N:ℝ)*(laguerreScale theta N)^2/(3/2)^2≤J.energy := by
  simpa only [laguerreChain,show (1/2:ℝ)+1=3/2 by ring] using
    laguerre_chain_minimum hN (by norm_num : (-1:ℝ)<1/2) (laguerreScale_pos ht N)

/-- The actual Laguerre scale divided by its genuine matrix dimension has limit 1/(2*theta).
Use: laguerre_minimum_limit takes the exact finite minimum to the printed cubic energy scale.
Article: jacobi, Proposition 6.1.
Proof: H_n/n=(2+(3/2)/n)/(4*theta), and the reciprocal dimension tends to zero. -/
theorem laguerre_scale_limit {theta:ℝ} (ht:0<theta) :
    Tendsto (fun n:ℕ=>laguerreScale theta (n+1)/((n:ℝ)+1)) atTop (𝓝 (1/(2*theta))) := by
  -- Separate the vanishing reciprocal dimension from the constant leading term two.
  have hn:Tendsto (fun n:ℕ=>(n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hz:Tendsto (fun n:ℕ=>(3/2:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have h := (hz.const_add 2).div_const (4*theta)
  have hv:(2+(0:ℝ))/(4*theta)=1/(2*theta) := by field_simp; norm_num
  rw [hv] at h
  apply (tendsto_congr ?_).mpr h
  intro n
  unfold laguerreScale
  push_cast
  field_simp

/-- The exact complete-fibre minimum of the genuine Laguerre attaining family has the printed limit 1/(9*theta^2).
Use: supplies the second energy limit in Proposition 6.1; laguerre_counterexample_minimum separately proves that every term is the full original minimum.
Article: jacobi, Proposition 6.1.
Proof: divide the proved exact finite attained minimum by the cube
of its original dimension. It is (4/9)*(H_n/n)^2. The established
scale limit gives exactly the printed positive constant. -/
theorem laguerre_minimum_limit {theta:ℝ} (ht:0<theta) :
    Tendsto (fun n:ℕ=>(laguerreChain theta (n+1)).energy/((n:ℝ)+1)^3)
      atTop (𝓝 (1/(9*theta^2))) := by
  -- The same chain realizes the minimum in every dimension, so no interchange of infimum and limit occurs.
  have h := ((laguerre_scale_limit ht).pow 2).const_mul (4/9:ℝ)
  have hv:(4/9:ℝ)*(1/(2*theta))^2=1/(9*theta^2) := by field_simp; ring
  rw [hv] at h
  apply (tendsto_congr ?_).mpr h
  intro n
  rw [(laguerre_counterexample_minimum ht (Nat.succ_pos n)).2.1]
  push_cast
  field_simp
  ring

/-- The actual unswapped Laguerre inverse has trace n/(a+1), for every a>-1.
Use: the Laguerre edge l1 limit uses this exact total resolvent mass after proving convergence of individual ordered zeros.
Article: jacobi, Proposition 6.1.
Proof: the inverse-product identity and cyclicity of the genuine
finite trace transfer the trace to the Cholesky swap. Every actual
swapped inverse diagonal entry is the proved value 1/(a+1). -/
theorem laguerre_inverse_trace {a:ℝ} (ha:-1<a) (N:ℕ) :
    ((bidiagonal (laguerreDiagonal a) laguerreLower N*
      (bidiagonal (laguerreDiagonal a) laguerreLower N)ᵀ)⁻¹).trace=(N:ℝ)/(a+1) := by
  -- Cyclicity changes neither the original spectrum nor its complete finite multiplicity.
  let B := bidiagonal (laguerreDiagonal a) laguerreLower N
  have he:((B*Bᵀ)⁻¹).trace=((swappedGram (laguerreDiagonal a) laguerreLower N)⁻¹).trace := by
    rw [Matrix.mul_inv_rev,Matrix.trace_mul_comm]
    rw [swappedGram,Matrix.mul_inv_rev]
  rw [he]
  unfold Matrix.trace
  simp only [Matrix.diag_apply,swapped_inverse_diagonal (laguerreDiagonal a) laguerreLower
    (by linarith : 0<a+1) (by simp [laguerreLower])
    (fun i _=>laguerre_factor_drift ha i),Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,div_eq_mul_inv,one_mul]

end
end jacobi.Counterexample
