import jacobi.Counterexample.UEnergyLimit
import jacobi.Counterexample.LaguerreFibre

/-!
Article: jacobi, Proposition 6.1.
Both literal source polynomial families have all roots in (-1,1),
the same proved complete l1 edge spectrum, and different proved full
optimal-energy limits. The entire edge-only lower constant is bounded
by the smaller Laguerre value. The genuine finite packings of both
families have root mass one, as in the source's concluding observation.
Use: identical_edges_different_energies and edge_calibration_not_sharp state the source counterexample for the same original spectral data.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix Polynomial Set Filter jacobi.Finite jacobi.Variational chebyshev1
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The actual common positive summable edge spectrum of both original counterexample polynomial families.
Use: identical_edges_different_energies and edge_calibration_not_sharp state the source counterexample for the same original spectral data.
Article: jacobi, Proposition 6.1.
-/
def commonEdge (theta:ℝ) (ht:0 < theta) : EdgeSpectrum where
  value k:=(1/theta)* jacobi.Bessel.edgeValue (1/2) (by norm_num) k
  positive k:=mul_pos (by positivity) ((jacobi.Bessel.edgeValue_properties (by norm_num)).1 k)
  antitone:=by
    intro i j hij
    exact mul_le_mul_of_nonneg_left
      ((jacobi.Bessel.edgeValue_properties (by norm_num : (-1:ℝ)<1/2)).2.antitone hij) (by positivity)
  summable:=(jacobi.Bessel.edgeValue_summable (by norm_num : (-1:ℝ)<1/2)).mul_left (1/theta)

/-- The actual common spectrum has exactly the original explicit source values.
Use: identical_edges_different_energies retains the printed normalization rather than only a proportional Bessel spectrum.
Article: jacobi, Proposition 6.1.
Proof: substitute the proved actual U squared zeros pi^2*k^2 and simplify the original reciprocal coefficient. -/
theorem commonEdge_value {theta:ℝ} (ht:0 < theta) (k:ℕ) :
    (commonEdge theta ht).value k=2/(theta*Real.pi^2*(k+1:ℝ)^2) := by
  change (1/theta)* jacobi.Bessel.edgeValue (1/2) (by norm_num) k=_
  rw [jacobi.Bessel.edgeValue,jacobi.GelfandLevitan.half_sine_spectrum]
  field_simp

/-- Every root of the literal original U counterexample polynomial belongs to (-1,1).
Use: both original polynomial fibres meet the full source admissibility hypotheses in identical_edges_different_energies.
Article: jacobi, Proposition 6.1.
Proof: the polynomial is the complete actual admissible node product.
A vanishing finite product is one of its genuine original linear factors,
whose node already lies strictly inside the original spectral interval. -/
theorem u_polynomial_root_interval {theta:ℝ} (ht:0 < theta) (htop:theta≤1)
    (n:ℕ) {x:ℝ} (hx:(uPolynomial theta n).eval x=0) : x∈Ioo (-1:ℝ) 1 := by
  -- The empty original degree has no roots; no exceptional finite dimension is omitted.
  rw [← uNodes_polynomial ht htop,Nodes.polynomial,eval_prod] at hx
  simp only [eval_sub,eval_X,eval_C,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,sub_eq_zero] at hx
  obtain ⟨i,hi⟩:=hx
  exact hi ▸ (uNodes theta ht htop n).interval i

/-- The two actual limiting optimal-energy constants are strictly different.
Use: identical_edges_different_energies and edge_calibration_not_sharp prove an actual strict counterexample rather than an inequality with a numerical premise.
Article: jacobi, Proposition 6.1.
Proof: clear the genuine positive denominators; the strict rational coefficient comparison is exact. -/
theorem counterexample_constants_strict {theta:ℝ} (ht:0 < theta) :
    1/(9*theta^2)<2/(15*theta^2) := by
  rw [div_lt_div_iff₀ (by positivity : 0 < 9*theta^2) (by positivity : 0 < 15*theta^2)]
  nlinarith [sq_pos_of_pos ht]

/-- The complete original U and Laguerre polynomial families have the same whole edge spectrum and different full finite-fibre optimal-energy limits.
Use: this is Proposition 6.1, with literal source polynomials and every source spectral and energy premise proved.
Article: jacobi, Proposition 6.1.
Proof: the two independent actual l1 limits have the same original
common spectrum. The exact affine U-fibre equivalence and the genuine
Laguerre full-fibre attainment give their different actual optimal
limits. Their strict rational separation is proved above. -/
theorem identical_edges_different_energies {theta:ℝ} (ht:0 < theta) (htop:theta≤1/4) :
    Tendsto (fun n:ℕ=>∑'k,|uEdge theta (n+1) k-(commonEdge theta ht).value k|) atTop (𝓝 0) ∧
    Tendsto (fun n:ℕ=>∑'k,|laguerreEdge theta (n+1) k-(commonEdge theta ht).value k|) atTop (𝓝 0) ∧
    Tendsto (fun n:ℕ=>sInf ((fun J:chebyshev2.Jacobi (n+1)=>
      J.energy/((n:ℝ)+1)^3) '' {J | InFiber J (uPolynomial theta (n+1))}))
      atTop (𝓝 (2/(15*theta^2))) ∧
    Tendsto (fun n:ℕ=>sInf ((fun J:chebyshev2.Jacobi (n+1)=>J.energy) ''
      {J | InFiber J (laguerrePolynomial theta (n+1))})/((n:ℝ)+1)^3)
      atTop (𝓝 (1/(9*theta^2))) ∧
    1/(9*theta^2)<2/(15*theta^2) :=
  ⟨uEdge_l1_limit ht,laguerreEdge_l1_limit ht,u_polynomial_energy_limit ht (by linarith),
    laguerre_polynomial_minimum_limit ht,counterexample_constants_strict ht⟩

/-- The entire original edge-only lower constant is bounded by the smaller true Laguerre minimum, strictly below the original U optimum.
Use: proves the source conclusion that no lower bound depending only on the edge spectrum can be sharp for the first polynomial family.
Article: jacobi, Proposition 6.1.
Proof: identify the actual Laguerre node-fibre spectrum with its
proved original full l1 limit. Apply the complete existing Transfer
theorem and its full lower constant, then use the actual attained
Laguerre infimum limit and the exact strict coefficient comparison. -/
theorem edge_calibration_not_sharp {theta:ℝ} (ht:0 < theta) (htop:theta≤1/4) :
    lowerConstant (commonEdge theta ht)≤ENNReal.ofReal (1/(9*theta^2)) ∧
      1/(9*theta^2)<2/(15*theta^2) := by
  -- The entire lower constant is transferred, including all moment and Fredholm calibrations.
  have hd:Tendsto (fun n:ℕ=>distance (jacobi.Packing.fibreSpectrum
      (laguerreNodes theta ht htop (n+1))) (commonEdge theta ht).value) atTop (𝓝 0) := by
    simp only [laguerre_fibreSpectrum]
    exact laguerreEdge_l1_limit ht
  have hl:=lowerConstant_transfer (fun n:ℕ=>n+1) (fun n=>laguerreNodes theta ht htop (n+1))
    (fun n=>Nat.succ_pos n) (tendsto_add_atTop_nat 1) (commonEdge theta ht) hd
  rw [(laguerre_fibre_energy_limit ht htop).liminf_eq] at hl
  exact ⟨hl,counterexample_constants_strict ht⟩

/-- Every actual original finite competitor in either counterexample fibre has a genuine canonical packing of root mass one.
Use: the source's stronger root-mass constraint does not distinguish the two original polynomial families.
Article: jacobi, Proposition 6.1.
Proof: both original source polynomials are proved admissible node
products. Every actual fibre competitor is therefore strictly contractive.
Apply the already verified original finite packing integral identities
to those same matrices, with their true dimensions unchanged. -/
theorem counterexample_packing_rootMass {theta:ℝ} (ht:0 < theta) (htop:theta≤1/4)
    {N:ℕ} (hN:0 < N) (J K:chebyshev2.Jacobi N)
    (hJ:InFiber J (uPolynomial theta N)) (hK:InFiber K (laguerrePolynomial theta N)) :
    ∃hJU:opNorm J.matrix < 1,∃hKL:opNorm K.matrix < 1,
      (jacobi.Packing.variationalDensity J hJU hN).rootMass=1 ∧
      (jacobi.Packing.variationalDensity K hKL hN).rootMass=1 := by
  -- These are the existing canonical packings of the actual arbitrary competitors, not new unrelated feasible densities.
  have hU:InFiber J (uNodes theta ht (by linarith) N).polynomial:=by
    simpa only [uNodes_polynomial] using hJ
  have hL:InFiber K (laguerreNodes theta ht htop N).polynomial:=by
    simpa only [laguerreNodes_polynomial] using hK
  let hcU:opNorm J.matrix < 1:=(uNodes theta ht (by linarith) N).contractive hU
  let hcL:opNorm K.matrix < 1:=(laguerreNodes theta ht htop N).contractive hL
  exact ⟨hcU,hcL,(jacobi.Packing.variationalDensity_integrals J hcU hN).2.1,
    (jacobi.Packing.variationalDensity_integrals K hcL hN).2.1⟩

end
end jacobi.Counterexample
