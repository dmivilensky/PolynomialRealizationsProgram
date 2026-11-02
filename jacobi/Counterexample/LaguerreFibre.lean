import jacobi.Counterexample.LaguerreEdge
import jacobi.Finite.PolynomialIdentification
import jacobi.Variational.LowerConstant

/-!
Article: jacobi, Proposition 6.1.
The literal source nodes form an admissible Nodes object whose full
polynomial is precisely p_n^L. The original complete-fibre infimum,
its entire edge sequence and its genuine attaining matrices are
identified with the common finite packing theory.
Use: laguerre_lowerConstant_bound applies the original full Transfer theorem to this very source family.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix Polynomial Set Filter jacobi.Finite jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The actual admissible complete source Laguerre node data.
Use: laguerre_lowerConstant_bound applies the original full Transfer theorem to this very source family.
Article: jacobi, Proposition 6.1.
-/
def laguerreNodes (theta:ℝ) (ht:0 < theta) (htop:theta≤1/4) (n:ℕ) : Nodes n where
  value:=laguerreNode theta n
  strictAnti:=laguerreNode_strictAnti ht n
  interval i:=laguerre_polynomial_root_interval ht htop n (laguerreNode_is_root ht n i)

/-- The common finite-fibre interface retains exactly the original classical Laguerre counterexample polynomial.
Use: laguerre_fibre_energy_limit and the common packing and Transfer results quantify over precisely the complete original source fibre.
Article: jacobi, Proposition 6.1.
Proof: all actual nodes are proved original roots. The exact actual
attaining chain characteristic identity proves original monicity and
degree. Complete monic node-product uniqueness gives the unchanged polynomial. -/
theorem laguerreNodes_polynomial {theta:ℝ} (ht:0 < theta) (htop:theta≤1/4) (n:ℕ) :
    (laguerreNodes theta ht htop n).polynomial=laguerrePolynomial theta n := by
  -- The source characteristic polynomial is identified before passing to a packing or limiting spectrum.
  apply Eq.symm
  apply Nodes.eq_polynomial
  · rw [← laguerreChain_charpoly ht]
    exact Matrix.charpoly_monic _
  · rw [← laguerreChain_charpoly ht,Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin]
  · exact laguerreNode_is_root ht n

/-- The actual common full-fibre spectrum is exactly the original Laguerre source scaled resolvent sequence.
Use: laguerre_lowerConstant_bound supplies the proved genuine l1 edge limit to the general Transfer theorem without a new spectrum-identification premise.
Article: jacobi, Proposition 6.1.
Proof: on every finite index the literal original node resolvent is
1/(n^2*(1-zeta)); past the dimension both genuine spectra are zero. -/
theorem laguerre_fibreSpectrum {theta:ℝ} (ht:0 < theta) (htop:theta≤1/4) (n:ℕ) :
    jacobi.Packing.fibreSpectrum (laguerreNodes theta ht htop n)=laguerreEdge theta n := by
  funext k
  unfold jacobi.Packing.fibreSpectrum laguerreEdge
  split_ifs
  · simp only [jacobi.Packing.nodeResolvent,laguerreNodes]
    field_simp
  · rfl

/-- The original common full-fibre infima of the Laguerre source family converge to the printed exact finite limit.
Use: laguerre_lowerConstant_bound compares every edge-only calibration with this genuine original full-fibre minimum limit.
Article: jacobi, Proposition 6.1.
Proof: the actual attaining matrix belongs to the full source fibre,
and every original competitor has at least its proved exact energy.
Both sides of the nonnegative infimum are therefore equal to its true
attaining cost. Apply the established actual cubic-scale energy limit. -/
theorem laguerre_fibre_energy_limit {theta:ℝ} (ht:0 < theta) (htop:theta≤1/4) :
    Tendsto (fun n:ℕ=>fibreEnergyInfimum (laguerreNodes theta ht htop (n+1)))
      atTop (𝓝 (ENNReal.ofReal (1/(9*theta^2)))) := by
  -- No selection of near-minimizers or extra numerical condition is used in this exact finite family.
  have he (n:ℕ) : fibreEnergyInfimum (laguerreNodes theta ht htop (n+1))=
      ENNReal.ofReal ((laguerreChain theta (n+1)).energy/((n:ℝ)+1)^3) := by
    have hm:=laguerre_polynomial_minimum ht (Nat.succ_pos n)
    rw [fibreEnergyInfimum,laguerreNodes_polynomial]
    apply le_antisymm
    · apply sInf_le
      refine ⟨laguerreChain theta (n+1),hm.1,?_⟩
      simp only [fibreCost,Nat.cast_add,Nat.cast_one]
    · apply le_sInf
      rintro E ⟨J,hJ,rfl⟩
      apply ENNReal.ofReal_le_ofReal
      simp only [Nat.cast_add,Nat.cast_one]
      have hh:=hm.2.2 J hJ
      rw [← hm.2.1] at hh
      exact div_le_div_of_nonneg_right hh (by positivity)
  simp_rw [he]
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (laguerre_minimum_limit ht)

end
end jacobi.Counterexample
