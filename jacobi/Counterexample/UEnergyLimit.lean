import jacobi.Counterexample.UFamily
import jacobi.Comparison.MainBounds

/-!
Article: jacobi, Proposition 6.1.
The existing complete Transfer lower bound and actual persymmetric
upper candidate force convergence of the entire sequence of genuine
finite U-fibre infima. The exact affine fibre equivalence then gives
the printed constant 2/(15*theta^2) on the literal source polynomial.
Use: u_fibre_energy_limit applies the exact finite positive affine bijection to recover the source's U counterexample family.
-/
namespace jacobi.Counterexample
noncomputable section
open Set Filter jacobi.Finite jacobi.Comparison jacobi.Variational jacobi.GelfandLevitan
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The entire sequence of actual full finite U-fibre optimal energies converges to two fifteenths.
Use: u_fibre_energy_limit applies the exact finite positive affine bijection to recover the source's U counterexample family.
Article: jacobi, Proposition 6.1.
Proof: the original full-fibre liminf equals two fifteenths by the
proved Transfer and exact Young calibration at U. Every actual finite
infimum is bounded by its original persymmetric candidate, whose
energy has the same genuine limit. Thus limsup and liminf coincide. -/
theorem u_base_energy_limit :
    Tendsto (fun n:ℕ=>fibreEnergyInfimum
      (jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) (n+1)))
      atTop (𝓝 (ENNReal.ofReal (2/15))) := by
  -- The upper comparison uses a genuine original competitor in every complete finite fibre.
  let ha:(-1:ℝ)<1/2:=by norm_num
  apply tendsto_of_le_liminf_of_limsup_le
  · change ENNReal.ofReal (2/15)≤jacobiOptimalEnergy (1/2) (1/2) ha ha
    rw [(jacobiOptimalEnergy_U ha ha).2]
  · have hc:=ENNReal.continuous_ofReal.continuousAt.tendsto.comp (target_energy_limit ha ha)
    rw [half_sine_persymmetricConstant] at hc
    have hb:∀n:ℕ,fibreEnergyInfimum (jacobi.Jacobi.nodes (1/2) (1/2) ha ha (n+1))≤
        ENNReal.ofReal ((targetChain (1/2) (1/2) ha ha n).energy/((n:ℝ)+1)^3) := by
      intro n
      apply sInf_le
      refine ⟨targetChain (1/2) (1/2) ha ha n,targetChain_inFiber (1/2) (1/2) ha ha n,?_⟩
      simp only [fibreCost,Nat.cast_add,Nat.cast_one]
    exact (limsup_le_limsup (Eventually.of_forall hb)).trans_eq hc.limsup_eq
  · exact isBoundedUnder_of ⟨⊤,fun _=>le_top⟩
  · exact isBoundedUnder_of ⟨⊥,fun _=>bot_le⟩

/-- The actual complete affine U-node fibres have exactly the printed optimal-energy limit.
Use: u_polynomial_energy_limit converts the same finite nonnegative objective to the literal ordinary real infimum on the printed source polynomial.
Article: jacobi, Proposition 6.1.
Proof: the proved positive affine equivalence acts on every original
competitor and scales its exact normalized energy by theta^(-2).
The same positive finite scalar therefore scales the actual full
infimum limit, with no restriction to the persymmetric family. -/
theorem u_fibre_energy_limit {theta:ℝ} (ht:0 < theta) (htop:theta≤1) :
    Tendsto (fun n:ℕ=>fibreEnergyInfimum (uNodes theta ht htop (n+1)))
      atTop (𝓝 (ENNReal.ofReal (2/(15*theta^2)))) := by
  -- This is an exact finite change of variables before taking any limit.
  have h:=ENNReal.Tendsto.const_mul (a:=ENNReal.ofReal (theta⁻¹^2))
    u_base_energy_limit (Or.inr ENNReal.ofReal_ne_top)
  have hc:ENNReal.ofReal (theta⁻¹^2)*ENNReal.ofReal (2/15)=
      ENNReal.ofReal (2/(15*theta^2)) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    field_simp
  rw [hc] at h
  apply (tendsto_congr ?_).mpr h
  intro n
  exact fibreEnergyInfimum_endpointAffine
    (jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) (n+1))
    (uNodes theta ht htop (n+1)) ht (fun _=>rfl)

/-- The literal original U polynomial family has the printed ordinary real full-fibre optimal-energy limit.
Use: paired with the original Laguerre minimum limit and the two full l1 edge limits, this is the first energy limit in the complete source counterexample.
Article: jacobi, Proposition 6.1.
Proof: the genuine extended finite infimum converges to the same
finite positive value. Its ordinary-value map is continuous there.
The proved exact finite toReal-infimum identity and complete original
polynomial identification give exactly the source competitor set. -/
theorem u_polynomial_energy_limit {theta:ℝ} (ht:0 < theta) (htop:theta≤1) :
    Tendsto (fun n:ℕ=>sInf ((fun J:chebyshev2.Jacobi (n+1)=>
      J.energy/((n:ℝ)+1)^3) '' {J | InFiber J (uPolynomial theta (n+1))}))
      atTop (𝓝 (2/(15*theta^2))) := by
  -- Finiteness at the genuine limiting value justifies passing to the ordinary real objective.
  have h:=(ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp (u_fibre_energy_limit ht htop)
  rw [ENNReal.toReal_ofReal (by positivity : 0≤2/(15*theta^2))] at h
  dsimp only [Function.comp_def] at h
  simp only [fibreEnergyInfimum_toReal,uNodes_polynomial,Nat.cast_add,Nat.cast_one] at h
  exact h

end
end jacobi.Counterexample
