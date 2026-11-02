import jacobi.Analytic.RealShiftedEnergy
import jacobi.Analytic.RealShiftedSpectralLimit
import jacobi.Variational.LowerConstant

/-!
Article: jacobi, Corollary C.6.
Full Transfer applies to arbitrary real shifted competitors in the
original Jacobi fibres. A genuine near-minimizer sequence is contracted
into the ordinary admissible fibres; the exact affine energy factor
tends to one. No extra finite-matrix or continuum feasibility premise
is retained in the lower bound.
Use: shiftedOptimalEnergy_lower removes theta_N from actual original near-minimizer costs.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter jacobi.Finite jacobi.Packing jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The original shifted cost and transformed ordinary cost have precisely the source affine factor.
Use: shiftedOptimalEnergy_lower removes theta_N from actual original near-minimizer costs.
Article: jacobi, Appendix E.1.
Proof: the already proved exact original matrix energy identity
commutes with division by the same matrix dimension and the nonnegative real embedding. -/
theorem shiftedFibre_cost {N:ℕ} (S:Nodes N) {J:chebyshev2.Jacobi N}
    (hJ:InFiber J S.polynomial) {z:ℝ} (hz:0<z) (ht:∀k,S.value k<z) :
    fibreCost (shiftedFibre J z)=ENNReal.ofReal (shiftScale z^2)*realShiftedCost J z := by
  rw [fibreCost,shiftedFibre_energy S hJ hz ht,realShiftedCost,realShiftedEnergy,
    mul_div_assoc,ENNReal.ofReal_mul (sq_nonneg _)]

/-- Every original real shifted finite-fibre optimum obeys all four complete source calibrations.
Use: shiftedOptimalEnergy_bounds is the full Corollary C.6.
Article: jacobi, Corollary C.6.
Proof: select genuine original competitors approaching the actual
finite lower limiting infimum. After discarding a finite prefix their
real edge points are positive and above every original node. Their
affine images lie in contractive fibres with the proved shifted L1
limit, so full Transfer bounds their limiting costs. The exact original
theta-squared cost factor tends to one, recovering the same original optimum. -/
theorem shiftedOptimalEnergy_lower {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) :
    lowerConstant (realShiftSpectrum a ha w hw)≤shiftedOptimalEnergy a b ha hb w := by
  -- Near-minimizers come from the complete original fibres, before making any affine change.
  by_cases hL:shiftedOptimalEnergy a b ha hb w=∞
  · rw [hL]; exact le_top
  obtain ⟨α,hα,J,hJ,hcost⟩ := exists_liminf_competitors
    (X:=fun n => chebyshev2.Jacobi (n+1))
    (fun n J => realShiftedCost J (1+w/(2*((n:ℝ)+1)^2)))
    (fun n => {J | InFiber J (jacobi.Jacobi.nodes a b ha hb (n+1)).polynomial}) hL
  have hg : ∀ᶠn:ℕ in atTop,0<1+w/(2*((α n:ℝ)+1)^2) ∧
      ∀k,(jacobi.Jacobi.nodes a b ha hb (α n+1)).value k<1+w/(2*((α n:ℝ)+1)^2) :=
    hα.eventually (((real_edgePoint_limit w).eventually (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))).and
      (real_edgePoint_above_nodes ha hb hw))
  obtain ⟨M,hM⟩ := eventually_atTop.mp hg
  let β (n:ℕ) := α (n+M)
  have hβ : Tendsto β atTop atTop := hα.comp (tendsto_add_atTop_nat M)
  have hgood (n:ℕ) := hM (n+M) (Nat.le_add_left M n)
  let S (n:ℕ) := shiftedNodes (jacobi.Jacobi.nodes a b ha hb (β n+1))
    (1+w/(2*((β n:ℝ)+1)^2)) (hgood n).1 (hgood n).2
  let J' (n:ℕ) := shiftedFibre (J (n+M)) (1+w/(2*((β n:ℝ)+1)^2))
  have hJ' (n:ℕ) : InFiber (J' n) (S n).polynomial :=
    shiftedFibre_inFiber _ (hJ (n+M)) (hgood n).1 (hgood n).2
  have hspec := shiftedNodes_spectral_limit ha hb hw β hβ
    (fun n => (hgood n).1) (fun n => (hgood n).2)
  have hlow := lowerConstant_transfer (fun n => β n+1) S (fun n => Nat.succ_pos _)
    ((tendsto_add_atTop_nat 1).comp hβ) (realShiftSpectrum a ha w hw) hspec
  -- The same genuine cost limit survives the finite prefix and theta_N^2 -> 1.
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (((shiftScale_limit w).comp hβ).pow 2)
  simp only [one_pow,ENNReal.ofReal_one] at ht
  have hc := hcost.comp (tendsto_add_atTop_nat M)
  have hmul := ENNReal.Tendsto.mul ht (Or.inl one_ne_zero) hc (Or.inr ENNReal.one_ne_top)
  simp only [one_mul,Function.comp_def] at hmul
  have hc' : Tendsto (fun n => fibreCost (J' n)) atTop (𝓝 (shiftedOptimalEnergy a b ha hb w)) := by
    simpa only [shiftedOptimalEnergy,shiftedFibreInfimum] using hmul.congr
      (fun n => (shiftedFibre_cost _ (hJ (n+M)) (hgood n).1 (hgood n).2).symm)
  have hbnd (n:ℕ) : fibreEnergyInfimum (S n)≤fibreCost (J' n) := sInf_le ⟨_,hJ' n,rfl⟩
  exact hlow.trans ((liminf_le_liminf (Eventually.of_forall hbnd)).trans_eq hc'.liminf_eq)

/-- The full original shifted optimum lies between the complete source lower constant and the actual squared profile integral.
Use: this is the complete extended nonnegative formulation of the off-edge two-sided corollary.
Article: jacobi, Corollary C.6.
Proof: combine the unconditional full-fibre shifted Transfer lower bound
and the genuine original persymmetric candidate upper limit. -/
theorem shiftedOptimalEnergy_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) :
    lowerConstant (realShiftSpectrum a ha w hw)≤shiftedOptimalEnergy a b ha hb w ∧
      shiftedOptimalEnergy a b ha hb w≤ENNReal.ofReal (realShiftedUpper a ha w) :=
  ⟨shiftedOptimalEnergy_lower ha hb hw,shiftedOptimalEnergy_upper ha hb hw⟩

end
end jacobi.EdgeResolvent
