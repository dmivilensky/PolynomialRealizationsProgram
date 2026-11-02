import jacobi.Comparison.MainBounds

/-!
Article: jacobi, Theorem 4.1.
The extended nonnegative finite-fibre formulation is exactly the
article's ordinary real lower limiting infimum. Finiteness and the
boundedness needed to commute toReal with the lower limit follow from
the actual proved persymmetric candidate limit, not from assumptions.
Use: realOptimalEnergy and its actual real infimum identity use the ordinary finite value, without totalizing an infinite extended cost.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan jacobi.Variational
open scoped Topology ENNReal

/-- The original full Jacobi-fibre limiting optimal energy is finite.
Use: realOptimalEnergy and its actual real infimum identity use the
ordinary finite value, without totalizing an infinite extended cost.
Article: jacobi, Theorem 4.1.
Proof: the proved actual upper constant is a finite real integral. -/
theorem jacobiOptimalEnergy_ne_top {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    jacobiOptimalEnergy a b ha hb≠∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (jacobiOptimalEnergy_upper ha hb)

/-- The article's ordinary real limiting optimal energy, recovered
from the same proved finite extended nonnegative fibre infimum.
Use: realOptimalEnergy_definition identifies its exact ordinary real
liminf/inf meaning; the real two-sided bounds are Theorems A--B.
Article: jacobi, Theorem 4.1.
-/
def realOptimalEnergy (a b:ℝ) (ha:-1<a) (hb:-1<b) : ℝ :=
  (jacobiOptimalEnergy a b ha hb).toReal

/-- The real optimal energy has exactly the article's original real
lower limiting infimum over the entire genuine finite Jacobi fibres.
Use: the real bounds and the later parameter derivative concern the
same original real function e, with no modified competitor domain.
Article: jacobi, Theorem 4.2.
Proof: the actual candidate limit bounds all sufficiently large finite
fibre infima by one finite real constant. The community bounded liminf
identity commutes toReal with their lower limit; the already proved
exact finite toReal-infimum identity gives the printed ordinary infima. -/
theorem realOptimalEnergy_definition {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    realOptimalEnergy a b ha hb=liminf (fun n:ℕ =>
      sInf ((fun J:chebyshev2.Jacobi (n+1) => J.energy/((n:ℝ)+1)^3) ''
        {J | jacobi.Finite.InFiber J (jacobi.Jacobi.nodes a b ha hb (n+1)).polynomial})) atTop := by
  -- The actual finite candidate supplies the bound needed by the real lower-limit theorem.
  have he := (target_energy_limit ha hb).eventually
    (Iio_mem_nhds (lt_add_one (persymmetricConstant a ha)))
  have hbnd : ∀ᶠn:ℕ in atTop,fibreEnergyInfimum (jacobi.Jacobi.nodes a b ha hb (n+1))≤
      ENNReal.ofReal (persymmetricConstant a ha+1) := by
    filter_upwards [he] with n hn
    have hi : fibreEnergyInfimum (jacobi.Jacobi.nodes a b ha hb (n+1))≤
        ENNReal.ofReal ((targetChain a b ha hb n).energy/((n:ℝ)+1)^3) := by
      apply sInf_le
      refine ⟨targetChain a b ha hb n,targetChain_inFiber a b ha hb n,?_⟩
      simp only [fibreCost,Nat.cast_add,Nat.cast_one]
    exact hi.trans (ENNReal.ofReal_le_ofReal hn.le)
  have hh := ENNReal.liminf_toReal_eq ENNReal.ofReal_ne_top hbnd
  simp only [fibreEnergyInfimum_toReal,Nat.cast_add,Nat.cast_one] at hh
  exact hh.symm

/-- The full original lower constant is finite for every genuine
Bessel order; neither parameter supremum hides an infinite value.
Use: realOptimalEnergy_bounds gives the literal real Theorem 4.1.
Article: jacobi, Theorem 4.1.
Proof: specialize the proved complete bounds at beta=alpha and use
the already proved actual finite optimal-energy upper bound. -/
theorem besselLowerConstant_ne_top {a:ℝ} (ha:-1<a) :
    lowerConstant (jacobi.Bessel.edgeSpectrum a ha)≠∞ :=
  ne_top_of_le_ne_top (jacobiOptimalEnergy_ne_top ha ha) (jacobiOptimalEnergy_bounds ha ha).1

/-- The ordinary real optimal energy satisfies precisely the full
printed two-sided bounds, with the actual alpha-only real constants.
Use: this is Theorem 4.1 in the literal real-number formulation and
provides Theorem 4.2's original real beta-independent squeeze.
Article: jacobi, Theorem 4.1.
Proof: every original quantity is proved finite. Monotonicity of the
ordinary-value map transfers the established actual extended bounds;
nonnegativity of the original squared-profile integral recovers c_star. -/
theorem realOptimalEnergy_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    (lowerConstant (jacobi.Bessel.edgeSpectrum a ha)).toReal≤realOptimalEnergy a b ha hb ∧
      realOptimalEnergy a b ha hb≤persymmetricConstant a ha := by
  have hh := jacobiOptimalEnergy_bounds ha hb
  refine ⟨ENNReal.toReal_mono (jacobiOptimalEnergy_ne_top ha hb) hh.1,?_⟩
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh.2
  simpa only [realOptimalEnergy,ENNReal.toReal_ofReal (persymmetricConstant_nonneg a ha)] using hu

/-- The actual ordinary real full-fibre optimal energy equals 2/15
at U for every admissible beta, with no extended-value convention.
Use: the exact real equality point in Theorems B--C.
Article: jacobi, Theorem 4.1.
Proof: the actual proved extended optimum equals the same positive
finite real value, so its ordinary real value is unchanged. -/
theorem realOptimalEnergy_U {b:ℝ} (hb:-1<b) (ha:-1<(1/2:ℝ)) :
    realOptimalEnergy (1/2) b ha hb=2/15 := by
  rw [realOptimalEnergy,(jacobiOptimalEnergy_U hb ha).2,ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤2/15)]

end
end jacobi.Comparison
