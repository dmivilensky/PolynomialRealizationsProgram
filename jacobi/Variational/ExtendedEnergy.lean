import jacobi.Variational.Problem

/-!
Article: jacobi, Appendix D.5 (unrestricted inner problem).
The finite-energy domain used in the direct method gives exactly the same
extended infimum as all nonnegative L1 sources, including sources of infinite
energy. A finite extended energy constructs the original Density; an infinite
one cannot lower any infimum. Thus the calibrated lower bounds carry no
additional finite-energy premise on their competitors.
Source: nonnegative Lebesgue integration and the definition of the variational infimum.
Use: extends the calibrated inequalities to every competitor in the source's mass-constrained problems.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The literal extended objective of any nonnegative L1 source, allowing infinite energy.
Use: extends the calibrated inequalities to every competitor in the source's mass-constrained problems.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
def L1Source.energyCost (m : L1Source) : ℝ≥0∞ := ∫⁻ x,ENNReal.ofReal (m.value x^(3/2:ℝ))

/-- The extended nonnegative objective agrees with the actual finite-energy objective on Density.
Use: transfers infima and actual attainers between the two exactly equivalent variational domains.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: the nonnegative integrable energy has lintegral equal to ofReal of its real integral. -/
theorem Density.energyCost_eq_cost (m : Density) : m.toL1Source.energyCost=m.cost := by
  rw [L1Source.energyCost,← ofReal_integral_eq_lintegral_ofReal m.energy_integrable
    (Eventually.of_forall fun x => rpow_nonneg (m.nonneg x) _)]
  rfl

/-- A source of finite extended energy is an actual member of the original finite-energy domain.
Use: discharges finite-energy membership whenever an unrestricted competitor could improve an infimum.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
def L1Source.finiteEnergyDensity (m : L1Source) (h : m.energyCost≠∞) : Density where
  toL1Source := m
  energy_integrable := (lintegral_ofReal_ne_top_iff_integrable
    ((m.measurable.pow_const (3/2:ℝ)).aestronglyMeasurable)
    (Eventually.of_forall fun x => rpow_nonneg (m.nonneg x) _)).mp h

/-- Every unrestricted nonnegative L1 competitor obeys the original relaxed lower bound.
Use: calibrations apply with no unproved finite-energy hypothesis on the density being bounded.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: infinite energy is automatic. At finite energy the literal source
constructs an actual Density with identical mass, spectrum and objective;
its membership gives the infimum inequality. -/
theorem relaxed_le_extended_energy (S : Set Observation) (M : ℝ) (T : Observation → ℝ)
    (m : L1Source) (hm : m.mass≤M) (hT : ∀ i∈S,T i≤observe m i) :
    relaxedInfimum S M T≤m.energyCost := by
  -- The only split distinguishes a true infinite objective from a genuine finite-energy competitor.
  by_cases h : m.energyCost=∞
  · rw [h]
    exact le_top
  · let q := m.finiteEnergyDensity h
    have hq : relaxedInfimum S M T≤q.cost := sInf_le ⟨q,⟨hm,hT⟩,rfl⟩
    exact hq.trans_eq q.energyCost_eq_cost.symm

/-- The unrestricted actual mass-constrained spectral infimum, including infinite-energy sources.
Use: expresses the source variational domain independently of the direct method's finite-energy type.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
def extendedMomentInfimum (S : Set Observation) (M : ℝ) (T : Observation → ℝ) : ℝ≥0∞ :=
  sInf (L1Source.energyCost '' {m | m.mass≤M ∧ ∀ i∈S,T i≤observe m i})

/-- The source's unrestricted moment infimum is exactly the original finite-energy infimum, even for empty domains.
Use: all proved Young, elliptic and Keller calibration values are literal infima on the full stated domain.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: the unrestricted lower bound gives one direction. Every finite-energy
Density is an unrestricted source with exactly the same actual cost,
which gives the reverse direction. No existence or finiteness premise is needed. -/
theorem extendedMomentInfimum_eq (S : Set Observation) (M : ℝ) (T : Observation → ℝ) :
    extendedMomentInfimum S M T=relaxedInfimum S M T := by
  -- Both order comparisons use the actual admissible sets, including the empty-set case.
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨m,⟨hm,hT⟩,rfl⟩
    exact (sInf_le ⟨m.toL1Source,⟨hm,hT⟩,rfl⟩ :
      extendedMomentInfimum S M T≤m.toL1Source.energyCost).trans_eq m.energyCost_eq_cost
  · apply le_sInf
    rintro _ ⟨m,⟨hm,hT⟩,rfl⟩
    exact relaxed_le_extended_energy S M T m hm hT

end
end jacobi.Variational
