import jacobi.Variational.FredholmResolvent
import jacobi.Variational.SecondActivity
import jacobi.Variational.EnergyVariation
import jacobi.Variational.TopGap

/-!
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
The actual top eigenvalue has its exact amplitude homogeneity. Every actual
top-constrained minimizer therefore meets its threshold exactly, and the
direct-method minimizer has an active constraint before any Euler equation
is invoked.
Source: the actual simple top eigenvector and amplitude descent.
Use: amplitude homogeneity of the operator norm yields the actual spectral homogeneity.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set chebyshev2.Continuum
open scoped InnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The nonzero density operator's norm equals its actual leading eigenvalue.
Use: amplitude homogeneity of the operator norm yields the actual spectral homogeneity.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: combine the actual top norm bound with a proved unit top eigenvector. -/
theorem densityOperator_norm_eq_top (m : Density) (hm : 0<m.mass) :
    ‖densityOperator m.value‖=observe m .top := by
  -- An actual unit top vector gives the reverse inequality, not an assumed norm eigenvalue identity.
  apply le_antisymm (densityOperator_norm_top m)
  obtain ⟨e,he,hTe,_,_⟩ := density_top_gap m hm
  have h := (densityOperator m.value).le_opNorm e
  have hnon : 0≤m.spectrum 0 := (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg 0
  rw [hTe,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg hnon,he,mul_one,mul_one] at h
  exact h

/-- The original feature operator has exact amplitude linearity.
Use: proves the spectral top scaling for actual densities.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: scalar associativity inside the Bochner feature integral and integral homogeneity. -/
theorem Density.scale_operator (m : Density) (c : ℝ) (hc : 0≤c) :
    densityOperator (m.scale c hc).value=c • densityOperator m.value := by
  unfold densityOperator
  change (∫ x,(c*m.value x) • featureProjection x)=_
  simp_rw [mul_smul]
  exact integral_smul c _

/-- Positive amplitude scaling multiplies the actual leading eigenvalue by the same amplitude.
Use: scales a slack top-constrained candidate exactly to the threshold.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: both densities have positive mass, their norms equal their actual top eigenvalues,
and the underlying feature operator is exactly linear in amplitude. -/
theorem Density.scale_top (m : Density) (hm : 0<m.mass) (c : ℝ) (hc : 0<c) :
    observe (m.scale c hc.le) .top=c*observe m .top := by
  have hq : 0<(m.scale c hc.le).mass := by rw [Density.scale_mass]; positivity
  rw [← densityOperator_norm_eq_top _ hq,← densityOperator_norm_eq_top m hm,
    Density.scale_operator,norm_smul,Real.norm_eq_abs,abs_of_pos hc]

/-- Every actual nonzero top-constrained minimizer has its spectral constraint active.
Use: the top KKT and Keller calibration use the exact threshold, not an assumed equality.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: if the actual top value exceeds T, amplitude T/top is feasible and
strictly below one. Its mass stays admissible, its top becomes T exactly,
and its proved positive energy decreases strictly. -/
theorem top_constraint_active {M T : ℝ} (hT : 0<T) (m : Density) (hm : 0<m.mass)
    (hmM : m.mass≤M) (hmT : T≤observe m .top)
    (hmin : m.cost=relaxedInfimum {Observation.top} M (fun _ => T)) :
    observe m .top=T := by
  -- The amplitude competitor lies in the exact original top-constrained admissible set.
  apply le_antisymm _ hmT
  by_contra! hslack
  have htop : 0<observe m .top := hT.trans_le hmT
  let c := T/observe m .top
  have hc : 0<c := div_pos hT htop
  have hc1 : c<1 := (div_lt_one htop).mpr hslack
  let q := m.scale c hc.le
  have hqM : q.mass≤M := by
    rw [Density.scale_mass]
    exact (mul_le_of_le_one_left hm.le hc1.le).trans hmM
  have hqT : observe q .top=T := by
    rw [Density.scale_top m hm c hc]
    exact div_mul_cancel₀ _ htop.ne'
  have hqE : q.energy<m.energy := by
    rw [Density.scale_energy]
    exact mul_lt_of_lt_one_left (m.energy_pos hm)
      (Real.rpow_lt_one hc.le hc1 (by norm_num : (0:ℝ)<3/2))
  have hle : m.cost≤q.cost := by
    rw [hmin]
    apply sInf_le
    refine ⟨q,⟨hqM,?_⟩,rfl⟩
    intro i hi
    have hh : i=Observation.top := mem_singleton_iff.mp hi
    subst i
    exact hqT.ge
  have hqcost : q.cost<m.cost := (ENNReal.ofReal_lt_ofReal_iff (m.energy_pos hm)).mpr hqE
  exact (not_lt_of_ge hle) hqcost

/-- The actual strictly subcritical top-constrained infimum has a nonzero radial attainer with active constraint.
Use: the top KKT and Keller quadratures start from an actual minimizer, not an assumed optimizer certificate.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the full direct-method theorem provides an actual radial minimizer;
the proved amplitude descent establishes its top constraint exactly. -/
theorem top_minimizer_exists {M T : ℝ} (hM : 0<M) (hT : 0<T) (hsub : T<M) :
    ∃ m : Density,SymmetricDecreasing m.value ∧ 0<m.mass ∧ m.mass≤M ∧
      observe m .top=T ∧ m.cost=relaxedInfimum {Observation.top} M (fun _ => T) := by
  -- The active constraint is proved for the same density returned by the direct method.
  obtain ⟨m,hs,hm,hmM,hmT,hmin⟩ := moment_minimizer_exists hM {Observation.top}
    (by simp) (fun _ => T) (fun _ _ => hT)
    (by intro i hi; simp only [mem_singleton_iff] at hi; subst i; exact hsub)
  exact ⟨m,hs,hm,hmM,top_constraint_active hT m hm hmM (hmT .top (by simp)) hmin,hmin⟩

end
end jacobi.Variational
