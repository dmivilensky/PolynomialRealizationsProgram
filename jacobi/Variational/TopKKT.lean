import jacobi.Variational.MultiplierRule
import jacobi.Variational.TopActivity

/-!
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Every actual nonzero radial top-constrained minimizer has its active
threshold, positive normal multipliers and the printed positive-part Euler
equation. The gradient is the actual normalized ground-state square and
its quadratic expansion uses the density's actual positive spectral gap.
Source: the fully proved normal multiplier rule and actual top spectral variation.
Use: starts the mass-constrained Keller calibration from an actual attained minimizer.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter chebyshev2.Continuum chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false

/-- Every actual radial top-constrained minimizer satisfies the complete normal pointwise KKT equation.
Use: starts the mass-constrained Keller calibration from an actual attained minimizer.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: use the actual simple-gap first variation and strict top dilation.
The common normal multiplier proof discharges constraint qualification,
separation and complementarity; amplitude descent proves the constraint active. -/
theorem top_minimizer_kkt {M T : ℝ} (hT : 0<T) (m : Density) (hm : 0<m.mass)
    (hrad : SymmetricDecreasing m.value) (hmM : m.mass≤M) (hmT : T≤observe m .top)
    (hmin : m.cost=relaxedInfimum {Observation.top} M (fun _ => T)) :
    observe m .top=T ∧ ∃ e : H1,‖e‖=1 ∧ densityOperator m.value e=m.spectrum 0 • e ∧
      ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
        (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (μ*topGradient e x-l) 0 := by
  -- All constants and the gradient belong to this actual density, with no isolated-eigenvalue premise.
  have hminE (q : Density) (hqM : q.mass≤M) (hqT : T≤observe q .top) : m.energy≤q.energy := by
    have hcost : m.cost≤q.cost := by
      rw [hmin]
      apply sInf_le
      refine ⟨q,⟨hqM,?_⟩,rfl⟩
      intro i hi
      have hh : i=Observation.top := mem_singleton_iff.mp hi
      subst i
      exact hqT
    exact (ENNReal.ofReal_le_ofReal_iff q.energy_nonneg).mp hcost
  obtain ⟨e,he,hTe,hgap,hγc,hγbound,hvariation⟩ := top_variation m hm
  obtain ⟨k,hk,hgain⟩ := top_strict_dilation m hm
  have hγB (x : ℝ) : |topGradient e x|≤1 := by
    rw [abs_of_nonneg (hγbound x).1]
    exact (hγbound x).2
  have hvar (q : Density) (hsmall : (∫ x,|q.value x-m.value x|)≤(m.spectrum 0-m.spectrum 1)/4) :
      |observe q .top-observe m .top-(∫ x,topGradient e x*(q.value x-m.value x))|≤
        (2/(m.spectrum 0-m.spectrum 1))*(∫ x,|q.value x-m.value x|)^2 := by
    have h := hvariation q hsmall
    change |observe q .top-observe m .top-(∫ x,topGradient e x*(q.value x-m.value x))|≤_ at h
    convert h using 1
    ring
  obtain ⟨μ,l,hμ,hl,hcomp,heq⟩ := normal_multiplier_rule m hm hrad
    (fun q => observe q .top) (topGradient e) hγc.measurable hγB
    (by positivity : 0<2/(m.spectrum 0-m.spectrum 1))
    (by positivity : 0<(m.spectrum 0-m.spectrum 1)/4) hk hmM hmT hminE hvar hgain
  exact ⟨top_constraint_active hT m hm hmM hmT hmin,e,he,hTe,μ,l,hμ,hl,hcomp,heq⟩

/-- The actual subcritical top-constrained infimum has a radial attainer satisfying its proved Euler equation.
Use: Keller calibration may start from an actual attained solution rather than an assumed stationary profile.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: apply the fully discharged KKT theorem to the actual direct-method minimizer with active constraint. -/
theorem top_minimizer_kkt_exists {M T : ℝ} (hM : 0<M) (hT : 0<T) (hsub : T<M) :
    ∃ m : Density,SymmetricDecreasing m.value ∧ 0<m.mass ∧ m.mass≤M ∧
      observe m .top=T ∧ m.cost=relaxedInfimum {Observation.top} M (fun _ => T) ∧
      ∃ e : H1,‖e‖=1 ∧ densityOperator m.value e=m.spectrum 0 • e ∧
        ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
          (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (μ*topGradient e x-l) 0 := by
  -- One actual density supplies feasibility, attainment, activity, the top vector and both multipliers.
  obtain ⟨m,hs,hm,hmM,hmT,hmin⟩ := top_minimizer_exists hM hT hsub
  exact ⟨m,hs,hm,hmM,hmT,hmin,(top_minimizer_kkt hT m hm hs hmM hmT.ge hmin).2⟩

end
end jacobi.Variational
