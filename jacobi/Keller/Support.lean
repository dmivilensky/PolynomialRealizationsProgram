import jacobi.Keller.FreeProfile

/-!
Article: jacobi, Theorem D.6.
The strict mass branch has a strictly positive ground cutoff. The actual
ground state attains that level at a finite positive radius, and strict
radial decrease identifies the entire positive set of the Euler density.
Both branch theorems return the same actual densities that attain the
original variational infimum, with no numerical feasibility assumptions.
Source: the intermediate value theorem on the proved full ground branch.
Use: identifies the compact support of the genuine attaining density in the mass-constrained regime.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Set Filter jacobi.Variational
open chebyshev2.Sobolev
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {m : Density} {ell M : ℝ}

/-- The strict Keller branch has a finite centered positive-density core for its actual continuous representative.
Use: identifies the compact support of the genuine attaining density in the mass-constrained regime.
Article: jacobi, Theorem D.6.
Proof: the positive cutoff has square root in (0,1), so the actual full
ground branch attains it. Strict radial decrease identifies every point
inside and outside that radius, and the positive-part formula gives the support. -/
theorem Profile.compact_core (p : Profile m ell M) (hell : 0<ell) (hc : 1<p.shape) :
    ∃ a : ℝ,0<a ∧ ∀ x : ℝ,(0<p.rho x ↔ |x|<a) := by
  -- The free boundary is a level of the actual attained ground state.
  have he0 : 0<p.edge := lt_of_le_of_ne p.edge_nonneg (by
    intro hz
    exact hc.ne' (p.shape_eq_one_iff.mpr hz.symm))
  have hlev : sqrt p.edge∈Ioo (0:ℝ) 1 :=
    ⟨sqrt_pos.mpr he0,(sqrt_lt' zero_lt_one).mpr (by nlinarith [p.edge_lt_one hell])⟩
  obtain ⟨a,ha,hua⟩ := (show sqrt p.edge∈H1.rep p.u '' Ioi (0:ℝ) from by
    rw [p.state_image]; exact hlev)
  refine ⟨a,ha,fun x => ?_⟩
  have habs : H1.rep p.u |x|=H1.rep p.u x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx,p.even]
  have hpos : 0<p.rho x ↔ p.edge<H1.rep p.u x^2 := by
    unfold Profile.rho
    rw [mul_pos_iff_of_pos_left p.b_pos]
    constructor
    · intro hh
      by_contra! hn
      rw [max_eq_right (sub_nonpos.mpr hn)] at hh
      norm_num at hh
    · intro hh
      exact sq_pos_of_pos (lt_max_of_lt_left (sub_pos.mpr hh))
  rw [hpos]
  have hsq := sq_sqrt he0.le
  constructor
  · intro hh
    by_contra! hx
    have hb := p.decreasing.antitoneOn (mem_Ici.mpr (mem_Ioi.mp ha).le)
      (mem_Ici.mpr (abs_nonneg x)) hx
    rw [hua,habs] at hb
    nlinarith [p.positive x,sqrt_nonneg p.edge]
  · intro hx
    have hb := p.decreasing (mem_Ici.mpr (abs_nonneg x))
      (mem_Ici.mpr (mem_Ioi.mp ha).le) hx
    rw [hua,habs] at hb
    nlinarith [p.positive x,sqrt_nonneg p.edge]

/-- The strict mass-constrained Keller minimum has an actual compactly supported radial attainer.
Use: completes the article's attaining-profile assertion in the second regime,
with its unique shape, exact energy, active mass and active top eigenvalue.
Article: jacobi, Theorem D.6.
Proof: the complete constrained calibration gives the actual minimizing
density and its genuine profile. The proved positive ground cutoff gives
a finite core; transfer its pointwise support to the original density a.e. -/
theorem constrained_attainer (hell : 0<ell) (hsub : ell<M) (hregime : M<3*ell/2) :
    ∃ c : ℝ,1<c ∧ 3*ell*massCurve c=M ∧
      (∀ d : ℝ,1<d → 3*ell*massCurve d=M → d=c) ∧
      Kel ell M=ENNReal.ofReal (constrainedValue ell c) ∧
      ∃ m : Density,SymmetricDecreasing m.value ∧ m.mass=M ∧ observe m .top=ell ∧
        m.energy=constrainedValue ell c ∧ m.cost=Kel ell M ∧
        ∃ a : ℝ,0<a ∧ ∀ᵐ x : ℝ,(0<m.value x ↔ |x|<a) := by
  -- The support belongs to the same actual original variational attainer.
  obtain ⟨c,hc,hr,hu,hvalue,m,hs,hm,hG,hE,hcost,p,hpc⟩ := constrained_calibration hell hsub hregime
  obtain ⟨a,ha,hcore⟩ := p.compact_core hell (by rwa [hpc])
  refine ⟨c,hc,hr,hu,hvalue,m,hs,hm,hG,hE,hcost,a,ha,?_⟩
  filter_upwards [p.density] with x hx
  change m.value x=p.rho x at hx
  rw [hx]
  exact hcore x

end
end jacobi.Keller
