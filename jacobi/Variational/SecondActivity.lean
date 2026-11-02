import jacobi.Variational.Amplitude
import jacobi.Young.Sharp
import jacobi.Variational.MomentExistence

/-!
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Every actual minimizer has its second-moment constraint active. The proof
uses a literal admissible amplitude rescaling, with exact mass, moment and
energy identities. No multiplier, Euler equation or constraint regularity
is assumed; this activity fact is available before the remaining KKT proof.
Use: the second-moment KKT and elliptic quadratures use the exact value G_2=T rather than an assumed active constraint.
-/
namespace jacobi.Variational
noncomputable section
open Real MeasureTheory Set
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Every actual second-moment minimizer meets its spectral threshold exactly.
Use: the second-moment KKT and elliptic quadratures use the exact value G_2=T rather than an assumed active constraint.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: if G>T, scale the actual density by sqrt(T/G)<1. Its mass remains
admissible, its actual second moment becomes exactly T and its positive
energy decreases strictly, contradicting attainment of the actual infimum. -/
theorem second_constraint_active {M T : ℝ} (hT : 0<T) (m : Density)
    (hM : m.mass≤M) (hG : T≤observe m .second)
    (hmin : m.cost=relaxedInfimum {Observation.second} M (fun _ => T)) :
    observe m .second=T := by
  -- The competing density is constructed explicitly in the original admissible set.
  apply le_antisymm _ hG
  by_contra! hslack
  let G := observe m .second
  have hGp : 0<G := hT.trans_le hG
  let c := sqrt (T/G)
  have hc : 0<c := sqrt_pos.mpr (div_pos hT hGp)
  have hc1 : c<1 := (Real.sqrt_lt' zero_lt_one).mpr (by
    simpa only [one_pow] using (div_lt_one hGp).mpr hslack)
  have hc2 : c^2=T/G := Real.sq_sqrt (div_nonneg hT.le hGp.le)
  let q := m.scale c hc.le
  have hqM : q.mass≤M := by
    change (m.scale c hc.le).mass≤M
    rw [Density.scale_mass]
    exact (mul_le_of_le_one_left (integral_nonneg m.nonneg) hc1.le).trans hM
  have hqG : observe q .second=T := by
    rw [Density.scale_second,hc2]
    exact div_mul_cancel₀ _ hGp.ne'
  have hEp : 0<m.energy := by
    have hs := jacobi.Young.sharp_young_cubed m
    have he0 := m.energy_nonneg
    by_contra! h
    have hz : m.energy=0 := le_antisymm h he0
    rw [hz] at hs
    norm_num at hs
    exact (not_le_of_gt (pow_pos hGp 3)) (by nlinarith [hs])
  have hqE : q.energy<m.energy := by
    rw [Density.scale_energy]
    have hr : c^(3/2 : ℝ)<1 := Real.rpow_lt_one hc.le hc1 (by norm_num)
    exact mul_lt_of_lt_one_left hEp hr
  have hqcost : q.cost<m.cost := by
    exact (ENNReal.ofReal_lt_ofReal_iff hEp).mpr hqE
  have hle : m.cost≤q.cost := by
    rw [hmin]
    apply sInf_le
    refine ⟨q,⟨hqM,?_⟩,rfl⟩
    intro i hi
    have hh : i=Observation.second := mem_singleton_iff.mp hi
    subst i
    exact hqG.ge
  exact (not_lt_of_ge hle) hqcost

/-- The actual subcritical second-moment problem has a radial nonzero minimizer with its spectral constraint active.
Use: elliptic normalization starts with an attained minimizer and G_2=T, with neither property supplied as a premise.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the general direct method constructs the actual radial minimizer;
the explicit amplitude-descent theorem then proves its spectral constraint active. -/
theorem second_minimizer_exists {M T : ℝ} (hM : 0<M) (hT : 0<T) (hsub : T<M^2) :
    ∃ m : Density, SymmetricDecreasing m.value ∧ 0<m.mass ∧ m.mass≤M ∧
      observe m .second=T ∧ m.cost=relaxedInfimum {Observation.second} M (fun _ => T) := by
  -- Existence and activity concern the same actual density and the same original infimum.
  obtain ⟨m,hs,hm0,hmM,hmT,hmin⟩ := moment_minimizer_exists hM {Observation.second}
    (by simp) (fun _ => T) (fun _ _ => hT)
    (by intro i hi; simp only [mem_singleton_iff] at hi; subst i; exact hsub)
  exact ⟨m,hs,hm0,hmM,second_constraint_active hT m hmM (hmT .second (by simp)) hmin,hmin⟩

end
end jacobi.Variational
