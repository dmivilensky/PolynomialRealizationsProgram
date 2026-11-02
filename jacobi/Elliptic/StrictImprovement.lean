import jacobi.Young.Equality
import jacobi.Young.Constants
import jacobi.Variational.MomentExistence
import jacobi.Elliptic.RatioEndpoints

/-!
Article: jacobi, Section 3.2 (sharp comparison at U).
The actual attained second-moment infimum is strictly larger than the sharp
Young lower bound throughout 2M²<5T<5M². The proof uses the unconditional
general existence theorem and the complete necessity classification of all
Young equality densities. It does not assume an elliptic optimizer or its
yet separate quadrature formula.
Use: the strict elliptic comparison starts from an unconditional lower bound.
-/
namespace jacobi.Elliptic
noncomputable section
open Real Set MeasureTheory jacobi.Variational jacobi.Young
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The general sharp Young lower bound for the actual second-moment infimum.
Use: the strict elliptic comparison starts from an unconditional lower bound.
Article: jacobi, Theorem D.5.
Proof: every element of the actual admissible cost set satisfies the proved energy bound. -/
theorem second_infimum_young_lower {M T : ℝ} (hT : 0≤T) :
    ENNReal.ofReal (youngValue T)≤relaxedInfimum {Observation.second} M (fun _ => T) := by
  apply le_sInf
  rintro a ⟨m,hm,rfl⟩
  exact ENNReal.ofReal_le_ofReal (second_energy_lower m hT (hm.2 .second (by simp)))

/-- A density attaining the Young lower bound above threshold must be a genuine Young equality case.
Use: links equality of variational values to the classified family, without assuming the spectral constraint is active.
Article: jacobi, Theorem D.5.
Proof: sharp Young and the exact fourth power of the proposed energy squeeze
the second moment to its threshold; both polynomial bounds then become equalities. -/
theorem energy_at_young_value {T : ℝ} (hT : 0<T) (m : Density)
    (hm : T≤observe m .second) (he : m.energy=youngValue T) :
    observe m .second=T ∧ 18*(observe m .second)^3=5*m.energy^4 := by
  -- Positivity permits taking cubes in order, so there is no extra active-constraint premise.
  have hg : 0≤observe m .second := tsum_nonneg (fun _ => sq_nonneg _)
  have hy := youngValue_four hT.le
  have hs := sharp_young_cubed m
  rw [he,hy] at hs
  have hle : observe m .second≤T :=
    (pow_le_pow_iff_left₀ hg hT.le (by decide : 3≠0)).mp (by nlinarith [hs])
  have hgt := le_antisymm hle hm
  refine ⟨hgt,?_⟩
  rw [hgt,he,hy]
  ring

/-- Strict elliptic improvement for the actual attained variational infimum.
Use: closes the strict inequality in the article's elliptic calibration, independently of its quadrature identification.
Article: jacobi, Theorem D.5.
Proof: existence gives a nonzero actual minimizer. Equality with Young would
force its second moment to the threshold and make it a classified Young
profile. Such a profile has G_2=(2/5)mass², violating its upper mass bound. -/
theorem second_infimum_strict_young {M T : ℝ} (hM : 0<M) (hT : 0<T)
    (hsub : T<M^2) (helliptic : 2*M^2<5*T) :
    ENNReal.ofReal (youngValue T)<relaxedInfimum {Observation.second} M (fun _ => T) := by
  -- The general direct method supplies a minimizer, rather than a hypothetical extremizing profile.
  apply lt_of_le_of_ne (second_infimum_young_lower hT.le)
  intro heq
  obtain ⟨m,_,hm0,hmM,hmT,hmI⟩ := moment_minimizer_exists hM {Observation.second}
    (by simp) (fun _ => T) (fun _ _ => hT) (by intro i hi; simp only [mem_singleton_iff] at hi; subst i; exact hsub)
  have he : m.energy=youngValue T := by
    have hcost : m.cost=ENNReal.ofReal (youngValue T) := hmI.trans heq.symm
    have h := congrArg ENNReal.toReal hcost
    rwa [m.cost_toReal,ENNReal.toReal_ofReal (youngValue_nonneg hT.le)] at h
  obtain ⟨hG,heY⟩ := energy_at_young_value hT m (hmT .second (by simp)) he
  have hr := young_equality_mass_ratio m hm0 heY
  have hmass : m.mass^2≤M^2 := (sq_le_sq₀ hm0.le hM.le).mpr hmM
  nlinarith [hr,hG]

/-- Strict elliptic improvement with exactly the printed sqrt-three Young lower bound.
Use: records the source-facing strict inequality in its literal normalization.
Article: jacobi, Theorem D.5.
Proof: substitute the proved exact printed-value identity into the unconditional strict infimum theorem. -/
theorem second_infimum_strict_young_printed {M T : ℝ} (hM : 0<M) (hT : 0<T)
    (hsub : T<M^2) (helliptic : 2*M^2<5*T) :
    ENNReal.ofReal ((2*sqrt 3/5)*(5*T/2)^(3/4 : ℝ))<
      relaxedInfimum {Observation.second} M (fun _ => T) := by
  rw [← youngValue_printed hT.le]
  exact second_infimum_strict_young hM hT hsub helliptic

end
end jacobi.Elliptic
